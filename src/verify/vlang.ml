open Lang
open Z3
open Z3.Solver
open Options
open Vocab

(*******************************)
(*******************************)
(**** Verification Language ****)
(*******************************)
(*******************************)

type vformula =
  | VTrue | VFalse
  | VNot of vformula
  | VAnd of vformula * vformula
  | VOr of vformula * vformula
  | VBinRel of vbrel * vexp * vexp
  | Imply of vformula * vformula
  | SigmaEqual of vexp * var (* left: uint, right: mapping (address => uint) *)
  | NoOverFlow of var
  | ForAll of var list * vformula
  | Label of int * vformula (* 0: assignment, 1: assume *)

and vexp =
  | VInt of BatBig_int.t
  | VVar of var
  | Read of vexp * vexp * typ (* A[i] *)
  | Write of vexp * vexp * vexp (* A[i] := v, return A *)
  | VBinOp of vbop * vexp * vexp * typ
  | VUnOp of vuop * vexp * typ
  | VCast of typ * vexp
  | VCond of vformula
  | Ite of vexp * vexp * vexp

and vid = string 
and vbrel = VGeq | VGt | VEq
and vbop = VAdd | VSub | VMul | VDiv | VMod | VPower
           | VShiftL | VShiftR | VBXor | VBAnd | VBOr
and vuop = VNeg | VBNot 

let rec compare_vf vf1 vf2 =
  match vf1,vf2 with
  | VTrue, VTrue -> 0
  | VNot f1,VNot f2 -> compare_vf f1 f2
  | VAnd (f1,f1'), VAnd (f2,f2') ->
    let c = compare_vf f1 f2 in
    if c = 0 then compare_vf f1' f2' else c
  | VOr (f1,f1'), VOr (f2,f2') ->
    let c = compare_vf f1 f2 in
    if c = 0 then compare_vf f1' f2' else c
  | VBinRel (r1,e1,e1'), VBinRel (r2,e2,e2') ->
    let c1 = Stdlib.compare (tag_of_brel r1) (tag_of_brel r2) in
    if c1 = 0 then
      let c2 = compare_ve e1 e2 in
      if c2 = 0 then compare_ve e1' e2'
      else c2
    else c1
  | Imply (f1,f1'), Imply (f2,f2') ->
    let c = compare_vf f1 f2 in
    if c = 0 then compare_vf f1' f2' else c
  | SigmaEqual (e1,x1), SigmaEqual (e2,x2) ->
    let c = compare_ve e1 e2 in
    if c = 0 then Stdlib.compare x1 x2 else c
  | NoOverFlow x1, NoOverFlow x2 -> Stdlib.compare x1 x2
  | ForAll (_,f1), ForAll (_,f2) -> compare_vf f1 f2 
  | _ -> Stdlib.compare (tag_of_vf vf1) (tag_of_vf vf2)

and compare_ve ve1 ve2 =
  match ve1,ve2 with
  | VInt n1,VInt n2 -> BatBig_int.compare n1 n2 
  | VVar (x1,t1),VVar (x2,t2) ->
    let c = BatString.compare x1 x2 in
    if c = 0 then Stdlib.compare t1 t2 else c
  | Read (e1,e1',t1), Read (e2,e2',t2) ->
    let c1 = compare_ve e1 e2 in
    if c1 = 0 then
      let c2 = compare_ve e1' e2' in
      if c2 = 0 then Stdlib.compare t1 t2 else c2
    else c1
  | Write (e1,e1',e1''), Write (e2,e2',e2'') ->
    let c1 = compare_ve e1 e2 in
    if c1 = 0 then
      let c2 = compare_ve e1' e2' in
      if c2 = 0 then compare_ve e1'' e2'' else c2
    else c1
  | VBinOp (bop1,e1,e1',t1), VBinOp (bop2,e2,e2',t2) ->
    let c1 = Stdlib.compare (tag_of_bop bop1) (tag_of_bop bop2) in
    if c1 = 0 then
      let c2 = compare_ve e1 e2 in
      if c2 = 0 then
        let c3 = compare_ve e1' e2' in
        if c3 = 0 then Stdlib.compare t1 t2 else c3
      else c2
    else c1
  | VUnOp (uop1,e1,t1), VUnOp (uop2,e2,t2) ->
    let c1 = Stdlib.compare (tag_of_uop uop1) (tag_of_uop uop2) in
    if c1 = 0 then
      let c2 = compare_ve e1 e2 in
      if c2 = 0 then Stdlib.compare t1 t2 else c2
    else c1
  | VCast (t1,e1), VCast (t2,e2) ->
    let c = Stdlib.compare t1 t2 in
    if c = 0 then compare_ve e1 e2 else c
  | VCond f1, VCond f2 -> compare_vf f1 f2
  | Ite (e1,e2,e3), Ite (e1',e2',e3') ->
    if compare_ve e1 e1' = 0 then
      if compare_ve e2 e2' = 0 then
        compare_ve e3 e3'
      else compare_ve e2 e2'
    else compare_ve e1 e1' 
  | _ -> Stdlib.compare (tag_of_ve ve1) (tag_of_ve ve2)

and tag_of_vf = function 
  | VTrue -> 0 | VFalse -> 1 | VNot _ -> 2 | VAnd _ -> 3 | VOr _ -> 4 | VBinRel _ -> 5
  | Imply _ -> 6 | SigmaEqual _ -> 7 | NoOverFlow _ -> 8 | ForAll _ -> 9 | Label _ -> 10

and tag_of_brel = function
  | VGeq -> 0 | VGt -> 1 | VEq -> 2

and tag_of_ve = function
  | VInt _ -> 0 | VVar _ -> 1 | Read _ -> 2 | Write _ -> 3 | VBinOp _ -> 4
  | VUnOp _ -> 5 | VCast _ -> 6 | VCond _ -> 7 | Ite _ -> 8 

and tag_of_bop = function
  | VAdd -> 0 | VSub -> 1 | VMul -> 2 | VDiv -> 3 | VMod -> 4 | VPower -> 5
  | VShiftL -> 6 | VShiftR -> 7 | VBXor -> 8 | VBAnd -> 9 | VBOr -> 10

and tag_of_uop = function
  | VNeg -> 0 | VBNot -> 1

let compare vf1 vf2 = compare_vf vf1 vf2
let equal_vf vf1 vf2 = if compare vf1 vf2 = 0 then true else false
let equal_ve ve1 ve2 = if compare_ve ve1 ve2 = 0 then true else false

module FormulaSet = BatSet.Make (struct type t = vformula let compare = compare end)
module ExpSet = BatSet.Make (struct type t = vexp let compare = compare_ve end)

let rec to_string_vformula vf =
  match vf with
  | VTrue -> "true"
  | VFalse -> "false"
  | VNot f -> "!" ^ "(" ^ to_string_vformula f ^ ")"
  | VAnd (f1,f2) -> "(" ^ to_string_vformula f1 ^ " /\\ " ^ to_string_vformula f2 ^ ")"
  | VOr (f1,f2) -> "(" ^ to_string_vformula f1 ^ " \\/ " ^ to_string_vformula f2 ^ ")"
  | VBinRel (vbrel,ve1,ve2) ->
    (match vbrel with
     | VGeq -> "(" ^ to_string_vexp ve1 ^ " >= " ^ to_string_vexp ve2 ^ ")" 
     | VGt -> "(" ^ to_string_vexp ve1 ^ " > " ^ to_string_vexp ve2 ^ ")" 
     | VEq -> "(" ^ to_string_vexp ve1 ^ " == " ^ to_string_vexp ve2 ^ ")")
  | Imply (f1,f2) -> "(" ^ to_string_vformula f1 ^ " -> " ^ to_string_vformula f2 ^ ")"
  | SigmaEqual (e,(m,t)) -> "(" ^ to_string_vexp e ^ " == " ^ "Σ" ^ m ^ ")" 
  | NoOverFlow (x,t) -> "NoOverFlow (" ^ "Σ" ^ x ^ ")"
  | ForAll (vars,f) -> "(" ^ "forAll " ^ string_of_list Vocab.id (List.map fst vars) ^ "." ^ to_string_vformula f ^ ")"
  | Label (_,f) -> to_string_vformula f

and to_string_vexp ve =
  match ve with
  | VInt n -> BatBig_int.to_string n
  | VVar (x,_) -> x
  | Read (ve1,ve2,_) -> "Read" ^ "(" ^ to_string_vexp ve1 ^ ", " ^ to_string_vexp ve2 ^ ")"
  | Write (ve1,ve2,ve3) -> "Write" ^ "(" ^ to_string_vexp ve1 ^ ", " ^ to_string_vexp ve2 ^ ", " ^ to_string_vexp ve3 ^ ")" 
  | VBinOp (vbop,ve1,ve2,_) ->
    (match vbop with
     | VAdd -> "(" ^ to_string_vexp ve1 ^ " + " ^ to_string_vexp ve2 ^ ")" 
     | VSub -> "(" ^ to_string_vexp ve1 ^ " - " ^ to_string_vexp ve2 ^ ")" 
     | VMul -> "(" ^ to_string_vexp ve1 ^ " * " ^ to_string_vexp ve2 ^ ")"
     | VDiv -> "(" ^ to_string_vexp ve1 ^ " / " ^ to_string_vexp ve2 ^ ")"
     | VMod -> "(" ^ to_string_vexp ve1 ^ " % " ^ to_string_vexp ve2 ^ ")"
     | VPower -> "(" ^ to_string_vexp ve1 ^ " ** " ^ to_string_vexp ve2 ^ ")"
     | VShiftL -> "(" ^ to_string_vexp ve1 ^ " << " ^ to_string_vexp ve2 ^ ")"
     | VShiftR -> "(" ^ to_string_vexp ve1 ^ " >> " ^ to_string_vexp ve2 ^ ")"
     | VBXor   -> "(" ^ to_string_vexp ve1 ^ " ^ " ^ to_string_vexp ve2 ^ ")"
     | VBAnd   -> "(" ^ to_string_vexp ve1 ^ " & " ^ to_string_vexp ve2 ^ ")"
     | VBOr   -> "(" ^ to_string_vexp ve1 ^ " | " ^ to_string_vexp ve2 ^ ")")
  | VUnOp (vuop,ve,_) ->
    (match vuop with
     | VNeg -> "(" ^ " - " ^ to_string_vexp ve ^ ")"
     | VBNot -> "(" ^ " ~ " ^ to_string_vexp ve ^ ")")
  | VCast (typ,ve) -> to_string_typ typ ^ "(" ^ to_string_vexp ve ^ ")"
  | VCond f -> to_string_vformula f
  | Ite (e1,e2,e3) -> "ite" ^ "(" ^ to_string_vexp e1 ^ ", " ^ to_string_vexp e2 ^ ", " ^ to_string_vexp e3 ^ ")"

let rec get_type_vexp : vexp -> typ
= fun vexp ->
  match vexp with
  | VInt _ -> ConstInt
  | VVar (_,typ) -> typ
  | Read (_,_,typ) -> typ
  | Write (ve,_,_) -> get_type_vexp ve
  | VBinOp (_,_,_,typ) -> typ
  | VCast (typ,_) -> typ
  | VCond _ -> EType Bool
  | VUnOp (_,_,typ) -> typ
  | Ite (_,e1,e2) ->
    let t1, t2 = get_type_vexp e1, get_type_vexp e2 in 
    let _ = assert (t1 = t2) in
    t1

let rec free_vf : vformula -> var BatSet.t
= fun vf ->
  match vf with
  | VTrue | VFalse -> BatSet.empty
  | VNot f -> free_vf f
  | VAnd (f1,f2) -> BatSet.union (free_vf f1) (free_vf f2)
  | VOr (f1,f2) -> BatSet.union (free_vf f1) (free_vf f2)
  | VBinRel (_,e1,e2) -> BatSet.union (free_ve e1) (free_ve e2)
  | Imply (f1,f2) -> BatSet.union (free_vf f1) (free_vf f2)
  | SigmaEqual (e,x) -> BatSet.union (free_ve e) (BatSet.singleton x)
  | NoOverFlow x -> BatSet.singleton x
  | ForAll (vars,f) -> BatSet.diff (free_vf f) (BatSet.of_list vars) 
  | Label (_,f) -> free_vf f

and free_ve : vexp -> var BatSet.t
= fun ve ->
  match ve with
  | VInt _ -> BatSet.empty
  | VVar (x,t) -> BatSet.singleton (x,t)
  | Read (e1,e2,_) -> BatSet.union (free_ve e1) (free_ve e2)
  | Write (e1,e2,e3) -> BatSet.union (free_ve e1) (BatSet.union (free_ve e2) (free_ve e3)) 
  | VBinOp (_,e1,e2,_) -> BatSet.union (free_ve e1) (free_ve e2) 
  | VCast (_,e) -> free_ve e
  | VUnOp (_,e,_) -> free_ve e 
  | VCond f -> free_vf f
  | Ite (e1,e2,e3) -> BatSet.union (free_ve e1) (BatSet.union (free_ve e2) (free_ve e3)) 

let split_implication : vformula -> vformula * vformula
= fun vf ->
  match vf with
  | Imply (pre,con) -> (pre,con)
  | _ -> raise (Failure "split_implication")

let split_vc : vformula -> vformula * vformula
= fun vf ->
  match vf with
  | VAnd (pgm_const, VNot safety) -> (pgm_const, safety)
  | _ -> raise (Failure "split_vc")

let rec list_of_conjuncts : vformula -> vformula list
= fun vf ->
  match vf with
  | VTrue | VFalse -> [vf]
  | VNot f -> [vf]
  | VAnd (f1,f2) -> (list_of_conjuncts f1) @ (list_of_conjuncts f2)
  | VOr _ -> [vf]
  | VBinRel _ -> [vf]
  | Imply _ -> [vf]
  | SigmaEqual _
  | NoOverFlow _
  | ForAll _ -> [vf]
  | Label (_,f) -> list_of_conjuncts f

let cartesian_two : vformula list -> vformula list list
= fun flst -> BatList.n_cartesian_product [flst;flst]

let cartesian_three : vformula list -> vformula list list
= fun flst -> BatList.n_cartesian_product [flst;flst;flst]

let cartesian_four : vformula list -> vformula list list
= fun flst ->
  let flst1 = List.filter (fun vf -> match vf with NoOverFlow _ -> true | _ -> false) flst in
  let flst2 = List.filter (fun vf -> match vf with SigmaEqual _ | VBinRel (VGeq, Read (VVar _, VVar _, _), VVar _) -> true | _ -> false) flst in
  let flst3 = List.filter (fun vf ->
                match vf with
                | VBinRel (VEq, VVar _, VInt _)
                | VBinRel (VGeq, VInt _, VVar _)
                | VBinRel (VEq, VVar _, Write (VVar _, VVar _, VBinOp (VSub, Read (VVar _, VVar _,_), VVar _, _)))
                | VBinRel (VEq, VVar _, Write (VVar _, VVar _, VBinOp (VAdd, Read (VVar _, VVar _,_), VVar _, _))) -> true
                | _ -> false
              ) flst in
  let flst4 = List.filter (fun vf ->
                match vf with
                | VBinRel (VGeq, Read (VVar _,VVar _,_), VVar _)
                | VBinRel (VEq, VVar _, Write (VVar _, VVar _, VBinOp (VSub, Read (VVar _, VVar _,_), VVar _, _)))
                | VBinRel (VEq, VVar _, Write (VVar _, VVar _, VBinOp (VAdd, Read (VVar _, VVar _,_), VVar _, _))) -> true
                | _ -> false
              ) flst in
  BatList.n_cartesian_product [flst1;flst2;flst3;flst4]

let cartesian_five : vformula list -> vformula list list
= fun flst ->
  let flst1 = List.filter (fun vf -> match vf with NoOverFlow _ -> true | _ -> false) flst in
  let flst2 = List.filter (fun vf -> match vf with SigmaEqual _ | VBinRel (VGeq, Read (VVar _,VVar _,_), VVar _) -> true | _ -> false) flst in
  let flst3 = List.filter (fun vf ->
                match vf with
                | VBinRel (VEq, VVar _, VInt _)
                | VBinRel (VEq, VVar _, Write (VVar _, VVar _, VBinOp (VSub, Read (VVar _, VVar _,_), VVar _, _))) -> true
                | _ -> false
              ) flst in
  let flst4 = List.filter (fun vf ->
                match vf with
                | VBinRel (VGeq, Read (VVar _,VVar _,_), VVar _)
                | VBinRel (VEq, VVar _, Read (VVar _, VVar _, _)) -> true
                | _ -> false
              ) flst in
  let flst5 = List.filter (fun vf ->
                match vf with
                | VBinRel (VEq, VVar _, Read (VVar _, VVar _, _))
                | VBinRel (VEq, VVar _, VVar _) -> true
                | _ -> false
              ) flst in
  BatList.n_cartesian_product [flst1;flst2;flst3;flst4;flst5]

let cartesian_six : vformula list -> vformula list list
= fun flst ->
  let flst1 = List.filter (fun vf -> match vf with NoOverFlow _ -> true | _ -> false) flst in
  let flst2 = List.filter (fun vf -> match vf with SigmaEqual _ -> true | _ -> false) flst in
  let flst3 = List.filter (fun vf -> match vf with VBinRel (VGeq,VInt _,VVar _) | VBinRel (VEq,VVar _,VInt _) -> true | _ -> false) flst in
  let flst4 = List.filter (fun vf -> match vf with VBinRel (VGeq, Read (VVar _, VVar _, _), VVar _) -> true | _ -> false) flst in
  let flst5 = List.filter (fun vf -> match vf with VBinRel (VEq, VVar _, Write (VVar _, VVar _, VBinOp (VSub, Read (VVar _, VVar _,_), VVar _, _))) -> true | _ -> false) flst in
  let flst6 = List.filter (fun vf -> match vf with VBinRel (VEq, VVar _, Write (VVar _, VVar _, VBinOp (VAdd, Read (VVar _, VVar _,_), VVar _, _))) -> true | _ -> false) flst in
  BatList.n_cartesian_product [flst1;flst2;flst3;flst4;flst5;flst6]

let rec has_label : vformula -> bool
= fun vf ->
  match vf with
  | VTrue | VFalse -> false
  | VNot f -> has_label f
  | VAnd (f1,f2) -> has_label f1 || has_label f2
  | VOr (f1,f2) -> has_label f1 || has_label f2
  | VBinRel _ -> false
  | Imply (f1,f2) -> has_label f1 || has_label f2
  | SigmaEqual _ -> false
  | NoOverFlow _ -> false
  | ForAll (_,f) -> has_label f
  | Label _ -> true

let rec has_noflow : vformula -> bool
= fun vf ->
  match vf with
  | VTrue | VFalse -> false
  | VNot f -> has_noflow f
  | VAnd (f1,f2) -> has_noflow f1 || has_noflow f2
  | VOr (f1,f2) -> has_noflow f1 || has_noflow f2
  | VBinRel _ -> false
  | Imply (f1,f2) -> has_noflow f1 || has_noflow f2
  | SigmaEqual _ -> false
  | NoOverFlow _ -> true
  | ForAll (_,f) -> has_noflow f 
  | Label (_,f) -> has_noflow f

let rec has_sigeq : vformula -> bool
= fun vf ->
  match vf with
  | VTrue | VFalse -> false
  | VNot f -> has_sigeq f
  | VAnd (f1,f2) -> has_sigeq f1 || has_sigeq f2
  | VOr (f1,f2) -> has_sigeq f1 || has_sigeq f2
  | VBinRel _ -> false
  | Imply (f1,f2) -> has_sigeq f1 || has_sigeq f2 
  | SigmaEqual _ -> true
  | NoOverFlow _ -> false
  | ForAll (_,f) -> has_sigeq f 
  | Label (_,f) -> has_sigeq f

let rec rewrite_vf : vformula -> vexp -> vexp -> vformula
= fun vformula target replacement -> 
  match vformula with
  | VTrue | VFalse -> vformula
  | VNot vf -> VNot (rewrite_vf vf target replacement)
  | VAnd (vf1,vf2) -> VAnd (rewrite_vf vf1 target replacement, rewrite_vf vf2 target replacement)
  | VOr (vf1,vf2) -> VOr (rewrite_vf vf1 target replacement, rewrite_vf vf2 target replacement)
  | VBinRel (vbrel,ve1,ve2) -> VBinRel (vbrel, rewrite_ve ve1 target replacement, rewrite_ve ve2 target replacement)
  | Imply (vf1,vf2) -> Imply (rewrite_vf vf1 target replacement, rewrite_vf vf2 target replacement)
  | SigmaEqual (e, (m,t)) ->
    let e' = rewrite_ve e target replacement in
    let m' = if BatString.equal m (to_string_vexp target) then to_string_vexp replacement else m in
    SigmaEqual (e', (m',t))
  | NoOverFlow (x,t) -> 
    if BatString.equal x (to_string_vexp target) then NoOverFlow (to_string_vexp replacement, t)
    else vformula
  | ForAll (vars,vf) -> ForAll (vars, rewrite_vf vf target replacement)
  | Label (l,vf) -> Label (l, rewrite_vf vf target replacement)

and rewrite_ve : vexp -> vexp -> vexp -> vexp
= fun vexp target replacement -> 
  match vexp with
  | VInt _ -> vexp
  | VVar _ ->
    if equal_ve vexp target then replacement
    else vexp
  | Read (e1,e2,typ) -> Read (rewrite_ve e1 target replacement, rewrite_ve e2 target replacement, typ) 
  | Write (e1,e2,e3) -> Write (rewrite_ve e1 target replacement, rewrite_ve e2 target replacement, rewrite_ve e3 target replacement) 
  | VBinOp (vbop,e1,e2,typ) -> VBinOp (vbop, rewrite_ve e1 target replacement, rewrite_ve e2 target replacement, typ)
  | VUnOp (vuop,e,typ) -> VUnOp (vuop, rewrite_ve e target replacement, typ)
  | VCast (typ,e) -> VCast (typ, rewrite_ve e target replacement)
  | VCond f -> VCond (rewrite_vf f target replacement)
  | Ite (e1,e2,e3) -> Ite (rewrite_ve e1 target replacement, rewrite_ve e2 target replacement, rewrite_ve e3 target replacement) 

let rec weaken_vf : vformula -> vid -> vformula
= fun vf target -> (* remove 'target' var in vf *)
  match vf with
  | VTrue | VFalse -> vf
  | VNot f ->
    let f' = weaken_vf f target in
    if equal_vf f' VTrue then VTrue
    else VNot f' 
  | VAnd (f1,f2) -> VAnd (weaken_vf f1 target, weaken_vf f2 target) 
  | VOr (f1,f2) -> VOr (weaken_vf f1 target, weaken_vf f2 target) 
  | VBinRel (vbrel,e1,e2) ->
    if BatSet.mem target (BatSet.union (BatSet.map fst (free_ve e1)) (BatSet.map fst (free_ve e2))) then VTrue
    else vf
  | Imply (f1,f2) -> Imply (weaken_vf f1 target, weaken_vf f2 target)
  | SigmaEqual (e,(x,_)) ->
    if BatString.equal x target then VTrue else
    if BatSet.mem target (BatSet.map fst (free_ve e)) then VTrue
    else vf
  | NoOverFlow (x,_) ->
    if BatString.equal x target then VTrue
    else vf
  | ForAll (vars,f) -> ForAll (vars, weaken_vf f target)
  | Label (l,f) -> Label (l, weaken_vf f target)

(**********************************)
(**********************************)
(** Transform special predicates **)
(**********************************)
(**********************************)

let rec make_powerset : 'a list -> 'a list list
= fun lst ->
  match lst with
  | [] -> [[]]
  | hd::tl ->
    let ps = make_powerset tl in
    ps @ List.map (fun lst' -> hd::lst') ps

(* [p;q;r;s] => [(p,q); (q,r); (r,s)] *)
let rec make_pairs : 'a list -> ('a * 'a) list 
= fun lst ->
  match lst with
  | h1::h2::[] -> [(h1,h2)]
  | h1::h2::tl -> (h1,h2)::(make_pairs (h2::tl)) 
  | _ -> raise (Failure "make_pairs")

(* assume all exps have address type *)
let make_all_neq : (vexp * vexp) list -> vformula 
= fun pairs ->
  List.fold_left (fun acc (e1,e2) ->
    let neq = VNot (VBinRel (VEq, e1, e2)) in
    if equal_vf acc VTrue then neq
    else VAnd (acc, neq) 
  ) VTrue pairs

(* assume all exps have address type *)
let make_all_eq : (vexp * vexp) list -> vformula
= fun pairs ->
  List.fold_left (fun acc (e1,e2) ->
    let eq = VBinRel (VEq, e1, e2) in
    if equal_vf acc VTrue then eq
    else VAnd (acc, eq) 
  ) VTrue pairs

let make_elems : vexp -> ExpSet.t -> vexp list
= fun mapvar addrs ->
  let elemtyp = match (get_type_vexp mapvar) with Mapping (Address, t) -> t | _ -> assert false in
  let org_x = try fst (BatString.split (to_string_vexp mapvar) "(#") with Not_found -> to_string_vexp mapvar in
  let remainder = VVar ("@R_"^org_x, elemtyp) in
  ExpSet.fold (fun addr acc ->
    (Read (mapvar, addr, elemtyp))::acc
  ) addrs [remainder] 

let rec make_sum_of_elems : vexp list -> vexp 
= fun lst ->
  match lst with
  | ve::[] -> ve (* when there does not exist addr expressions in the basic path *)
  | ve1::ve2::[] ->
    let (typ1,typ2) = (get_type_vexp ve1, get_type_vexp ve2) in
    let _ = assert (equal_typ typ1 typ2) in 
    VBinOp (VAdd,ve1,ve2,typ1) 
  | ve1::ve2::tl ->
    let (typ1,typ2) = (get_type_vexp ve1, get_type_vexp ve2) in
    let _ = assert (equal_typ typ1 typ2) in 
    let plus = VBinOp (VAdd,ve1,ve2,typ1) in
    make_sum_of_elems (plus::tl)
  | _ -> raise (Failure "make_sum_of_elems")

let add_safe : vexp -> vexp -> vformula
= fun ve1 ve2 ->
  let (typ1,typ2) = (get_type_vexp ve1, get_type_vexp ve2) in
  let _ = assert (equal_typ typ1 typ2) in 
  VBinRel (VGeq,VBinOp (VAdd, ve1, ve2, typ1), ve2) 

let rec all_elems_no_flow : vexp list -> vformula 
= fun lst ->
  match lst with
  | ve1::ve2::[] -> add_safe ve1 ve2
  | ve1::ve2::tl ->
    let (typ1,typ2) = (get_type_vexp ve1, get_type_vexp ve2) in
    let _ = assert (equal_typ typ1 typ2) in 
    let plus = VBinOp (VAdd,ve1,ve2,typ1) in
    VAnd (add_safe ve1 ve2, all_elems_no_flow (plus::tl)) 
  | _ -> raise (Failure "all_elems_no_flow") 

module PartitionSet = BatSet.Make (struct type t = ExpSet.t let compare = ExpSet.compare let to_string = string_of_set (string_of_set to_string_vexp) end) 

let rec f : ExpSet.t -> int -> PartitionSet.t list
= fun set k ->
  if k = 1 then [PartitionSet.singleton set] else
  if ExpSet.cardinal set = k then
    [ExpSet.fold (fun e acc ->
      PartitionSet.add (ExpSet.singleton e) acc
     ) set PartitionSet.empty] 
  else
    let e',set' = ExpSet.pop set in
    (* scenario: {{p,q}, {r,s}} *)
    (* if a new element is 'e', outputs {{p,q}, {r,s}, {e}} for each scenario. *)
    let case1 =
      List.map (fun partition_set -> PartitionSet.add (ExpSet.singleton e') partition_set) (f set' (k-1))
    in
    let case2 =
      List.fold_left (fun acc scenario -> (* partition scenario : {{p,q}, {r,s}} *)
        (* when existing scenario is {{p,q}, {r,s}}, outputs {{p,q,e'}, {r,s}} and {{p,q}, {r,s,e'}} *)
        PartitionSet.fold (fun partition acc' -> (* partition: {p,q} *)
          let replaced = PartitionSet.update partition (ExpSet.add e' partition) scenario in
          acc' @ [replaced]
        ) scenario acc
      ) [] (f set' k)
    in
    case1 @ case2

let rec upto set n =
  if n=1 then f set 1
  else (upto set (n-1)) @ (f set n)
  
let make_pre_eq : PartitionSet.t -> vformula 
= fun partition_set ->
  PartitionSet.fold (fun partition acc ->
    ExpSet.fold (fun e1 acc' ->
      ExpSet.fold (fun e2 acc'' ->
        if equal_ve e1 e2 then acc''
        else VAnd (acc'', VBinRel (VEq, e1, e2))
      ) partition acc'
    ) partition acc
  ) partition_set VTrue 

let make_pre_neq : PartitionSet.t -> vformula 
= fun partition_set ->
  let lst = PartitionSet.to_list partition_set in
  let cartesian = BatList.cartesian_product lst lst in
  List.fold_left (fun acc (partition1, partition2) ->
    if ExpSet.equal partition1 partition2 then acc
    else
      ExpSet.fold (fun e1 acc' ->
        ExpSet.fold (fun e2 acc'' ->
          VAnd (acc'', VNot (VBinRel (VEq, e1, e2)))
        ) partition2 acc'
      ) partition1 acc
  ) VTrue cartesian

let make_sum : vexp -> vexp -> PartitionSet.t -> vformula 
= fun ve mapvar partition_set ->
  let distinct_addrs = PartitionSet.fold (fun partition acc -> ExpSet.add (ExpSet.choose partition) acc) partition_set ExpSet.empty in
  let sum_of_elems = make_sum_of_elems (make_elems mapvar distinct_addrs) in
  VBinRel (VEq, ve, sum_of_elems)

let make_sigma_eq : vexp -> vexp -> ExpSet.t -> vformula
= fun ve mapvar addrs ->
  if ExpSet.is_empty addrs || ExpSet.cardinal addrs = 1 then
    VBinRel (VEq, ve, make_sum_of_elems (make_elems mapvar addrs))
  else
    let all_partitions = upto addrs (ExpSet.cardinal addrs) in
    List.fold_left (fun acc partition_set ->
      let pre_eq = make_pre_eq partition_set in
      let pre_neq = make_pre_neq partition_set in
      let sum = make_sum ve mapvar partition_set in 
      VAnd (acc, Imply (VAnd (pre_eq, pre_neq), sum))
    ) VTrue all_partitions

let make_sum_no_flow : vexp -> PartitionSet.t -> vformula
= fun mapvar partition_set ->
  let distinct_addrs = PartitionSet.fold (fun partition acc -> ExpSet.add (ExpSet.choose partition) acc) partition_set ExpSet.empty in
  let elems = make_elems mapvar distinct_addrs in
  all_elems_no_flow elems 

let make_no_flow : vexp -> ExpSet.t -> vformula
= fun mapvar addrs ->
  let org_x = try fst (BatString.split (to_string_vexp mapvar) "(#") with Not_found -> to_string_vexp mapvar in
  let remainder_no_flow = VBinRel (VEq, VVar ("@noflow_"^org_x, EType Bool), VCond VTrue) in
  if ExpSet.is_empty addrs then remainder_no_flow else
  if ExpSet.cardinal addrs = 1 then
    VAnd (all_elems_no_flow (make_elems mapvar addrs), remainder_no_flow) 
  else
    let all_partitions = upto addrs (ExpSet.cardinal addrs) in
    let sum_no_flow =
      List.fold_left (fun acc partition_set ->
        let pre_eq = make_pre_eq partition_set in
        let pre_neq = make_pre_neq partition_set in
        let sum_no_flow = make_sum_no_flow mapvar partition_set in
        VAnd (acc, Imply (VAnd (pre_eq, pre_neq), sum_no_flow))
      ) VTrue all_partitions
    in
    VAnd (sum_no_flow, remainder_no_flow)

let rec get_addrs_f : id -> vformula -> ExpSet.t
= fun x vf ->
  match vf with
  | VTrue | VFalse -> ExpSet.empty
  | VNot f -> get_addrs_f x f
  | VAnd (f1,f2) -> ExpSet.union (get_addrs_f x f1) (get_addrs_f x f2)
  | VOr (f1,f2) -> ExpSet.union (get_addrs_f x f1) (get_addrs_f x f2)
  | VBinRel (_,e1,e2) -> ExpSet.union (get_addrs_e x e1) (get_addrs_e x e2)
  | Imply (f1,f2) -> ExpSet.union (get_addrs_f x f1) (get_addrs_f x f2)
  | SigmaEqual _ -> ExpSet.empty
  | NoOverFlow _ -> ExpSet.empty
  | ForAll (_,f) -> get_addrs_f x f
  | Label (_,f) -> get_addrs_f x f

and get_addrs_e : id -> vexp -> ExpSet.t
= fun x ve ->
  match ve with
  | VInt _ -> ExpSet.empty
  | VVar _ -> ExpSet.empty
  | Read (VVar (y1,t1), e2, _)
    when (BatString.equal x y1 || BatString.starts_with y1 (x^"(#"))
         (* && is_address (get_type_vexp e2) *)
    -> ExpSet.singleton e2
  | Read (e1,e2,_) -> ExpSet.union (get_addrs_e x e1) (get_addrs_e x e2) 
  | Write (VVar (y1,t1), e2, e3)
    when (BatString.equal x y1 || BatString.starts_with y1 (x^"(#"))
         (* && is_address (get_type_vexp e2) *)
    -> ExpSet.union (ExpSet.singleton e2) (get_addrs_e x e3)
  | Write (e1,e2,e3) ->
    ExpSet.union (get_addrs_e x e1) (ExpSet.union (get_addrs_e x e2) (get_addrs_e x e3))
  | VBinOp (_,e1,e2,_) -> ExpSet.union (get_addrs_e x e1) (get_addrs_e x e2)
  | VUnOp (_,e,_) -> get_addrs_e x e
  | VCast (_,e) -> get_addrs_e x e
  | VCond f -> get_addrs_f x f
  | Ite (e1,e2,e3) -> 
    ExpSet.union (get_addrs_e x e1) (ExpSet.union (get_addrs_e x e2) (get_addrs_e x e3))

let rec trans_f : vformula -> vformula -> vformula
= fun whole vf ->
  match vf with
  | VTrue | VFalse -> vf
  | VNot f -> VNot (trans_f whole f)
  | VAnd (NoOverFlow (x1,t1), SigmaEqual (VInt n, (x2,t2)))
    when BatString.equal x1 x2 && BatBig_int.equal n BatBig_int.zero ->
    (* NoOverFlow(b) /\ Sigma(b)=0 : @R=0 /\ @NF /\ forall x.b[x]=0 *)
    let _ = assert (t1=t2) in
    let org_x = try fst (BatString.split x1 "(#") with Not_found -> x1 in
    let addrs = get_addrs_f org_x whole in
    let elemtyp = match t1 with Mapping (Address, t) -> t | _ -> assert false in
    let remainder = VVar ("@R_"^org_x, elemtyp) in
    let remainder_no_flow = VBinRel (VEq, VVar ("@noflow_"^org_x, EType Bool), VCond VTrue) in
    ExpSet.fold (fun addr acc ->
      VAnd (acc, VBinRel (VEq, Read (VVar (x1,t1), addr, elemtyp), VInt BatBig_int.zero))
    ) addrs (VAnd (VBinRel (VEq, remainder, VInt BatBig_int.zero), remainder_no_flow))
  | VAnd (f1,f2) -> VAnd (trans_f whole f1, trans_f whole f2)
  | VOr (f1,f2) -> VOr (trans_f whole f1, trans_f whole f2) 
  | VBinRel (brel,e1,e2) -> vf
  | Imply (f1,f2) -> Imply (trans_f whole f1, trans_f whole f2)
  | SigmaEqual (e,(x,t)) ->
    let org_x = try fst (BatString.split x "(#") with Not_found -> x in
    let addrs = get_addrs_f org_x whole in
    make_sigma_eq e (VVar (x,t)) addrs
  | NoOverFlow (x,t) ->
    let org_x = try fst (BatString.split x "(#") with Not_found -> x in
    let addrs = get_addrs_f org_x whole in
    make_no_flow (VVar (x,t)) addrs
  | ForAll _ -> failwith "trans_f : forAll encountered"
  | Label (l,f) -> Label (l, trans_f whole f)

let transform : vformula -> vformula
= fun vf -> trans_f vf vf

let get_bigint_v : vexp -> BatBig_int.t 
= fun ve ->
  match ve with
  | VInt n -> n
  | VUnOp (VNeg,VInt n,ConstInt) -> BatBig_int.neg n
  | VUnOp (VBNot,VInt n,ConstInt) -> n
  | _ -> failwith "get_bigint"

(*************************)
(*** Make fresh symbol ***)
(*************************)

let newsym_cnt = ref 0
let newsym = "@SYM__"

let gen_newsym typ =
  newsym_cnt:=!newsym_cnt+1;
  (newsym ^ (string_of_int !newsym_cnt), typ)

(**********************************************)
(*** Ghost variables for analyzing Solidity ***)
(**********************************************)

let trust_map = ("@TU", Mapping (Address, EType Bool))
let invest_map = ("@Invest", Mapping (Address, EType (UInt 256))) (* addresses that have sent money to contracts *)
let eth_map = ("@Eth", Mapping (Address, EType (UInt 256)))
let this_addr = ("@thisAddr", EType Address)
let length_map = "@L" (* length variable may have different types *)

let global_ghost_var_names = ["@TU"; "@Invest"; "@Eth"; "@thisAddr"; "@L"]
