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
  | SigmaEqual of var * vexp (* left: mapping, right: uint *)
  | NoOverFlow of var
  | UntrustSum of var * var (* sum of untrustworthy accounts *)
  | UntrustSum2 of var * var * var (* invsum, struct, member *)
  | ForAll of var list * vformula
  | Label of int * vformula (* 0: assignment, 1: assume *)

and vexp =
  | VInt of BatBig_int.t
  | VVar of var
  | Read of vexp * vexp (* A[i] *)
  | Write of vexp * vexp * vexp (* A[i] := v, return A *)
  | VBinOp of vbop * vexp * vexp * typ
  | VUnOp of vuop * vexp * typ
  | VCast of typ * vexp
  | VCond of vformula
  | Ite of vexp * vexp * vexp
  | Uninterp of string * vexp list * typ (* (fname, args, return typ) *)

and vid = string
and vbrel = VGeq | VGt | VEq
and vbop = VAdd | VSub | VMul | VDiv | VMod | VPower
           | VShiftL | VShiftR | VBXor | VBAnd | VBOr
           | VBVConcat (* bitvector concatenation *)
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
  | SigmaEqual (x1,e1), SigmaEqual (x2,e2) ->
    let c = Stdlib.compare x1 x2 in
    if c = 0 then compare_ve e1 e2 else c
  | NoOverFlow x1, NoOverFlow x2 -> Stdlib.compare x1 x2
  | UntrustSum (x1,x1'), UntrustSum (x2,x2') ->
    let c = Stdlib.compare x1 x2 in
    if c = 0 then Stdlib.compare x1' x2' else c
  | UntrustSum2 (x1,x1',x1''), UntrustSum2 (x2,x2',x2'') ->
    let c1 = Stdlib.compare x1 x2 in
    if c1 = 0 then
      let c2 = Stdlib.compare x1' x2' in
      if c2 = 0 then Stdlib.compare x1'' x2''
      else c2
    else c1
  | ForAll (_,f1), ForAll (_,f2) -> compare_vf f1 f2
  | _ -> Stdlib.compare (tag_of_vf vf1) (tag_of_vf vf2)

and compare_ve ve1 ve2 =
  match ve1,ve2 with
  | VInt n1,VInt n2 -> BatBig_int.compare n1 n2 
  | VVar (x1,t1),VVar (x2,t2) ->
    let c = BatString.compare x1 x2 in
    if c = 0 then Stdlib.compare t1 t2 else c
  | Read (e1,e1'), Read (e2,e2') ->
    let c1 = compare_ve e1 e2 in
    if c1 = 0 then compare_ve e1' e2'
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
  | Uninterp (fname1,args1,t1), Uninterp (fname2,args2,t2) ->
    let c1 = Stdlib.compare fname1 fname2 in
    if c1 = 0 then
      let c2 = Vocab.compare_lst compare_ve args1 args2 in
      if c2 = 0 then Stdlib.compare t1 t2 else c2
    else c1
  | _ -> Stdlib.compare (tag_of_ve ve1) (tag_of_ve ve2)

and tag_of_vf = function 
  | VTrue -> 0 | VFalse -> 1 | VNot _ -> 2 | VAnd _ -> 3 | VOr _ -> 4 | VBinRel _ -> 5
  | Imply _ -> 6 | SigmaEqual _ -> 7 | NoOverFlow _ -> 8 | UntrustSum _ -> 9 | UntrustSum2 _ -> 10
  | ForAll _ -> 11 | Label _ -> 12

and tag_of_brel = function
  | VGeq -> 0 | VGt -> 1 | VEq -> 2

and tag_of_ve = function
  | VInt _ -> 0 | VVar _ -> 1 | Read _ -> 2 | Write _ -> 3 | VBinOp _ -> 4
  | VUnOp _ -> 5 | VCast _ -> 6 | VCond _ -> 7 | Ite _ -> 8 | Uninterp _ -> 9

and tag_of_bop = function
  | VAdd -> 0 | VSub -> 1 | VMul -> 2 | VDiv -> 3 | VMod -> 4 | VPower -> 5
  | VShiftL -> 6 | VShiftR -> 7 | VBXor -> 8 | VBAnd -> 9 | VBOr -> 10
  | VBVConcat -> 11

and tag_of_uop = function
  | VNeg -> 0 | VBNot -> 1

let compare vf1 vf2 = compare_vf vf1 vf2
let equal_vf vf1 vf2 = if compare vf1 vf2 = 0 then true else false
let equal_ve ve1 ve2 = if compare_ve ve1 ve2 = 0 then true else false

module FormulaSet = BatSet.Make (struct type t = vformula let compare = compare end)
module ExpSet = BatSet.Make (struct type t = vexp let compare = compare_ve end)

(* e.g., org ("x(#1)") = "x" *)
let org : var -> var
= fun (x,t) -> try (fst (BatString.split x "(#"), t) with Not_found -> (x,t)

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
  | SigmaEqual ((m,t),e) -> "(" ^ "Σ" ^ m ^ " == " ^ to_string_vexp e ^ ")"
  | NoOverFlow (x,t) -> "NoOverFlow (" ^ "Σ" ^ x ^ ")"
  | UntrustSum ((isum,_),(m,_)) -> isum ^ " >= " ^ "Σ_u " ^ m
  | UntrustSum2 ((isum,_),(s,_),(mem,_)) -> isum ^ " >= " ^ "Σ_u,i " ^ mem ^ "[" ^ s ^ "[i]" ^ "]"
  | ForAll (vars,f) -> "(" ^ "forAll " ^ string_of_list Vocab.id (List.map fst vars) ^ "." ^ to_string_vformula f ^ ")"
  | Label (_,f) -> to_string_vformula f

and to_string_vexp ve =
  match ve with
  | VInt n -> BatBig_int.to_string n
  | VVar (x,_) -> x
  | Read (ve1,ve2) -> "Read" ^ "(" ^ to_string_vexp ve1 ^ ", " ^ to_string_vexp ve2 ^ ")"
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
     | VBOr   -> "(" ^ to_string_vexp ve1 ^ " | " ^ to_string_vexp ve2 ^ ")"
     | VBVConcat -> "(" ^ to_string_vexp ve1 ^ " ~~ " ^ to_string_vexp ve2 ^ ")")
  | VUnOp (vuop,ve,_) ->
    (match vuop with
     | VNeg -> "(" ^ " - " ^ to_string_vexp ve ^ ")"
     | VBNot -> "(" ^ " ~ " ^ to_string_vexp ve ^ ")")
  | VCast (typ,ve) -> to_string_typ typ ^ "(" ^ to_string_vexp ve ^ ")"
  | VCond f -> to_string_vformula f
  | Ite (e1,e2,e3) -> "ite" ^ "(" ^ to_string_vexp e1 ^ ", " ^ to_string_vexp e2 ^ ", " ^ to_string_vexp e3 ^ ")"
  | Uninterp (fname,args,typ) -> fname ^ string_of_list ~first:"(" ~sep:", " ~last:")" to_string_vexp args

let rec get_typ_vexp : vexp -> typ
= fun vexp ->
  match vexp with
  | VInt _ -> ConstInt
  | VVar (_,typ) -> typ
  | Read (ve,_) -> range_typ (get_typ_vexp ve)
  | Write (ve,_,_) -> get_typ_vexp ve
  | VBinOp (_,_,_,typ) -> typ
  | VCast (typ,_) -> typ
  | VCond _ -> EType Bool
  | VUnOp (_,_,typ) -> typ
  | Ite (_,e1,e2) ->
    let t1, t2 = get_typ_vexp e1, get_typ_vexp e2 in 
    let _ = assert (t1 = t2) in
    t1
  | Uninterp (_,_,typ) -> typ

let rec free_vf : vformula -> var BatSet.t
= fun vf ->
  match vf with
  | VTrue | VFalse -> BatSet.empty
  | VNot f -> free_vf f
  | VAnd (f1,f2) -> BatSet.union (free_vf f1) (free_vf f2)
  | VOr (f1,f2) -> BatSet.union (free_vf f1) (free_vf f2)
  | VBinRel (_,e1,e2) -> BatSet.union (free_ve e1) (free_ve e2)
  | Imply (f1,f2) -> BatSet.union (free_vf f1) (free_vf f2)
  | SigmaEqual (x,e) -> BatSet.union (BatSet.singleton x) (free_ve e)
  | NoOverFlow x -> BatSet.singleton x
  | UntrustSum (x1,x2) -> BatSet.of_list [x1;x2]
  | UntrustSum2 (x1,x2,x3) -> BatSet.of_list [x1;x2;x3]
  | ForAll (vars,f) -> BatSet.diff (free_vf f) (BatSet.of_list vars)
  | Label (_,f) -> free_vf f

and free_ve : vexp -> var BatSet.t
= fun ve ->
  match ve with
  | VInt _ -> BatSet.empty
  | VVar (x,t) -> BatSet.singleton (x,t)
  | Read (e1,e2) -> BatSet.union (free_ve e1) (free_ve e2)
  | Write (e1,e2,e3) -> BatSet.union (free_ve e1) (BatSet.union (free_ve e2) (free_ve e3)) 
  | VBinOp (_,e1,e2,_) -> BatSet.union (free_ve e1) (free_ve e2) 
  | VCast (_,e) -> free_ve e
  | VUnOp (_,e,_) -> free_ve e 
  | VCond f -> free_vf f
  | Ite (e1,e2,e3) -> BatSet.union (free_ve e1) (BatSet.union (free_ve e2) (free_ve e3))
  | Uninterp (_,args,_) -> List.fold_left (fun acc e' -> BatSet.union (free_ve e') acc) BatSet.empty args

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
  | SigmaEqual _ | NoOverFlow _
  | UntrustSum _ | UntrustSum2 _ | ForAll _ -> [vf]
  | Label (_,f) -> list_of_conjuncts f

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
  | UntrustSum _ -> false
  | UntrustSum2 _ -> false
  | ForAll (_,f) -> has_label f
  | Label _ -> true

let rec rewrite_vf : vformula -> vexp -> vexp -> vformula
= fun vformula target replacement -> 
  match vformula with
  | VTrue | VFalse -> vformula
  | VNot vf -> VNot (rewrite_vf vf target replacement)
  | VAnd (vf1,vf2) -> VAnd (rewrite_vf vf1 target replacement, rewrite_vf vf2 target replacement)
  | VOr (vf1,vf2) -> VOr (rewrite_vf vf1 target replacement, rewrite_vf vf2 target replacement)
  | VBinRel (vbrel,ve1,ve2) -> VBinRel (vbrel, rewrite_ve ve1 target replacement, rewrite_ve ve2 target replacement)
  | Imply (vf1,vf2) -> Imply (rewrite_vf vf1 target replacement, rewrite_vf vf2 target replacement)
  | SigmaEqual ((m,t), e) ->
    let m' = if BatString.equal m (to_string_vexp target) then to_string_vexp replacement else m in
    let e' = rewrite_ve e target replacement in
    SigmaEqual ((m',t), e')
  | NoOverFlow (x,t) -> 
    if BatString.equal x (to_string_vexp target) then NoOverFlow (to_string_vexp replacement, t)
    else vformula
  | UntrustSum ((x,xt),(m,mt)) ->
    let x' = if BatString.equal x (to_string_vexp target) then to_string_vexp replacement else x in
    let m' = if BatString.equal m (to_string_vexp target) then to_string_vexp replacement else m in
    UntrustSum ((x',xt),(m',mt))
  | UntrustSum2 ((x,xt),(s,st),(mem,memt)) ->
    let x' = if BatString.equal x (to_string_vexp target) then to_string_vexp replacement else x in
    let s' = if BatString.equal s (to_string_vexp target) then to_string_vexp replacement else s in
    let mem' = if BatString.equal mem (to_string_vexp target) then to_string_vexp replacement else mem in
    UntrustSum2 ((x',xt),(s',st),(mem',memt))
  | ForAll (vars,vf) -> ForAll (vars, rewrite_vf vf target replacement)
  | Label (l,vf) -> Label (l, rewrite_vf vf target replacement)

and rewrite_ve : vexp -> vexp -> vexp -> vexp
= fun vexp target replacement -> 
  match vexp with
  | VInt _ -> vexp
  | VVar _ ->
    if equal_ve vexp target then replacement
    else vexp
  | Read (e1,e2) -> Read (rewrite_ve e1 target replacement, rewrite_ve e2 target replacement)
  | Write (e1,e2,e3) -> Write (rewrite_ve e1 target replacement, rewrite_ve e2 target replacement, rewrite_ve e3 target replacement)
  | VBinOp (vbop,e1,e2,typ) -> VBinOp (vbop, rewrite_ve e1 target replacement, rewrite_ve e2 target replacement, typ)
  | VUnOp (vuop,e,typ) -> VUnOp (vuop, rewrite_ve e target replacement, typ)
  | VCast (typ,e) -> VCast (typ, rewrite_ve e target replacement)
  | VCond f -> VCond (rewrite_vf f target replacement)
  | Ite (e1,e2,e3) -> Ite (rewrite_ve e1 target replacement, rewrite_ve e2 target replacement, rewrite_ve e3 target replacement)
  | Uninterp (fname, args, typ) ->
    let args' = List.map (fun arg -> rewrite_ve arg target replacement) args in
    Uninterp (fname, args', typ)

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
  | SigmaEqual ((x,_),e) ->
    if BatString.equal x target then VTrue else
    if BatSet.mem target (BatSet.map fst (free_ve e)) then VTrue
    else vf
  | NoOverFlow (x,_) ->
    if BatString.equal x target then VTrue
    else vf
  | UntrustSum ((x1,t1),(x2,t2)) ->
    if BatString.equal target x1 || BatString.equal target x2 then VTrue
    else vf
  | UntrustSum2 ((x1,t1),(x2,t2),(x3,t3)) ->
    if BatString.equal target x1 || BatString.equal target x2 || BatString.equal target x3 then VTrue
    else vf
  | ForAll (vars,f) -> ForAll (vars, weaken_vf f target)
  | Label (l,f) -> Label (l, weaken_vf f target)

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

let trust_map = ("@TU", Mapping (Address, EType Bool)) (* trusted user or non-vulnerable user *)
let invest_map = ("@Invest", Mapping (Address, EType (UInt 256))) (* addresses that have sent money to contracts *)
let eth_map = ("@B", Mapping (Address, EType (UInt 256)))
let this_addr = ("@this", EType Address)
let length_map = "@L" (* length variable may have different types *)
let contract_account = ("@CA", EType Address)

let invest_sum = ("@Invest_sum", EType (UInt 256))

let global_ghost_var_names =
  ["@TU"; "@Invest"; "@Invest_sum"; "@B"; "@this"; "@L"; "@CA"; "@extern_called"]

(* make ghost variable at function entry *)
let label_var_entry : var -> var
= fun (x,t) -> (x ^ "@E", t)

(* make ghost variable at function exit *)
let label_var_exit : var -> var
= fun (x,t) -> (x ^ "@X", t)

let msg_sender = ("msg.sender", EType Address)
let msg_value = ("msg.value", EType (UInt 256))
let tx_origin = ("tx.origin", EType Address)
