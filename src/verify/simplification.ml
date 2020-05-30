open Lang
open Vlang
open ItvDom

(******************************)
(******************************)
(** Syntactic Simplification **)
(******************************)
(******************************)

let rec norm_vf : vformula -> vformula
= fun vf -> 
  match vf with
  | VTrue | VFalse -> vf
  | VNot VTrue -> VFalse
  | VNot VFalse -> VTrue
  | VNot (VBinRel (VGt,e1,e2)) -> VBinRel (VGeq,e2,e1) (* !(e1>e2) -> e2>=e1. *)
  | VNot f -> VNot (norm_vf f)
  | VAnd (VTrue,f) | VAnd (f,VTrue) -> norm_vf f
  | VAnd (VFalse,_)| VAnd (_,VFalse) -> VFalse
  | VAnd (f1,f2) when equal_vf f1 f2 -> f1
  | VAnd (VBinRel (VGeq,x1,y1), VBinRel (VGt,x2,y2))
    when equal_ve x1 x2 && equal_ve y1 y2 -> VBinRel (VGt,x1,y1)
  | VAnd (VBinRel (VGeq,x1,y1), VBinRel (VGeq,y2,x2))
    when equal_ve x1 x2 && equal_ve y1 y2 -> VBinRel (VEq,x1,y1)
    (* a = v1 
     * b = v2
     * -
     * c = a + b
     * c >= a
     * -
     * ret = c
     * tmp = ret
     * balance = write (balance', e1, e2, tmp)
     * *)
  | VAnd (VAnd (VAnd (VAnd (VAnd (VAnd (VAnd (VAnd (VAnd (f1,
                                                          VBinRel (VEq,a1,v1)),
                                                          VBinRel (VEq,b1,v2)),
                                                          f4),
                                                          VBinRel (VEq,c1,VBinOp (VAdd,a2,b2,t))),
                                                          VBinRel (VGeq,c2,a3)),
                                                          f7),
                                                          VBinRel (VEq,ret1,c3)),
                                                          VBinRel (VEq,tmp1,ret2)),
                                                          VBinRel (VEq,balance,Write (e1,e2,tmp2)))
    when equal_ve a1 a2 && equal_ve a2 a3 &&
         equal_ve b1 b2 &&
         equal_ve c1 c2 && equal_ve c2 c3 &&
         equal_ve ret1 ret2 &&
         equal_ve tmp1 tmp2
    ->
    let safe = VBinRel (VGeq,VBinOp (VAdd,v1,v2,t),v1) in
    let con = VBinRel (VEq,balance,Write (e1,e2,VBinOp (VAdd,v1,v2,t))) in
    VAnd (VAnd (VAnd (VAnd (f1,f4),f7),safe),con)
   (* a = v1
    * b = v2
    * X
    * a >= b
    * ret = a-b
    * tmp = ret
    * balance = Write (e1,e2,tmp) *)
  | VAnd (VAnd (VAnd (VAnd (VAnd (VAnd (VAnd (f1,
                                              VBinRel (VEq,a1,v1)),
                                              VBinRel (VEq,b1,v2)),
                                              f4),
                                              VBinRel (VGeq,a2,b2)),
                                              VBinRel (VEq,ret1,VBinOp (VSub,a3,b3,t2))),
                                              VBinRel (VEq,tmp1,ret2)),
                                              VBinRel (VEq,balance,Write (e1,e2,tmp2)))
    when equal_ve a1 a2 && equal_ve a2 a3 &&
         equal_ve b1 b2 && equal_ve b2 b3 &&
         equal_ve ret1 ret2 && equal_ve tmp1 tmp2
    ->
    VAnd (VAnd (VAnd (f1,f4),VBinRel (VGeq,v1,v2)), VBinRel (VEq,balance,Write (e1,e2,VBinOp (VSub,v1,v2,t2))))
  | VAnd (VAnd (VAnd (VAnd (VAnd (VAnd (f1,
                                        VBinRel (VEq,a1,v1)),
                                        VBinRel (VEq,b1,v2)),
                                        f3),
                                        VBinRel (VGeq,a2,b2)),
                                        VBinRel (VEq,ret1,VBinOp (VSub,a3,b3,t2))),
                                        VBinRel (VEq,tmp,ret2))
    when equal_ve a1 a2 && equal_ve a2 a3 &&
         equal_ve b1 b2 && equal_ve b2 b3 &&
         equal_ve ret1 ret2
    -> VAnd (VAnd (VAnd (f1,f3),VBinRel (VGeq,v1,v2)), VBinRel (VEq,tmp,VBinOp (VSub,v1,v2,t2)))
  | VAnd (f1,f2) -> VAnd (norm_vf f1, norm_vf f2)
  | VOr (VTrue,_) -> VTrue
  | VOr (_,VTrue) -> VTrue
  | VOr (f,VFalse) -> norm_vf f
  | VOr (VFalse,f) -> norm_vf f
    (* A=0 \/ (A!=0 /\ ((A*1)/A)=1)
     * i.e., 'A*1' is safe.
     * *)
  | VOr (VBinRel (VEq,e1,VInt n1),
         VAnd (VNot (VBinRel (VEq,e2,VInt n2)), VBinRel (VEq, VBinOp (VDiv, (VBinOp (VMul,e3,VInt n3,t)),e4,t'), VInt n4)))
    when BatBig_int.equal n1 BatBig_int.zero &&
         BatBig_int.equal n2 BatBig_int.zero &&
         BatBig_int.equal n3 BatBig_int.one &&
         BatBig_int.equal n4 BatBig_int.one &&
         equal_ve e1 e2 && equal_ve e2 e3 && equal_ve e3 e4 
    -> VTrue
  | VOr (f1,f2) -> VOr (norm_vf f1, norm_vf f2)
  | VBinRel (VEq,e1,e2) when equal_ve e1 e2 -> VTrue
  (* | VBinRel (VEq,VVar (x,xt),VVar (y,yt)) when x > y -> VBinRel (VEq,VVar (y,yt),VVar (x,xt)) *)
  | VBinRel (VEq,VInt n1,VInt n2) -> if BatBig_int.equal n1 n2 then VTrue else VFalse
  | VBinRel (VEq,VInt n,e) -> VBinRel (VEq,e,VInt n)
  | VBinRel (VEq,VCond VFalse,VCond VTrue) -> VFalse
  | VBinRel (VEq,VCond VTrue,VCond VFalse) -> VFalse
  | VBinRel (VGt,e1,e2) when equal_ve e1 e2 -> VFalse
  | VBinRel (VGeq,e1,e2) when equal_ve e1 e2 -> VTrue
  | VBinRel (VGeq, VInt n, VVar (x,t)) when is_uintkind t && BatBig_int.sign_big_int n = 0 -> VBinRel (VEq, VVar (x,t), VInt n)
  | VBinRel (VGeq, VVar (x,EType (UInt 8)), VInt n)
    when BatBig_int.sign_big_int (BatBig_int.modulo n (BatBig_int.of_int 256)) = 0 -> VTrue 
  | VBinRel (VGeq, VVar (_,t), VInt n) when is_uintkind t && BatBig_int.sign_big_int n = 0 -> VTrue
  | VBinRel (rel,e1,e2) -> VBinRel (rel, norm_ve e1, norm_ve e2)
    (* A = B / C /\ C != 0 -> A == 0 \/ (A != 0 /\ (A * C / A) == C)  *)
    (* e1  e2  e3   e4  n4   e5   n5    e6   n6    e7  e8   e9   e10  *)
    (* i.e., (B/C) * C is safe. *)
  | Imply (VAnd (VAnd (_,VBinRel (VEq,e1,VBinOp(VDiv,e2,e3,_))), VNot (VBinRel (VEq,e4,VInt n4))),
           VOr (VBinRel (VEq,e5,VInt n5),
                VAnd (VNot (VBinRel (VEq,e6,VInt n6)), VBinRel (VEq, VBinOp (VDiv, (VBinOp (VMul,e7,e8,_)),e9,_),e10))))
    when BatBig_int.equal n4 BatBig_int.zero &&
         BatBig_int.equal n5 BatBig_int.zero &&
         BatBig_int.equal n6 BatBig_int.zero &&
         equal_ve e1 e5 && equal_ve e5 e6 && equal_ve e6 e7 && equal_ve e7 e9 &&
         equal_ve e3 e4 && equal_ve e4 e8 && equal_ve e8 e10
    -> VTrue
  | Imply (f1,f2) -> Imply (norm_vf f1, norm_vf f2)
  | SigmaEqual _ -> vf
  | NoOverFlow _ -> vf
  | ForAll (vars,f) -> ForAll (vars, norm_vf f)
  | Label (_,f) -> norm_vf f

and norm_ve : vexp -> vexp
= fun ve ->
  match ve with
  | VInt _ | VVar _ -> ve
  | Read (e1,e2,t) -> ve (* optimize if neccesary *) 
  | Write (e1,e2,e3) -> ve
  | VBinOp (bop,e1,e2,t) -> VBinOp (bop, norm_ve e1, norm_ve e2,t)
  | VUnOp (VNeg,VInt n,ConstInt) -> VInt (BatBig_int.neg n)
  | VUnOp (uop,e,t) -> ve
  | VCast (t,e) -> VCast (t, norm_ve e)
  | VCond f -> VCond (norm_vf f)
  | Ite (e1,e2,e3) -> ve

let normalize vf = norm_vf vf

let rec fix_normalize x =
  let x' = normalize x in
    if equal_vf x' x then x'
    else fix_normalize x'

(* assume input is conjunctive invariant *)
let rec vf_to_set : vformula -> FormulaSet.t
= fun vf ->
  match vf with
  | VTrue | VFalse -> FormulaSet.singleton vf
  | VAnd (f1,f2) -> FormulaSet.union (vf_to_set f1) (vf_to_set f2)
  | VBinRel _ | SigmaEqual _ | NoOverFlow _ -> FormulaSet.singleton vf
  | VNot _ -> raise (Failure "vf_to_set : VNot")
  | VOr _ -> raise (Failure "vf_to_set : VOr")
  | Imply _ -> raise (Failure "vf_to_set : Imply")
  | ForAll _ -> raise (Failure "vf_to_set : ForAll")
  | Label _ -> raise (Failure "vf_to_set : Label")

let set_to_vf : FormulaSet.t -> vformula 
= fun set ->
  FormulaSet.fold (fun f acc ->
    if equal_vf acc VTrue then f
    else VAnd (acc,f) 
  ) set VTrue

let compress : vformula -> vformula
= fun vf -> set_to_vf (vf_to_set vf)

let rec fix x =
  let x' = compress (normalize x) in
    if equal_vf x' x then x'
    else fix x'

let simplify : vformula -> vformula
= fun vf -> fix vf

(*****************************)
(*****************************)
(** Semantic Simplification **)
(*****************************)
(*****************************)

let rec msg_num_const : Mem.t -> vformula -> vformula
= fun mem vf ->
  match vf with
  | VTrue | VFalse -> vf
  | VAnd (f1,f2) -> VAnd (msg_num_const mem f1, msg_num_const mem f2)
  | VBinRel (VGeq, VVar (x,xt), VInt n)
  | VBinRel (VEq, VVar (x,xt), VInt n)
  | VBinRel (VGeq, VInt n, VVar (x,xt)) ->
    let itv = Val.itv_of (Mem.find2 (x,xt) mem) in
    if is_uint256 xt && Itv.is_bot itv then VFalse
    else
    (match itv with
     | Itv (V l, V u) when BatBig_int.equal l u ->
       VBinRel (VEq, VVar (x,xt), VInt n)
     | _ -> vf) 
  | VBinRel _ -> vf
  | SigmaEqual _ | NoOverFlow _ -> vf
  | VNot _ | VOr _
  | Imply _ | ForAll _ | Label _ -> raise (Failure "msg_num_const")

let massage_numeric_constraints : vformula -> vformula
= fun vf ->
  let mem = ItvAnalysis2.run vf in
  msg_num_const mem vf

let simplify_both vf =
  let vf = massage_numeric_constraints vf in
  simplify vf

(*****************************)
(*****************************)
(** Remove Power Constraint **)
(*****************************)
(*****************************)

let rec include_pow_vf : vformula -> bool
= fun vf ->
  match vf with
  | VTrue | VFalse -> false
  | VNot f -> include_pow_vf f
  | VAnd (f1,f2) -> include_pow_vf f1 || include_pow_vf f2
  | VOr (f1,f2) -> include_pow_vf f1 || include_pow_vf f2
  | VBinRel (rel,e1,e2) -> include_pow_ve e1 || include_pow_ve e2
  | Imply (f1,f2) -> include_pow_vf f1 || include_pow_vf f2
  | SigmaEqual (e,v) -> include_pow_ve e
  | NoOverFlow v -> false
  | ForAll (vars,f) -> include_pow_vf f
  | Label (l,f) -> include_pow_vf f

and include_pow_ve : vexp -> bool
= fun ve ->
  match ve with
  | VInt _ | VVar _ -> false
  | Read (e1,e2,_) -> include_pow_ve e1 || include_pow_ve e2
  | Write (e1,e2,e3) -> include_pow_ve e1 || include_pow_ve e2 || include_pow_ve e3
  | VBinOp (VPower,_,_,_) -> true
  | VBinOp (_,e1,e2,_) -> include_pow_ve e1 || include_pow_ve e2
  | VUnOp (_,e,_) -> include_pow_ve e
  | VCast (_,e) -> include_pow_ve e
  | VCond f -> include_pow_vf f
  | Ite (e1,e2,e3) -> include_pow_ve e1 || include_pow_ve e2 || include_pow_ve e3

let rec rm_pow_vf : Mem.t -> vformula -> vformula * vexp list
= fun mem vf ->
  match vf with
  | VTrue | VFalse -> (vf, [])
  | VNot f ->
    let (f',lst) = rm_pow_vf mem f in
    (VNot f', lst)
  | VAnd (f1,f2) ->
    let (f1',lst1) = rm_pow_vf mem f1 in
    let (f2',lst2) = rm_pow_vf mem f2 in
    (VAnd (f1',f2'), lst1 @ lst2)
  | VOr (f1,f2) ->
    let (f1',lst1) = rm_pow_vf mem f1 in
    let (f2',lst2) = rm_pow_vf mem f2 in
    (VOr (f1',f2'), lst1 @ lst2)
  | VBinRel (brel,e1,e2) ->
    let (e1',lst1) = rm_pow_ve mem e1 in
    let (e2',lst2) = rm_pow_ve mem e2 in
    (VBinRel (brel,e1',e2'), lst1@lst2)
  | Imply (f1,f2) ->
    let (f1',lst1) = rm_pow_vf mem f1 in
    let (f2',lst2) = rm_pow_vf mem f2 in
    (Imply (f1',f2'), lst1 @ lst2)
  | SigmaEqual _ -> (vf,[])
  | NoOverFlow _ -> (vf,[])
  | ForAll (vars,f) ->
    let (f',lst) = rm_pow_vf mem f in
    (ForAll (vars, f'), lst)
  | Label (l,f) ->
    let (f',lst) = rm_pow_vf mem f in
    (Label (l, f'), lst)

and rm_pow_ve : Mem.t -> vexp -> vexp * vexp list
= fun mem ve ->
  match ve with
  | VInt _ -> (ve, [])
  | VVar _ -> (ve, [])
  | VBinOp (VPower,e1,e2,t) ->
    let (e1',lst1) = rm_pow_ve mem e1 in
    let (e2',lst2) = rm_pow_ve mem e2 in
    let ve' = VBinOp (VPower,e1',e2',t) in
    let itv_ve' = Val.itv_of (ItvSem2.eval_ve ve' mem) in
    if Itv.is_const itv_ve' then
      (VInt (Itv.lower_int itv_ve'), lst1 @ lst2)
    else (VVar (gen_newsym t), lst1 @ lst2)
  | VBinOp (bop,e1,e2,t) ->
    let (e1',lst1) = rm_pow_ve mem e1 in
    let (e2',lst2) = rm_pow_ve mem e2 in
    (VBinOp (bop, e1', e2', t), lst1 @ lst2)
  | Read (e1,e2,t) ->
    let (e1',lst1) = rm_pow_ve mem e1 in
    let (e2',lst2) = rm_pow_ve mem e2 in
    (Read (e1', e2', t), lst1 @ lst2)
  | Write (e1,e2,e3) ->
    let (e1',lst1) = rm_pow_ve mem e1 in
    let (e2',lst2) = rm_pow_ve mem e2 in
    let (e3',lst3) = rm_pow_ve mem e3 in
    (Write (e1', e2', e3'), lst1 @ lst2 @ lst3)
  | VUnOp (uop,e,t) ->
    let (e',lst) = rm_pow_ve mem e in
    if get_type_vexp e' = t then (VUnOp (uop, e', t), lst)
    else
      (* some fixed-size bit expressions may be converted into integer constant types *)
      (VUnOp (uop, VCast (t, e'), t), lst)
  | VCast (t,e) ->
    let (e',lst) = rm_pow_ve mem e in
    (VCast (t, e'), lst)
  | VCond f ->
    let (f',lst) = rm_pow_vf mem f in
    (VCond f', lst)
  | Ite (e1,e2,e3) ->
    let (e1',lst1) = rm_pow_ve mem e1 in
    let (e2',lst2) = rm_pow_ve mem e2 in
    let (e3',lst3) = rm_pow_ve mem e3 in
    (Ite (e1', e2', e3'), lst1 @ lst2 @ lst3)

let remove_pow : vformula -> vformula
= fun vf ->
  let (pre,sc) = split_implication vf in
  let mem = ItvAnalysis2.run pre in (* perform interval analysis on formula *)
  let (pre',lst1) = rm_pow_vf mem pre in
  let (sc',lst2) = rm_pow_vf mem sc in
  (* verification mode => no concretizations are performed. *)
  let _ = assert (List.length (lst1 @ lst2) = 0) in
  let final = Imply (pre',sc') in
  let _ = assert (not (include_pow_vf final)) in
  final
