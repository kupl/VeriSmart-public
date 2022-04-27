open Vlang
open Lang
open Vocab

(***************************************)
(*** Transform nonlinear expressions ***)
(*** into uninterpreted functions.   ***)
(***************************************)

let rec constrained : vformula -> var -> bool
= fun vf target ->
  match vf with
  | VTrue | VFalse -> false
  (* | VNot f -> constrained f target *)
  | VNot f -> false (* e.g., view "!(msg.value = 0)" as not constrained *)
  | VAnd (f1,f2) -> (constrained f1 target) || (constrained f2 target)
  | VOr (f1,f2) -> (constrained f1 target) || (constrained f2 target)
  | VBinRel (VGeq,VInt _,VVar x) when x = target -> true
  | VBinRel (VEq,VVar x,VInt _) when x = target -> true
  | VBinRel _ -> false
  | Imply (f1,f2) -> constrained (VOr (VNot f1, f2)) target
  | SigmaEqual _ | NoOverFlow _ | UntrustSum _ | UntrustSum2 _ -> assert false
  | ForAll (bvs,f) -> constrained f target
  | Label (l,f) -> constrained f target

let rec trans_f : vformula -> vformula -> vformula
= fun state vf ->
  match vf with
  | VTrue | VFalse -> vf
  | VNot f -> VNot (trans_f state f)
  | VAnd (f1,f2) -> VAnd (trans_f state f1, trans_f state f2)
  | VOr (f1,f2) -> VOr (trans_f state f1, trans_f state f2)
  | VBinRel (brel,e1,e2) -> VBinRel (brel, trans_e state e1, trans_e state e2)
  | Imply (f1,f2) -> Imply (trans_f state f1, trans_f state f2)
  | SigmaEqual _ | NoOverFlow _ | UntrustSum _ | UntrustSum2 _ -> vf
  | ForAll (bvs,f) -> vf
  | Label (l,f) -> Label (l, trans_f state f)

and trans_e : vformula -> vexp -> vexp
= fun state ve ->
  match ve with
  | VInt _ | VVar _ -> ve
  | Read (e1,e2) -> Read (trans_e state e1, trans_e state e2)
  | Write (e1,e2,e3) -> Write (trans_e state e1, trans_e state e2, trans_e state e3)

  | VBinOp (vbop,e1,VInt n,typ) when (vbop = VMul || vbop = VDiv) && BatBig_int.equal n BatBig_int.zero ->
    VBinOp (vbop, trans_e state e1, VInt n, typ)

  | VBinOp (vbop,e1,e2,typ) when vbop = VMul || vbop = VDiv ->
    let vars1,vars2 = free_ve e1, free_ve e2 in
    let b1, b2  = BatSet.for_all (constrained state) vars1, BatSet.for_all (constrained state) vars2 in
    let worth = b1 && b2 in
    if worth then
      VBinOp (vbop, trans_e state e1, trans_e state e2, typ) (* should recurse, e.g., it may contain power operation *)
    else
      let fname = match vbop with VMul -> "umul" | VDiv -> "udiv" | _ -> assert false in
      Uninterp (fname, [trans_e state e1; trans_e state e2], typ)

  | VBinOp (VMod,e1,e2,typ) -> Uninterp ("umod", [e1;e2], typ)
  | VBinOp (VPower,e1,e2,typ) -> Uninterp ("upower", [e1;e2], typ)
  | VBinOp (bop,e1,e2,typ) -> VBinOp (bop, trans_e state e1, trans_e state e2, typ)
  | VUnOp (uop,e,typ) -> VUnOp (uop, trans_e state e, typ)
  | VCast (t,e) -> VCast (t, trans_e state e)
  | VCond f -> VCond (trans_f state f)
  | Ite (e1,e2,e3) -> Ite (trans_e state e1, trans_e state e2, trans_e state e3)
  | Uninterp (fname,args,typ) -> Uninterp (fname, List.map (trans_e state) args, typ)

let transform : vformula -> vformula
= fun vf ->
  let _ = assert (!Options.mode = "verify") in
  let (state,sc) = split_implication vf in
  trans_f state vf
