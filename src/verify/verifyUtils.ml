open Lang
open Vlang
open Simplification

let rec contain_lock : vformula -> bool
= fun vf ->
  match vf with
  | VBinRel (VEq,VVar _,VCond VTrue)
  | VBinRel (VEq,VVar _,VCond VFalse) -> true
  | VAnd (f1,f2) -> contain_lock f1 || contain_lock f2
  | VOr _ | Imply _ -> assert false
  | _ -> false

let rec contain_given_lock : var -> vformula -> bool
= fun var vf ->
  match vf with
  | VBinRel (VEq,VVar x,VCond VTrue)
  | VBinRel (VEq,VVar x,VCond VFalse) -> x = var
  | VAnd (f1,f2) -> contain_given_lock var f1 || contain_given_lock var f2
  | VOr _ | Imply _ -> assert false
  | _ -> false

let rec contain_lock_s : vformula -> stmt -> bool
= fun vf stmt ->
  match stmt with
  | Assign (Var (v,vinfo),_,_) when is_bool vinfo.vtyp -> contain_given_lock (v,vinfo.vtyp) vf
  | Seq (s1,s2) -> contain_lock_s vf s1 || contain_lock_s vf s2
  | If (_,_,_,_) | While (_,_) -> false
  | _ -> false

let rec has_mul_div_f : vformula -> bool
= fun vf ->
  match vf with
  | VTrue | VFalse -> false
  | VNot f -> has_mul_div_f f
  | VAnd (f1,f2) -> has_mul_div_f f1 || has_mul_div_f f2
  | VOr (f1,f2) -> has_mul_div_f f1 || has_mul_div_f f2
  | VBinRel (_,e1,e2) -> has_mul_div_e e1 || has_mul_div_e e2
  | Imply (f1,f2) -> has_mul_div_f f1 || has_mul_div_f f2
  | SigmaEqual _ | NoOverFlow _ | UntrustSum _ | UntrustSum2 _ -> false (* assert false *)
  | ForAll (_,f) -> has_mul_div_f f
  | Label (_,f) -> has_mul_div_f f (* assert false *)

and has_mul_div_e : vexp -> bool
= fun ve ->
  match ve with
  | VInt _ | VVar _ -> false
  | Read (e1,e2) -> has_mul_div_e e1 || has_mul_div_e e2
  | Write (e1,e2,e3) -> has_mul_div_e e1 || has_mul_div_e e2 || has_mul_div_e e3
  | VBinOp (vbop,e1,e2,_) -> vbop=VMul || vbop=VDiv || has_mul_div_e e1 || has_mul_div_e e2
  | VUnOp (_,e,_) -> has_mul_div_e e
  | VCast (_,e) -> has_mul_div_e e
  | VCond f -> has_mul_div_f f
  | Ite (e1,e2,e3) -> has_mul_div_e e1 || has_mul_div_e e2 || has_mul_div_e e3
  | Uninterp (_,args,_) -> List.fold_left (fun acc e' -> has_mul_div_e e' || acc) false args

let rec include_or : vformula -> bool
= fun vf ->
  match vf with
  | VTrue | VFalse -> false
  | VNot f -> include_or f
  | VAnd (f1,f2) -> include_or f1 || include_or f2
  | VOr (f1,f2) -> true
  | VBinRel (_,e1,e2) -> false
  | Imply _ -> true (* this case may exist, e.g., NoOverflow *)
  | SigmaEqual _ | NoOverFlow _ | UntrustSum _ | UntrustSum2 _ -> assert false
  | ForAll (_,f) -> include_or f
  | Label _ -> assert false

(* to preserve precision as possible, perform invalidity checking in a restrictive manner. *)
let is_complex : vformula -> bool
= fun vf ->
  match vf with
    (* A == 0 \/ (A!=0 /\ (A * B / A) == B) *)
    (* e1         e2       e3  e4  e5    e6 *)
  | VOr (VBinRel (VEq,e1,VInt n1),
         VAnd (VNot (VBinRel (VEq,e2,VInt n2)), VBinRel (VEq, VBinOp (VDiv, (VBinOp (VMul,e3,e4,t)),e5,t'), e6))) ->
    BatBig_int.equal n1 BatBig_int.zero && BatBig_int.equal n2 BatBig_int.zero &&
    equal_ve e1 e2 && equal_ve e2 e3 && equal_ve e3 e5 && equal_ve e4 e6
  | _ -> false

let is_invalid_approx : vformula -> bool
= fun vf ->
  match vf with
  | Imply (pre,con) when is_complex con ->
    if not (BatSet.subset (free_vf con) (free_vf pre))
      then true (* conjectures that the query may not be provable *)
    else false
  | Imply _ -> false (* if 'con' is not that complicated, invoke z3 to preserve precision as possible *)
  | VFalse -> false
  | _ -> assert false

let property_focused_simplification : vformula -> vformula
= fun vf ->
  let (pre,con) = split_implication vf in
  let dep_vars = Opt.compute_dependant_vars pre con in
  let pre' = Opt.remove_unrelated_part dep_vars pre in
  Imply (pre',con)

let is_valid_wrapper : vformula -> bool * Z3.Model.model option
= fun vf ->
  let vf = property_focused_simplification vf in
  let vf = Simplification.remove_pow vf in
  (* let vf = Simplification.fix (fun vf -> vf |> normalize |> propagate_eq) vf in *)
  let vf = vf |> normalize |> propagate_eq |> normalize |> propagate_eq in
  let vf = vf |> normalize |> propagate_eq |> normalize in (* To ensure termination. Also, the last step is normalization (e.g., cannot be applied to udiv) *)
  let vf = Tactic.apply vf in
  let b = try Template.valid_template vf with Stack_overflow -> false in
  if b then (true,None)
  else
    let vf = TransformPredicate.transform vf in (* special predicates are transformed in here *)
    if is_invalid_approx vf then (false,None)
    else
      let vf = TransNonLinear.transform vf in
      Z3Interface.is_valid vf
