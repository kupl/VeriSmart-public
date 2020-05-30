open Lang
open Vlang
open Simplification
open Semantics

let freshid = ref 0
let freshvar () = freshid:=!freshid+1; ("tmp" ^ (string_of_int !freshid))

let ctx = ref (Z3.mk_context [])

let rec typ_to_sort : typ -> Z3.Sort.sort
= fun typ ->
  match typ with
  | ConstInt -> Z3.Arithmetic.Integer.mk_sort !ctx
  | ConstString -> Z3.Sort.mk_uninterpreted_s !ctx "Uninterpreted-ConstStringSort"
  | ConstReal -> raise (Failure "typ_to_sort: translation for ConstReal type is not supported")
  | EType etyp -> etyp_to_sort etyp
  | Mapping (e,t) -> Z3.Z3Array.mk_sort !ctx (etyp_to_sort e) (typ_to_sort t)
  | Mapping2 (t1,t2) -> Z3.Z3Array.mk_sort !ctx (typ_to_sort t1) (typ_to_sort t2)
  | Array (t,eop) -> Z3.Z3Array.mk_sort !ctx (Z3.BitVector.mk_sort !ctx 256) (typ_to_sort t)
  | Contract s -> Z3.BitVector.mk_sort !ctx 160
  | Struct s -> Z3.Sort.mk_uninterpreted_s !ctx s
  | Enum s -> Z3.BitVector.mk_sort !ctx 256
  | TupleType _ -> raise (Failure "typ_to_sort: tuple types are not queried as a whole.")
  | Void -> raise (Failure "typ_to_sort: Void")

and etyp_to_sort : elem_typ -> Z3.Sort.sort
= fun etyp ->
  match etyp with
  | Address -> Z3.BitVector.mk_sort !ctx 160
  | Bool -> Z3.Boolean.mk_sort !ctx 
  | String -> Z3.Sort.mk_uninterpreted_s !ctx "Uninterpreted-StringSort"
  | UInt n -> Z3.BitVector.mk_sort !ctx n
  | SInt n -> Z3.BitVector.mk_sort !ctx n
  | Bytes n ->
    let domain_bit = if !Options.bit > 0 then !Options.bit else 256 in
    if n=1 then Z3.Sort.mk_uninterpreted_s !ctx "Uninterpreted"
    else Z3.Z3Array.mk_sort !ctx (Z3.BitVector.mk_sort !ctx domain_bit) (Z3.Sort.mk_uninterpreted_s !ctx "Uninterpreted")
  | DBytes ->
    let domain_bit = if !Options.bit > 0 then !Options.bit else 256 in
    Z3.Z3Array.mk_sort !ctx (Z3.BitVector.mk_sort !ctx domain_bit) (Z3.Sort.mk_uninterpreted_s !ctx "Uninterpreted")

let convert : typ -> typ -> Z3.Expr.expr -> Z3.Expr.expr
= fun my_typ comp_typ z3exp ->
  if my_typ = comp_typ then z3exp
  else
   (match my_typ, comp_typ with
    | ConstInt, EType (UInt n) -> Z3.Arithmetic.Integer.mk_int2bv !ctx n z3exp
    | ConstInt, EType (SInt n) -> Z3.Arithmetic.Integer.mk_int2bv !ctx n z3exp
    | EType (UInt n1), EType (UInt n2) when n1<n2 -> Z3.BitVector.mk_zero_ext !ctx (n2-n1) z3exp
    | EType (SInt n1), EType (SInt n2) when n1<n2 -> Z3.BitVector.mk_sign_ext !ctx (n2-n1) z3exp
    | EType (UInt n1), EType (SInt n2) when n1<=n2 -> Z3.BitVector.mk_sign_ext !ctx (n2-n1) z3exp
    | EType (SInt n1), EType (UInt n2) when n1<=n2 -> Z3.BitVector.mk_zero_ext !ctx (n2-n1) z3exp
    | ConstInt, EType Address -> Z3.Arithmetic.Integer.mk_int2bv !ctx 160 z3exp
    | ConstInt, EType (Bytes _) -> Z3.Expr.mk_fresh_const !ctx (freshvar ()) (typ_to_sort comp_typ)
    | EType (UInt n1), EType (UInt n2) when n1>n2 -> Z3.BitVector.mk_extract !ctx (n2-1) 0 z3exp
    | EType (Bytes n1), EType (UInt n2) when n1*8<=n2 ->
      Z3.BitVector.mk_const_s !ctx (Z3.Expr.to_string z3exp ^ "_Symbol") n2 
    | EType Address, Contract s ->
      Z3.Expr.mk_fresh_const !ctx (freshvar ()) (typ_to_sort comp_typ)
    | Contract s, EType Address ->
      let str = Z3.Expr.to_string z3exp in
      if BatString.equal str "this" then
        Z3.BitVector.mk_const_s !ctx (fst this_addr) 160
      else Z3.BitVector.mk_const_s !ctx str 160
    | EType (Bytes n1), EType (Bytes n2) -> Z3.Expr.mk_fresh_const !ctx (freshvar ()) (typ_to_sort comp_typ)
    | ConstInt, Contract s -> Z3.Expr.mk_fresh_const !ctx (freshvar ()) (typ_to_sort comp_typ)
    | EType Address, EType (UInt n) -> Z3.BitVector.mk_const_s !ctx (Z3.Expr.to_string z3exp) n
    | Enum _, EType (UInt n) ->
      (* enum is interpreted as unsigned 256-bit exps. *)
      if n < 256 then Z3.BitVector.mk_extract !ctx (n-1) 0 z3exp
      else z3exp
    | ConstInt, Enum _ -> Z3.Arithmetic.Integer.mk_int2bv !ctx 256 z3exp
    | ConstString, EType DBytes
    | EType String, EType DBytes -> Z3.Expr.mk_fresh_const !ctx (freshvar ()) (typ_to_sort comp_typ)
    | EType DBytes, EType String -> Z3.Expr.mk_fresh_const !ctx (freshvar ()) (typ_to_sort comp_typ)
    | ConstString, EType (Bytes _) -> Z3.Expr.mk_fresh_const !ctx (freshvar ()) (typ_to_sort comp_typ)
    | EType (UInt n1), EType (Bytes n2) -> Z3.Expr.mk_fresh_const !ctx (freshvar ()) (typ_to_sort comp_typ)
    | Array (t1,Some n), Array (t2,None) when t1=t2 -> z3exp
    | Contract id, EType (UInt n) -> Z3.Expr.mk_fresh_const !ctx (freshvar ()) (typ_to_sort comp_typ)
    | Contract id1, Contract id2 -> Z3.Expr.mk_fresh_const !ctx (freshvar ()) (typ_to_sort comp_typ)
    | EType (UInt n), EType Address -> Z3.Expr.mk_fresh_const !ctx (freshvar ()) (typ_to_sort comp_typ)
    | _ -> Z3.Expr.mk_fresh_const !ctx (freshvar ()) (typ_to_sort comp_typ)) (* for unknown cases, simply assign fresh variables *)

let rec vformula_to_z3exp : vformula -> Z3.Expr.expr
= fun vf ->
  match vf with
  | VTrue -> Z3.Boolean.mk_true !ctx
  | VFalse -> Z3.Boolean.mk_false !ctx
  | VNot f -> Z3.Boolean.mk_not !ctx (vformula_to_z3exp f)
  | VAnd (f1,f2) -> Z3.Boolean.mk_and !ctx [vformula_to_z3exp f1; vformula_to_z3exp f2]
  | VOr (f1,f2) -> Z3.Boolean.mk_or !ctx [vformula_to_z3exp f1; vformula_to_z3exp f2]
  | VBinRel (vbrel,ve1,ve2) ->
    let z3exp1 = vexp_to_z3exp ve1 in
    let z3exp2 = vexp_to_z3exp ve2 in
    (match vbrel with
     | VGeq -> Z3.BitVector.mk_uge !ctx z3exp1 z3exp2
     | VGt  -> Z3.BitVector.mk_ugt !ctx z3exp1 z3exp2 
     | VEq  -> Z3.Boolean.mk_eq !ctx z3exp1 z3exp2)
  | Imply (f1,f2) -> Z3.Boolean.mk_implies !ctx (vformula_to_z3exp f1) (vformula_to_z3exp f2)
  | SigmaEqual _ -> raise (Failure "z3interface: SigmaEqual")
  | NoOverFlow _ -> raise (Failure "z3interface: NoOverFlow")
  | ForAll (vars,f) ->
    let bound_vars = List.map (fun (x,t) -> vexp_to_z3exp (VVar (x,t))) vars in
    let body = vformula_to_z3exp f in
    Z3.Quantifier.expr_of_quantifier (Z3.Quantifier.mk_forall_const !ctx bound_vars body None [] [] None None)
  | Label _ -> raise (Failure "z3interface: Label")

and vexp_to_z3exp : vexp -> Z3.Expr.expr
= fun vexp ->
  match vexp with
  | VInt n -> Z3.Arithmetic.Integer.mk_numeral_s !ctx (BatBig_int.to_string n)
  | VVar (vid,typ) ->
    Z3.Expr.mk_const_s !ctx vid (typ_to_sort typ)
  | Read (ve1,ve2,_) ->
    let z3exp1 = vexp_to_z3exp ve1 in
    let z3exp2 = vexp_to_z3exp ve2 in
    Z3.Z3Array.mk_select !ctx z3exp1 z3exp2
  | Write (ve1,ve2,ve3) ->
    let z3exp1 = vexp_to_z3exp ve1 in
    let z3exp2 = vexp_to_z3exp ve2 in
    let z3exp3 = vexp_to_z3exp ve3 in
    Z3.Z3Array.mk_store !ctx z3exp1 z3exp2 z3exp3
  | VBinOp (vbop,ve1,ve2,typ) ->
    let z3exp1 = vexp_to_z3exp ve1 in
    let z3exp2 = vexp_to_z3exp ve2 in
    (match vbop with
     | VAdd -> Z3.BitVector.mk_add !ctx z3exp1 z3exp2 
     | VSub -> Z3.BitVector.mk_sub !ctx z3exp1 z3exp2 
     | VMul -> Z3.BitVector.mk_mul !ctx z3exp1 z3exp2
     | VDiv -> Z3.BitVector.mk_udiv !ctx z3exp1 z3exp2
     | VMod -> Z3.BitVector.mk_urem !ctx z3exp1 z3exp2
     | VPower -> failwith "z3interface : VPower encountered"
     | VShiftL -> Z3.BitVector.mk_shl !ctx z3exp1 z3exp2
     | VShiftR -> Z3.BitVector.mk_lshr !ctx z3exp1 z3exp2 
     | VBXor -> Z3.BitVector.mk_xor !ctx z3exp1 z3exp2
     | VBAnd -> Z3.BitVector.mk_and !ctx z3exp1 z3exp2
     | VBOr -> Z3.BitVector.mk_or !ctx z3exp1 z3exp2)
  | VUnOp (vuop,ve,typ) ->
    let z3exp = vexp_to_z3exp ve in
    (match vuop with
     | VNeg -> Z3.BitVector.mk_neg !ctx z3exp
     | VBNot -> Z3.BitVector.mk_not !ctx z3exp)
  | VCast (typ,ve) -> 
    let typ_ve = get_type_vexp ve in
    convert typ_ve typ (vexp_to_z3exp ve)
  | VCond vf -> vformula_to_z3exp vf
  | Ite (ve1,ve2,ve3) -> Z3.Boolean.mk_ite !ctx (vexp_to_z3exp ve1) (vexp_to_z3exp ve2) (vexp_to_z3exp ve3)

(* constant folding *)
let rec fold_vf : vformula -> vformula
= fun vf ->
  match vf with
  | VTrue | VFalse -> vf
  | VNot f -> VNot (fold_vf f)
  | VAnd (f1,f2) -> VAnd (fold_vf f1, fold_vf f2)
  | VOr (f1,f2) -> VOr (fold_vf f1, fold_vf f2)
  | VBinRel (VGeq, VInt n1, VInt n2) -> if BatBig_int.ge_big_int n1 n2 then VTrue else VFalse
  | VBinRel (VGt, VInt n1, VInt n2) -> if BatBig_int.gt_big_int n1 n2 then VTrue else VFalse
  | VBinRel (VEq, VInt n1, VInt n2) -> if BatBig_int.eq_big_int n1 n2 then VTrue else VFalse
  | VBinRel (rel,e1,e2) -> VBinRel (rel, fold_ve e1, fold_ve e2) 
  | Imply (f1,f2) -> Imply (fold_vf f1, fold_vf f2)
  | SigmaEqual _ | NoOverFlow _ -> failwith "fold_vf" 
  | ForAll (vars,f) -> ForAll (vars, fold_vf f)
  | Label (l,f) -> Label (l, fold_vf f)

and fold_ve : vexp -> vexp
= fun ve ->
  match ve with
  | VInt _ | VVar _ -> ve
  | Read (e1,e2,t) -> Read (fold_ve e1, fold_ve e2, t)
  | Write (e1,e2,e3) -> Write (fold_ve e1, fold_ve e2, fold_ve e3)
  | VBinOp (VAdd,VInt n1,VInt n2,typ) -> VInt (BatBig_int.add n1 n2)
  | VBinOp (VSub,VInt n1,VInt n2,typ) -> VInt (BatBig_int.sub n1 n2)
  | VBinOp (VMul,VInt n1,VInt n2,typ) -> VInt (BatBig_int.mul n1 n2)
  | VBinOp (VDiv,VInt n1,VInt n2,typ) -> VInt (BatBig_int.div n1 n2)
  | VBinOp (VMod,VInt n1,VInt n2,typ) -> VInt (BatBig_int.modulo n1 n2)
  | VBinOp (VPower,VInt n1,VInt n2,typ) -> VInt (BatBig_int.pow n1 n2)
  | VBinOp (VShiftL,VInt n1,VInt n2,typ) -> VInt (BatBig_int.shift_left_big_int n1 (BatBig_int.to_int n2))
  | VBinOp (VShiftR,VInt n1,VInt n2,typ) -> VInt (BatBig_int.shift_right_big_int n1 (BatBig_int.to_int n2))
  | VBinOp (VBXor,VInt n1,VInt n2,typ) -> VInt (BatBig_int.xor_big_int n1 n2)
  | VBinOp (VBAnd,VInt n1,VInt n2,typ) -> VInt (BatBig_int.and_big_int n1 n2)
  | VBinOp (VBOr,VInt n1,VInt n2,typ) -> VInt (BatBig_int.or_big_int n1 n2)
  | VBinOp (op,e1,e2,t) -> VBinOp (op, fold_ve e1, fold_ve e2, t)
  | VUnOp (uop,e,t) -> VUnOp (uop, fold_ve e, t)
  | VCast (t,e) -> VCast (t, fold_ve e)
  | VCond f -> VCond (fold_vf f) 
  | Ite (e1,e2,e3) -> Ite (fold_ve e1, fold_ve e2, fold_ve e3)

let rec constant_folding : vformula -> vformula
= fun vf ->
  let vf' = fold_vf vf in 
  if equal_vf vf vf' then vf'
  else constant_folding vf'

let common_typ : vexp -> vexp -> typ
= fun e1 e2 ->
  let t1,t2 = get_type_vexp e1, get_type_vexp e2 in
  if t1=t2 then t1
  else
   (match t1,t2 with
    | ConstInt, EType (UInt n) ->
      let n' = bit_unsigned_of_int (get_bigint_v e1) 8 in
      EType (UInt (max n n'))
    | EType (UInt n), ConstInt ->
      let n' = bit_unsigned_of_int (get_bigint_v e2) 8 in
      EType (UInt (max n n'))
    | ConstInt, EType (SInt n) ->
      let n' = bit_signed_of_int (get_bigint_v e1) 8 in
      EType (SInt (max n n'))
    | EType (SInt n), ConstInt ->
      let n' = bit_signed_of_int (get_bigint_v e2) 8 in
      EType (SInt (max n n'))
    | _ -> preceding_typ t1 t2)

let rec cast_vf vf =
  match vf with
  | VTrue | VFalse -> vf
  | VNot f -> VNot (cast_vf f)
  | VAnd (f1,f2) -> VAnd (cast_vf f1, cast_vf f2)
  | VOr (f1,f2) -> VOr (cast_vf f1, cast_vf f2)
  | VBinRel (vbrel,e1,e2) ->
    let t1,t2 = get_type_vexp e1, get_type_vexp e2 in
    let ctyp = common_typ e1 e2 in
    let e1' = if t1 = ctyp then cast_ve e1 else VCast (ctyp, cast_ve e1) in
    let e2' = if t2 = ctyp then cast_ve e2 else VCast (ctyp, cast_ve e2) in
    VBinRel (vbrel,e1',e2')
  | Imply (f1,f2) -> Imply (cast_vf f1, cast_vf f2) 
  | SigmaEqual _ -> failwith "cast_vf : SigmaEqual"
  | NoOverFlow _ -> failwith "cast_vf : NoOverFlow"
  | ForAll (vars,f) -> ForAll (vars, cast_vf f)
  | Label _ -> failwith "cast_vf : Label"

and cast_ve ve =
  match ve with
  | VInt _ | VVar _ -> ve
  | Read (e1,e2,typ) ->
    let expected_idx_typ = domain_typ (get_type_vexp e1) in
    let idx_typ = get_type_vexp e2 in
    let e1' = cast_ve e1 in
    let e2' = if expected_idx_typ = idx_typ then cast_ve e2 else VCast (expected_idx_typ, cast_ve e2) in
    Read (e1',e2',typ)
  | Write (e1,e2,e3) ->
    let expected_range_typ = range_typ (get_type_vexp e1) in
    let range_typ = get_type_vexp e3 in
    let expected_idx_typ = domain_typ (get_type_vexp e1) in
    let idx_typ = get_type_vexp e2 in
    let e1' = cast_ve e1 in
    let e2' = if expected_idx_typ = idx_typ then cast_ve e2 else VCast (expected_idx_typ, cast_ve e2) in
    let e3' = if expected_range_typ = range_typ then cast_ve e3 else VCast (expected_range_typ, cast_ve e3) in
    Write (e1',e2',e3')
  | VBinOp (vbop,e1,e2,t) ->
    let t1 = get_type_vexp e1 in
    let t2 = get_type_vexp e2 in
    let ctyp = common_typ e1 e2 in
    let _ = assert (t = ctyp) in
    let e1' = if t1 = ctyp then cast_ve e1 else VCast (ctyp, cast_ve e1) in
    let e2' = if t2 = ctyp then cast_ve e2 else VCast (ctyp, cast_ve e2) in
    VBinOp (vbop,e1',e2',t)
  | VUnOp (VBNot, VInt n, ConstInt) -> (* the syntax is allowed in solc, but needs casting. *)
    if BatBig_int.ge_big_int n BatBig_int.zero then
      let bit = bit_unsigned_of_int (get_bigint_v (VInt n)) 8 in
      VUnOp (VBNot, VCast (EType (UInt bit), VInt n), EType (UInt bit))
    else
      let bit = bit_signed_of_int (get_bigint_v (VInt n)) 8 in
      VUnOp (VBNot, VCast (EType (SInt bit), VInt n), EType (SInt bit))
  | VUnOp (vuop,e,t) -> VUnOp (vuop, cast_ve e, t)
  | VCast (t,e) -> VCast (t, cast_ve e)
  | VCond f -> VCond (cast_vf f) 
  | Ite (e1,e2,e3) -> Ite (cast_ve e1, cast_ve e2, cast_ve e3)

(****************************)
(*** Reestrict bit number ***)
(****************************)

let rec change_typ : int -> typ -> typ
= fun bit typ ->
  match typ with
  | ConstInt | ConstString | ConstReal -> typ
  | EType et -> EType (change_etyp bit et)
  | Mapping (et,t) -> Mapping (change_etyp bit et, change_typ bit t)
  | Mapping2 (t1,t2) -> Mapping2 (change_typ bit t1, change_typ bit t2)
  | Array (t,op) -> Mapping (change_etyp bit (UInt 256), change_typ bit t)
    (* Array (change_typ bit t, op) *)
  | Contract _ | Struct _ | Enum _ -> typ
  | TupleType lst -> TupleType (List.map (change_typ bit) lst)
  | Void -> typ

and change_etyp : int -> elem_typ -> elem_typ
= fun bit etyp ->
  match etyp with
  | Address | Bool | String -> etyp
  | UInt n -> if n=256 then UInt bit else UInt n
  | SInt n -> if n=256 then SInt bit else SInt n
  | Bytes n -> etyp
  | DBytes -> etyp

(* bit restriction *)
let rec rest_vf : int -> vformula -> vformula
= fun bit vf ->
  match vf with
  | VTrue | VFalse -> vf
  | VNot f -> VNot (rest_vf bit f)
  | VAnd (f1,f2) -> VAnd (rest_vf bit f1, rest_vf bit f2)
  | VOr (f1,f2) -> VOr (rest_vf bit f1, rest_vf bit f2)
  | VBinRel (rel,e1,e2) -> VBinRel (rel, rest_ve bit e1, rest_ve bit e2)
  | Imply (f1,f2) -> Imply (rest_vf bit f1, rest_vf bit f2)
  | SigmaEqual (e,(x,t)) -> SigmaEqual (rest_ve bit e, (x, change_typ bit t))
  | NoOverFlow (x,t) -> NoOverFlow (x, change_typ bit t)
  | ForAll (lst,f) ->
    let lst' = List.map (fun (x,t) -> (x,change_typ bit t)) lst in
    ForAll (lst', rest_vf bit f)
  | Label (l,f) -> Label (l, rest_vf bit f)

and rest_ve : int -> vexp -> vexp
= fun bit ve ->
  match ve with
  | VInt _ -> ve
  | VVar (x,t) -> VVar (x, change_typ bit t)
  | Read (e1,e2,t) -> Read (rest_ve bit e1, rest_ve bit e2, change_typ bit t) 
  | Write (e1,e2,e3) -> Write (rest_ve bit e1, rest_ve bit e2, rest_ve bit e3)
  | VBinOp (bop,e1,e2,t) -> VBinOp (bop, rest_ve bit e1, rest_ve bit e2, change_typ bit t)
  | VUnOp (uop,e,t) -> VUnOp (uop, rest_ve bit e, change_typ bit t)
  | VCast (t,e) -> VCast (change_typ bit t, rest_ve bit e)
  | VCond f -> VCond (rest_vf bit f)
  | Ite (e1,e2,e3) -> Ite (rest_ve bit e1, rest_ve bit e2, rest_ve bit e3)

let restrict_bit : int -> vformula -> vformula
= fun bit vf -> rest_vf bit vf

let is_unsat : vformula -> bool * Z3.Model.model option
= fun vf ->
  let vf = constant_folding vf in
  let vf = cast_vf vf in
  let z3formula = vformula_to_z3exp vf in
  let solver = Z3.Solver.mk_solver !ctx None in
  let _ = Z3.Solver.add solver [z3formula] in
    (match Z3.Solver.check solver [] with
    | UNSATISFIABLE -> (true,None)
    | SATISFIABLE ->
      (match Z3.Solver.get_model solver with
       | Some m -> (false, Some m)
       | _ -> raise (Failure "never happen"))
    | UNKNOWN -> (false,None)) (* say 'yes' only when UNSAT is certain *)

(* @ret 0: UNSAT
 * @ret 1: SAT 
 * @ret 2: UNKNOWN *)
let is_sat : vformula -> int * Z3.Model.model option
= fun vf ->
  let vf = constant_folding vf in
  let vf = cast_vf vf in
  let vf = if !Options.bit > 0 then restrict_bit !Options.bit vf else vf in
  let z3formula = vformula_to_z3exp vf in
  let solver = Z3.Solver.mk_solver !ctx None in
  let _ = Z3.Solver.add solver [z3formula] in
    (match Z3.Solver.check solver [] with
    | UNSATISFIABLE -> (0,None)
    | SATISFIABLE ->
      (match Z3.Solver.get_model solver with
       | Some m -> (1, Some m)
       | _ -> raise (Failure "never happen"))
    | UNKNOWN -> (2, None))

let is_valid : vformula -> bool * Z3.Model.model option
= fun vf -> is_unsat (VNot vf)
