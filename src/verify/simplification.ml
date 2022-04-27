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
  | VAnd (VBinRel (VEq,e1,VCond VTrue), VBinRel(VEq,e2,VCond VFalse)) -> VFalse
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
  | VOr (VBinRel (VEq,e1,VInt n1),
         VAnd (VNot (VBinRel (VEq,e2,VInt n2)), VBinRel (VEq, VBinOp (VDiv, (VBinOp (VMul,e3,VCast(EType (UInt 256), VInt n3),t)),e4,t'), VCast (EType (UInt 256), VInt n4))))
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
  | VBinRel (VEq, VCond (VBinRel (rel,e1,e2)), VCond VTrue) -> VBinRel (rel,e1,e2)
  | VBinRel (VEq, VCond VTrue, VCond (VBinRel (rel,e1,e2))) -> VBinRel (rel,e1,e2)
  | VBinRel (VEq, VCond VFalse, VCond VTrue) -> VFalse
  | VBinRel (VEq,VCond VTrue,VCond VFalse) -> VFalse
  | VBinRel (VGt, VInt n1, VInt n2) -> if BatBig_int.gt_big_int n1 n2 then VTrue else VFalse
  | VBinRel (VGt,e1,e2) when equal_ve e1 e2 -> VFalse
  | VBinRel (VGeq, VInt n1, VInt n2) -> if BatBig_int.ge_big_int n1 n2 then VTrue else VFalse
  | VBinRel (VGeq,e1,e2) when equal_ve e1 e2 -> VTrue
  | VBinRel (VGeq, VInt n, VVar (x,t)) when is_uintkind t && BatBig_int.sign_big_int n = 0 -> VBinRel (VEq, VVar (x,t), VInt n)
  | VBinRel (VGeq, VVar (x,EType (UInt 8)), VInt n)
    when BatBig_int.sign_big_int (BatBig_int.modulo n (BatBig_int.of_int 256)) = 0 -> VTrue 
  | VBinRel (VGeq, VVar (_,t), VInt n) when is_uintkind t && BatBig_int.sign_big_int n = 0 -> VTrue
  | VBinRel (rel,e1,e2) -> VBinRel (rel, norm_ve e1, norm_ve e2)
  | Imply (f1,f2) -> Imply (norm_vf f1, norm_vf f2)
  | SigmaEqual _ | NoOverFlow _ | UntrustSum _ | UntrustSum2 _ -> vf
  | ForAll (vars,f) -> ForAll (vars, norm_vf f)
  | Label (_,f) -> norm_vf f

and norm_ve : vexp -> vexp
= fun ve ->
  match ve with
  | VInt _ | VVar _ -> ve
  | Read (e1,e2) -> Read (norm_ve e1, norm_ve e2)
  | Write (e1,e2,e3) -> Write (norm_ve e1, norm_ve e2, norm_ve e3)

  (* constant folding *)
  | VBinOp (VAdd,VInt n1,VInt n2,ConstInt) -> VInt (BatBig_int.add n1 n2)
  | VBinOp (VAdd,VInt n1,VInt n2,typ) -> VCast (typ, VInt (BatBig_int.add n1 n2))
  | VBinOp (VSub,VInt n1,VInt n2,ConstInt) -> VInt (BatBig_int.sub n1 n2)
  | VBinOp (VSub,VInt n1,VInt n2,typ) -> VCast (typ, VInt (BatBig_int.sub n1 n2))
  | VBinOp (VMul,VInt n1,VInt n2,ConstInt) -> VInt (BatBig_int.mul n1 n2)
  | VBinOp (VMul,VInt n1,VInt n2,typ) -> VCast (typ, VInt (BatBig_int.mul n1 n2))
  | VBinOp (VDiv,VInt n1,VInt n2,ConstInt) -> VInt (BatBig_int.div n1 n2)
  | VBinOp (VDiv,VInt n1,VInt n2,typ) -> VCast (typ, VInt (BatBig_int.div n1 n2))
  | VBinOp (VMod,VInt n1,VInt n2,ConstInt) -> VInt (BatBig_int.modulo n1 n2)
  | VBinOp (VMod,VInt n1,VInt n2,typ) -> VCast (typ, VInt (BatBig_int.modulo n1 n2))
  | VBinOp (VPower,VInt n1,VInt n2,ConstInt) -> VInt (BatBig_int.pow n1 n2)
  | VBinOp (VPower,VInt n1,VInt n2,typ) -> VCast (typ, VInt (BatBig_int.pow n1 n2))
  | VBinOp (VShiftL,VInt n1,VInt n2,ConstInt) -> VInt (BatBig_int.shift_left_big_int n1 (BatBig_int.to_int n2))
  | VBinOp (VShiftL,VInt n1,VInt n2,typ) -> VCast (typ, VInt (BatBig_int.shift_left_big_int n1 (BatBig_int.to_int n2)))
  | VBinOp (VShiftR,VInt n1,VInt n2,ConstInt) -> VInt (BatBig_int.shift_right_big_int n1 (BatBig_int.to_int n2))
  | VBinOp (VShiftR,VInt n1,VInt n2,typ) -> VCast (typ, VInt (BatBig_int.shift_right_big_int n1 (BatBig_int.to_int n2)))
  | VBinOp (VBXor,VInt n1,VInt n2,ConstInt) -> VInt (BatBig_int.xor_big_int n1 n2)
  | VBinOp (VBXor,VInt n1,VInt n2,typ) -> VCast (typ, VInt (BatBig_int.xor_big_int n1 n2))
  | VBinOp (VBAnd,VInt n1,VInt n2,ConstInt) -> VInt (BatBig_int.and_big_int n1 n2)
  | VBinOp (VBAnd,VInt n1,VInt n2,typ) -> VCast (typ, VInt (BatBig_int.and_big_int n1 n2))
  | VBinOp (VBOr,VInt n1,VInt n2,ConstInt) -> VInt (BatBig_int.or_big_int n1 n2)
  | VBinOp (VBOr,VInt n1,VInt n2,typ) -> VCast (typ, VInt (BatBig_int.or_big_int n1 n2))

  | VBinOp (bop,e1,e2,t) -> VBinOp (bop, norm_ve e1, norm_ve e2, t)
  | VUnOp (VNeg,VInt n,ConstInt) -> VInt (BatBig_int.neg n)
  | VUnOp (uop,e,t) -> VUnOp (uop, norm_ve e, t)
  | VCast(t,e) when t = get_typ_vexp e -> (* E.g., uint(uint(n)) => uint, int_const(100) => 100 *)
    norm_ve e
  | VCast (t,e) -> VCast (t, norm_ve e)
  | VCond f -> VCond (norm_vf f)
  | Ite (e1,e2,e3) -> Ite (norm_ve e1, norm_ve e2, norm_ve e3)
  | Uninterp (fname,args,t) -> Uninterp (fname, List.map norm_ve args, t)

let normalize vf = norm_vf vf

(* assume input is conjunctive invariant *)
let rec vf_to_set : vformula -> FormulaSet.t
= fun vf ->
  match vf with
  | VTrue | VFalse -> FormulaSet.singleton vf
  | VAnd (f1,f2) -> FormulaSet.union (vf_to_set f1) (vf_to_set f2)
  | VBinRel _ -> FormulaSet.singleton vf
  | SigmaEqual _ | NoOverFlow _ | UntrustSum _ | UntrustSum2 _ -> FormulaSet.singleton vf
  | VNot _ -> FormulaSet.singleton vf
  | VOr _ -> FormulaSet.singleton vf
  | Imply _ -> raise (Failure "vf_to_set : Imply")
  | ForAll _ -> FormulaSet.singleton vf
  | Label _ -> raise (Failure "vf_to_set : Label")

let set_to_vf : FormulaSet.t -> vformula 
= fun set ->
  FormulaSet.fold (fun f acc ->
    if equal_vf acc VTrue then f
    else VAnd (acc,f) 
  ) set VTrue

let compress : vformula -> vformula
= fun vf -> set_to_vf (vf_to_set vf)

let rec fix f x =
  let x' = f x in
  if equal_vf x' x then x'
  else fix f x'

let simplify : vformula -> vformula
= fun vf -> fix (fun x -> compress (normalize x)) vf

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
  | SigmaEqual _ | NoOverFlow _ | UntrustSum _ | UntrustSum2 _ -> vf
  | ForAll _ -> vf
  | VNot _ | VOr _
  | Imply _ | Label _ -> raise (Failure "msg_num_const")

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
  | SigmaEqual (x,e) -> include_pow_ve e
  | NoOverFlow _ -> false
  | UntrustSum _ | UntrustSum2 _ -> false
  | ForAll (vars,f) -> include_pow_vf f
  | Label (l,f) -> include_pow_vf f

and include_pow_ve : vexp -> bool
= fun ve ->
  match ve with
  | VInt _ | VVar _ -> false
  | Read (e1,e2) -> include_pow_ve e1 || include_pow_ve e2
  | Write (e1,e2,e3) -> include_pow_ve e1 || include_pow_ve e2 || include_pow_ve e3
  | VBinOp (VPower,_,_,_) -> true
  | VBinOp (_,e1,e2,_) -> include_pow_ve e1 || include_pow_ve e2
  | VUnOp (_,e,_) -> include_pow_ve e
  | VCast (_,e) -> include_pow_ve e
  | VCond f -> include_pow_vf f
  | Ite (e1,e2,e3) -> include_pow_ve e1 || include_pow_ve e2 || include_pow_ve e3
  | Uninterp (_,args,_) -> List.fold_left (fun acc e' -> include_pow_ve e' || acc) false args

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
  | SigmaEqual _ | NoOverFlow _ | UntrustSum _ | UntrustSum2 _ -> (vf,[])
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
    let itv_e1' = Val.itv_of (ItvSem2.eval_ve e1' mem) in
    let itv_ve' = Val.itv_of (ItvSem2.eval_ve ve' mem) in
    (match !Options.mode with
     | "exploit" ->
       (* Why casting is needed? *)
       (* uint result = ...; *)
       (* (2 ** result) + uint8 => common type: 'uint256'. *)
       (* However, 2**18 + uint8 => common type: 'uint24' *)
       (* Thus, output uint(2**18) by explicitly casting. *)
       if Itv.is_const itv_ve' then
         let ve'' = VInt (Itv.lower_int itv_ve') in
         let ve'' = if t=ConstInt then ve'' else VCast (t,ve'') in
         (ve'', lst1 @ lst2)
       else if Itv.is_const itv_e1' then
         let ve'' = VInt (BatBig_int.pow (Itv.lower_int itv_e1') (BatBig_int.of_int 18)) in
         let ve'' = if t=ConstInt then ve'' else VCast (t,ve'') in
         (ve'', e2'::(lst1 @ lst2))
       else (VVar (gen_newsym t), lst1 @ lst2)
     | _ ->
       if Itv.is_const itv_ve' then
         (VCast (t, VInt (Itv.lower_int itv_ve')), lst1 @ lst2)
       else (ve', lst1 @ lst2))
       (* else (VVar (gen_newsym t), lst1 @ lst2)) *)
  | VBinOp (bop,e1,e2,t) ->
    let (e1',lst1) = rm_pow_ve mem e1 in
    let (e2',lst2) = rm_pow_ve mem e2 in
    (VBinOp (bop, e1', e2', t), lst1 @ lst2)
  | Read (e1,e2) ->
    let (e1',lst1) = rm_pow_ve mem e1 in
    let (e2',lst2) = rm_pow_ve mem e2 in
    (Read (e1', e2'), lst1 @ lst2)
  | Write (e1,e2,e3) ->
    let (e1',lst1) = rm_pow_ve mem e1 in
    let (e2',lst2) = rm_pow_ve mem e2 in
    let (e3',lst3) = rm_pow_ve mem e3 in
    (Write (e1', e2', e3'), lst1 @ lst2 @ lst3)
  | VUnOp (uop,e,t) ->
    let (e',lst) = rm_pow_ve mem e in
    if get_typ_vexp e' = t then (VUnOp (uop, e', t), lst)
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
  | Uninterp (fname,args,typ) ->
    List.fold_left (fun (acc_args,acc_lst) e ->
      let (e',lst) = rm_pow_ve mem e in
      (acc_args @ [e'], acc_lst @ lst)
    ) ([],[]) args
    |> (fun (args',lst') -> (Uninterp (fname,args',typ), lst'))

let remove_pow : vformula -> vformula
= fun vf ->
  let (pre,sc) = if !Options.mode="exploit" then split_vc vf else split_implication vf in
  let mem = ItvAnalysis2.run pre in (* perform interval analysis on formula *)
  let (pre',lst1) = rm_pow_vf mem pre in
  let (sc',lst2) = rm_pow_vf mem sc in
  (* verify mode => no concretizations are performed. *)
  let _ = assert (!Options.mode="exploit" || List.length (lst1 @ lst2) = 0) in
  let new_f =
    List.fold_left (fun acc ve ->
      let f' = VBinRel (VEq, ve, VInt (BatBig_int.of_int 18)) in
      if equal_vf acc VTrue then f' else VAnd (acc, f')
    ) VTrue (lst1 @ lst2) in
  let final = if !Options.mode="exploit" then VAnd (VAnd (pre',new_f), VNot sc') else Imply (pre',sc') in
  (* let _ = assert (not (include_pow_vf final)) in *)
  let _ = assert (not (!Options.mode="exploit") || not (include_pow_vf final)) in
  final

let rec prop_eq_vf : vformula -> vformula -> vformula
= fun state vf ->
  match vf with
  | VTrue | VFalse -> vf
  | VNot f -> VNot (prop_eq_vf state f)
  | VAnd (f1,f2) -> VAnd (prop_eq_vf state f1, prop_eq_vf state f2)
  | VOr (f1,f2) -> VOr (prop_eq_vf state f1, prop_eq_vf state f2)

  | VBinRel (VEq,e1,VCond VTrue) ->
    let vf' = VBinRel (VEq, prop_eq_ve state e1, VCond VTrue) in
    if equal_vf VTrue (normalize vf') then vf
    else if equal_vf vf vf' then vf
    else
      (* let _ = print_endline "\nHI1" in
      let _ = print_endline (to_string_vformula vf) in
      let _ = print_endline (to_string_vformula vf') in *)
      vf'

  | VBinRel (VEq,e1,e2) (* when is_uintkind (get_typ_vexp e1) *) ->
    let vf' = VBinRel (VEq, e1, prop_eq_ve state e2) in
    if equal_vf VTrue (normalize vf') then vf (* to avoid losing info, .e.g., a=b /\ ... => b=b /\ ... *)
    else if equal_vf vf vf' then vf
    else
      (* let _ = print_endline "\nHI1" in
      let _ = print_endline (to_string_vformula vf) in
      let _ = print_endline (to_string_vformula vf') in *)
      vf'

  | VBinRel (brel,e1,e2) ->
    let vf' = VBinRel (brel, prop_eq_ve state e1, prop_eq_ve state e2) in
    if equal_vf VTrue (normalize vf') then vf (* to avoid losing info, .e.g., a=b /\ ... => b=b /\ ... *)
    else if equal_vf vf vf' then vf
    else
      (* let _ = print_endline "\nHI2" in
      let _ = print_endline (to_string_vformula vf) in
      let _ = print_endline (to_string_vformula vf') in *)
      (* let _ = print_endline (to_string_vformula state ) in *)
      vf'
  | Imply (f1,f2) -> Imply (prop_eq_vf state f1, prop_eq_vf state f2)
  | SigmaEqual _ | NoOverFlow _ | UntrustSum _ | UntrustSum2 _ -> vf
  | ForAll (bvs,f) -> ForAll (bvs, prop_eq_vf state f)
  | Label (l,f) -> Label (l, prop_eq_vf state f)

and prop_eq_ve : vformula -> vexp -> vexp
= fun state ve ->
  match ve with
  | VInt _ -> ve
    (* the goal is to make forms that can be checked with templates *)
    (* O: tmp=b[f] /\ tmp>=v ~> b[f]>=v *)
    (* X: b' = write (b'',f,b''[f]-v]) /\ b = write (b',t,b'[t]+v) ~>
     *    b = write (write(b'',f,b''[f]-v), t, (write(b'',f',b''[f]-v)[t] + v) *)
  | VVar x when is_mapping (snd x) || is_mapping2 (snd x) -> ve
  | VVar x ->
    let reps = collect_reps state x in
    if not (ExpSet.cardinal reps = 1) then ve
    else
      let rep = ExpSet.choose reps in
      (match rep with
       | VInt n -> VCast (snd x, VInt n) | _ -> rep)
  | Read (e1,e2) -> Read (prop_eq_ve state e1, prop_eq_ve state e2)
  | Write (e1,e2,e3) -> Write (prop_eq_ve state e1, prop_eq_ve state e2, prop_eq_ve state e3)
  | VBinOp (bop,e1,e2,t) -> VBinOp (bop, prop_eq_ve state e1, prop_eq_ve state e2, t)
  | VUnOp (uop,e,t) -> VUnOp (uop, prop_eq_ve state e, t)
  | VCast (t,e) -> VCast (t, prop_eq_ve state e)
  | VCond f -> VCond (prop_eq_vf state f)
  | Ite (e1,e2,e3) -> Ite (prop_eq_ve state e1, prop_eq_ve state e2, prop_eq_ve state e3)
  | Uninterp (fname,args,typ) -> Uninterp (fname, List.map (prop_eq_ve state) args, typ)

(* collect replacements for 'target' *)
and collect_reps : vformula -> var -> ExpSet.t
= fun vf target ->
  match vf with
  | VTrue | VFalse -> ExpSet.empty
  | VNot _ -> ExpSet.empty
  | VAnd (f1,f2) -> ExpSet.union (collect_reps f1 target) (collect_reps f2 target)
  | VOr (f1,f2) -> ExpSet.empty

  | VBinRel (VEq, VVar x, VBinOp (VDiv,_,_,_)) -> ExpSet.empty

  | VBinRel (VEq, VVar x, Ite _) -> ExpSet.empty

  | VBinRel (VEq, VVar x, VCond VTrue) -> ExpSet.empty

  | VBinRel (VEq, VVar x, ve2) when target = x -> ExpSet.singleton ve2
  | VBinRel _ -> ExpSet.empty
  | Imply _ -> ExpSet.empty
  | SigmaEqual _ | NoOverFlow _ | UntrustSum _ | UntrustSum2 _ -> ExpSet.empty
  | ForAll (vars,f) -> ExpSet.empty
  | Label (_,f) -> collect_reps f target

let propagate_eq : vformula -> vformula
= fun vf ->
  let state = match vf with Imply (pre,con) -> pre | _ -> assert false in
  let res = prop_eq_vf state vf in
  res
