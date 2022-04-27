open Vlang
open Lang
open Vocab
open Semantics

(***************)
(*** Helpers ***)
(***************)

let cartesian_2 : vformula list -> vformula list list
= fun flst -> BatList.n_cartesian_product [flst;flst]

let cartesian_3 : vformula list -> vformula list list
= fun flst -> BatList.n_cartesian_product [flst;flst;flst]

let cartesian_4 : vformula list -> vformula list list
= fun flst ->
  let flst1 = List.filter (fun vf -> match vf with NoOverFlow _ -> true | _ -> false) flst in
  let flst2 = List.filter (fun vf ->
                match vf with
                | SigmaEqual _ | VBinRel (VGeq, _, _) | VBinRel (VGt,_,_) -> true
                | VBinRel (VEq, VVar _, Write (VVar _, x, VBinOp (VAdd, Read (VVar _, x1), v, _))) -> equal_ve x x1
                | _ -> false
              ) flst in
  let flst3 = List.filter (fun vf ->
                match vf with
                | VBinRel (VGeq, _, _) | VBinRel (VGt,_,_) -> true
                (* | VBinRel (VGeq, VInt _, VVar _) -> true *)
                | VBinRel (VEq, VVar _, VInt _) -> true
                | VBinRel (VEq, VVar _, Write (VVar _, x, VBinOp (VSub, Read (VVar _, x1), v, _))) -> equal_ve x x1
                | VBinRel (VEq, VVar _, Write (VVar _, x, VBinOp (VAdd, Read (VVar _, x1), v, _))) -> equal_ve x x1
                | _ -> false
              ) flst in
  let flst4 = List.filter (fun vf ->
                match vf with
                | VBinRel (VGeq, Read (VVar _,_), _) -> true
                | VBinRel (VEq, VVar _, Write (VVar _, x, VBinOp (VSub, Read (VVar _, x1), v, _))) -> equal_ve x x1
                | VBinRel (VEq, VVar _, Write (VVar _, x, VBinOp (VAdd, Read (VVar _, x1), v, _))) -> equal_ve x x1
                | _ -> false
              ) flst in
  BatList.n_cartesian_product [flst1;flst2;flst3;flst4]

let cartesian_5 : vformula list -> vformula list list
= fun flst ->
  let flst1 = List.filter (fun vf -> match vf with NoOverFlow _ -> true | _ -> false) flst in
  let flst2 = List.filter (fun vf -> match vf with SigmaEqual _ | VBinRel (VGeq, Read (VVar _,VVar _), VVar _) -> true | _ -> false) flst in
  let flst3 = List.filter (fun vf ->
                match vf with
                | VBinRel (VEq, VVar _, VInt _)
                | VBinRel (VEq, VVar _, Write (VVar _, VVar _, VBinOp (VSub, Read (VVar _, VVar _), VVar _, _))) -> true
                | _ -> false
              ) flst in
  let flst4 = List.filter (fun vf ->
                match vf with
                | VBinRel (VGeq, Read (VVar _,VVar _), VVar _)
                | VBinRel (VEq, VVar _, Read (VVar _, VVar _)) -> true
                | _ -> false
              ) flst in
  let flst5 = List.filter (fun vf ->
                match vf with
                | VBinRel (VEq, VVar _, Read (VVar _,VVar _))
                | VBinRel (VEq, VVar _, VVar _) -> true
                | _ -> false
              ) flst in
  BatList.n_cartesian_product [flst1;flst2;flst3;flst4;flst5]

let cartesian_6 : vformula list -> vformula list list
= fun flst ->
  let flst1 = List.filter (fun vf -> match vf with NoOverFlow _ -> true | _ -> false) flst in
  let flst2 = List.filter (fun vf -> match vf with SigmaEqual _ -> true | _ -> false) flst in
  let flst3 = List.filter (fun vf -> match vf with VBinRel (VGeq,VInt _,VVar _) | VBinRel (VEq,VVar _,VInt _) -> true | _ -> false) flst in
  let flst4 = List.filter (fun vf -> match vf with VBinRel (VGeq, Read (VVar _, VVar _), VVar _) -> true | _ -> false) flst in
  let flst5 = List.filter (fun vf -> match vf with VBinRel (VEq, VVar _, Write (VVar _, VVar _, VBinOp (VSub, Read (VVar _, VVar _), VVar _, _))) -> true | _ -> false) flst in
  let flst6 = List.filter (fun vf -> match vf with VBinRel (VEq, VVar _, Write (VVar _, VVar _, VBinOp (VAdd, Read (VVar _, VVar _), VVar _, _))) -> true | _ -> false) flst in
  BatList.n_cartesian_product [flst1;flst2;flst3;flst4;flst5;flst6]

let cartesian_5_leak : vformula list -> vformula list list
= fun flst ->
  let flst1 = List.filter (fun vf ->
                match vf with
                | UntrustSum _ -> true | UntrustSum2 _ -> true
                | _ -> false
              ) flst in
  let flst2 = List.filter (fun vf ->
                match vf with
                | VBinRel (VGeq,_,_) | VBinRel (VGt,_,_) -> true
                | VOr (VAnd _, VAnd _) -> true
                | VBinRel (VEq, Read _, VCond VTrue) -> true
                | VBinRel (VEq, VVar _, Ite (VCond (VBinRel (VEq, Read (VVar _, _), VCond VFalse)), _, _)) -> true
                | _ -> false
              ) flst in
  let flst3 = List.filter (fun vf ->
                match vf with
                | VBinRel (VGeq,_,_) | VBinRel (VGt,_,_) -> true
                | VBinRel (VEq, VVar _, Write (VVar _, x, VBinOp (bop, Read (VVar _, x1), v, _))) when bop=VAdd || bop=VSub -> equal_ve x x1
                | VBinRel (VEq, VVar _, Ite (VCond (VBinRel (VEq, Read (VVar _, _), VCond VFalse)), _, _)) -> true
                | _ -> false
              ) flst in
  let flst4 = List.filter (fun vf ->
                match vf with
                | VBinRel (VEq, Read (VVar ("@TU", Mapping (Address, EType Bool)),_), VCond VFalse) -> true
                | VBinRel (VEq, VVar _, Write (VVar _, x, VBinOp (bop, Read (VVar _, x1), v, _))) when bop=VAdd || bop=VSub -> equal_ve x x1
                | VBinRel (VGeq,_,_) -> true | VBinRel (VGt,_,_) -> true
                | _ -> false
              ) flst in
  let flst5 = List.filter (fun vf ->
                match vf with
                | VBinRel (VEq, VVar _, Write (VVar _, x, VBinOp (bop, Read (VVar _, x1), v, _))) when bop=VAdd || bop=VSub -> equal_ve x x1
                | VBinRel (VEq, VVar x, VBinOp (VSub, VVar y,_,_)) when org x = org y && x = ("@Invest_sum", EType (UInt 256)) -> true
                | _ -> false
              ) flst in
  BatList.n_cartesian_product [flst1; flst2; flst3; flst4; flst5]


let cartesian_7_leak : vformula list -> vformula list list
= fun flst ->
  let flst1 = List.filter (fun vf -> match vf with UntrustSum _ -> true | _ -> false) flst in
  let flst2 = List.filter (fun vf ->
                match vf with
                | VBinRel (VEq, Read (VVar ("@TU", Mapping (Address, EType Bool)),VVar ("@this", EType Address)), VCond VTrue) -> true
                | VBinRel (VEq, VVar _, Ite (VCond (VBinRel (VEq, Read (VVar _, _), VCond VFalse)), _, _)) -> true
                | VOr (VAnd _, VAnd _) -> true
                | _ -> false
              ) flst in
  let flst3 = List.filter (fun vf ->
                match vf with
                | VBinRel (VGeq,_,_) | VBinRel (VGt,_,_) -> true
                | VBinRel (VEq, _, VBinOp (VDiv, _, _, _)) -> true
                | _ -> false
              ) flst in
  let flst4 = List.filter (fun vf ->
                match vf with
                | VBinRel (VEq, VVar _, Write (VVar _, x, VBinOp (bop, Read (VVar _, x1), v, _))) when bop=VAdd || bop=VSub -> equal_ve x x1
                | VNot (VBinRel (VEq, div1, VInt zero)) -> true
                | VBinRel (VEq, VVar _, Ite (VCond (VBinRel (VEq, Read (VVar _, _), VCond VFalse)), _, _)) -> true
                | _ -> false
              ) flst in
  let flst5 = List.filter (fun vf ->
                match vf with
                | VBinRel (VEq, VVar _, Write (VVar _, x, VBinOp (bop, Read (VVar _, x1), v, _))) when bop=VAdd || bop=VSub -> equal_ve x x1
                | VBinRel (VGeq,_,_) | VBinRel (VGt,_,_) -> true
                | _ -> false
              ) flst in
  let flst6 = List.filter (fun vf ->
                match vf with
                | VBinRel (VEq, Read (VVar ("@TU", Mapping (Address, EType Bool)),_), VCond VFalse) -> true
                | VBinRel (VEq, VVar _, Write (VVar _, x, VBinOp (bop, Read (VVar _, x1), v, _))) when bop=VAdd || bop=VSub -> equal_ve x x1
                | _ -> false
              ) flst in
  let flst7 = List.filter (fun vf ->
                match vf with
                | VBinRel (VEq, VVar x, VBinOp (VSub, VVar y,_,_)) when org x = org y && x = ("@Invest_sum", EType (UInt 256)) -> true
                | VBinRel (VEq, VVar _, Write (VVar _, x, VBinOp (bop, Read (VVar _, x1), v, _))) when bop=VAdd || bop=VSub -> equal_ve x x1
                | _ -> false
              ) flst in
  BatList.n_cartesian_product [flst1; flst2; flst3; flst4; flst5; flst6; flst7]


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
  | UntrustSum _ -> false
  | UntrustSum2 _ -> false
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
  | UntrustSum _ -> false
  | UntrustSum2 _ -> false
  | ForAll (_,f) -> has_sigeq f
  | Label (_,f) -> has_sigeq f

let rec has_usum : vformula -> bool
= fun vf ->
  match vf with
  | VTrue | VFalse -> false
  | VNot f -> has_usum f
  | VAnd (f1,f2) -> has_usum f1 || has_usum f2
  | VOr (f1,f2) -> has_usum f1 || has_usum f2
  | VBinRel _ -> false
  | Imply (f1,f2) -> has_usum f1 || has_usum f2
  | SigmaEqual _ -> false
  | NoOverFlow _ -> false
  | UntrustSum _ -> true
  | UntrustSum2 _ -> true
  | ForAll (_,f) -> has_usum f
  | Label (_,f) -> has_usum f


(**********************************)
(*** Tactics to aid SMT solvers ***)
(**********************************)

let tactic_3 : vformula -> vformula
= fun vf ->
  if not (has_sigeq vf) then vf
  else
  let lst_3 = vf |> list_of_conjuncts |> cartesian_3 in
  List.fold_left (fun acc l ->
    match l with
    | [SigmaEqual ((b_,typ), total);
       VBinRel (VEq, VVar (b__,_), Write (VVar (b_1,_), x, VBinOp (VSub, Read (VVar (b_2,_), x1), v, _)));
       VBinRel (VEq, VVar (b,_), Write (VVar (b__1,_), y, VBinOp (VAdd, Read (VVar (b__2,_), y1), v1, _)))]
       when is_renamed b_ && is_renamed b__ && not (is_renamed b) &&
            BatString.equal b_ b_1 && BatString.equal b_1 b_2 &&
            BatString.equal b__ b__1 && BatString.equal b__1 b__2 &&
            equal_ve x x1 && equal_ve y y1 &&
            equal_ve v v1
       -> VAnd (acc, SigmaEqual ((b,typ), total))

    | [SigmaEqual ((b_,typ), total);
       VBinRel (VEq, VVar (b__,_), Write (VVar (b_1,_), x, VBinOp (VAdd, Read (VVar (b_2,_), x1), v, _)));
       VBinRel (VEq, VVar (b,_), Write (VVar (b__1,_), y, VBinOp (VSub, Read (VVar (b__2,_), y1), v1, _)))]
       when is_renamed b_ && is_renamed b__ && not (is_renamed b) &&
            BatString.equal b_ b_1 && BatString.equal b_1 b_2 &&
            BatString.equal b__ b__1 && BatString.equal b__1 b__2 &&
            equal_ve x x1 && equal_ve y y1 &&
            equal_ve v v1
       -> VAnd (acc, SigmaEqual ((b,typ), total))

      (* burn *)
    | [NoOverFlow (b_,typ);
       VBinRel (brel, Read (VVar (b_1,_), x), v);
       VBinRel (VEq, VVar (b,_), Write (VVar (b_2,_), x1, VBinOp (VSub, Read (VVar (b_3,_), x2), v1, _)))]
       when is_renamed b_ && not (is_renamed b) &&
            BatString.equal b_ b_1 && BatString.equal b_1 b_2 && BatString.equal b_2 b_3 &&
            equal_ve x x1 && equal_ve x1 x2 &&
            equal_ve v v1 &&
            (brel = VGeq || brel = VGt)
       -> VAnd (acc, NoOverFlow (b,typ))

    | _ -> acc
  ) vf lst_3

let tactic_4 : vformula -> vformula
= fun vf ->
  if not (has_noflow vf) then vf
  else
  let lst_4 = try vf |> list_of_conjuncts |> cartesian_4 with Stack_overflow -> [] in
  List.fold_left (fun acc l ->
    match l with
    | [NoOverFlow (b_, typ);
       VBinRel (brel, Read (VVar (b_1,_), x), v);
       VBinRel (VEq, VVar (b__,_), Write (VVar (b_2,_), x1, VBinOp (VSub, Read (VVar (b_3,_), x2), v1, _)));
       VBinRel (VEq, VVar (b,_), Write (VVar (b__1,_), y, VBinOp (VAdd, Read (VVar (b__2,_), y1), v2, _)))]
       when is_renamed b_ && is_renamed b__ && not (is_renamed b) &&
            BatString.equal b_ b_1 && BatString.equal b_1 b_2 && BatString.equal b_2 b_3 &&
            BatString.equal b__ b__1 && BatString.equal b__1 b__2 &&
            equal_ve x x1 && equal_ve x1 x2 &&
            equal_ve y y1 &&
            equal_ve v v1 && equal_ve v1 v2 &&
            (brel = VGeq || brel = VGt)
       -> VAnd (acc, NoOverFlow (b, typ))
    | [NoOverFlow (b_, typ);
       VBinRel (brel, Read (VVar (b_1,_), x), v);
       VBinRel (VEq, VVar (b__,_), Write (VVar (b_2,_), y, VBinOp (VAdd, Read (VVar (b_3,_), y1), v1, _)));
       VBinRel (VEq, VVar (b,_), Write (VVar (b__1,_), x1, VBinOp (VSub, Read (VVar (b__2,_), x2), v2, _)))]
       when is_renamed b_ && is_renamed b__ && not (is_renamed b) &&
            BatString.equal b_ b_1 && BatString.equal b_1 b_2 && BatString.equal b_2 b_3 &&
            BatString.equal b__ b__1 && BatString.equal b__1 b__2 &&
            equal_ve x x1 && equal_ve x1 x2 &&
            equal_ve y y1 &&
            equal_ve v v1 && equal_ve v1 v2 &&
            (brel = VGeq || brel = VGt)
       -> VAnd (acc, NoOverFlow (b, typ))

      (* b[t]+=v; b[f] >= v; b[f]-=v *)
    | [NoOverFlow (b_, typ);
       VBinRel (VEq, VVar (b__,_), Write (VVar (b_1,_), y, VBinOp (VAdd, Read (VVar (b_2,_), y1), v, _)));
       VBinRel (brel, Read (VVar (b__1,_), x), v1);
       VBinRel (VEq, VVar (b,_), Write (VVar (b__2,_), x1, VBinOp (VSub, Read (VVar (b__3,_), x2), v2, _)))]
       when is_renamed b_ && is_renamed b__ && not (is_renamed b) &&
            BatString.equal b_ b_1 && BatString.equal b_1 b_2 &&
            BatString.equal b__ b__1 && BatString.equal b__1 b__2 && BatString.equal b__2 b__3 &&
            equal_ve x x1 && equal_ve x1 x2 &&
            equal_ve y y1 &&
            equal_ve v v1 && equal_ve v1 v2 &&
            (brel = VGeq || brel = VGt)
       -> VAnd (acc, NoOverFlow (b, typ))

    | _ -> acc
  ) vf lst_4


let tactic_3_leak : vformula -> vformula
= fun vf ->
  if not (has_usum vf) then vf
  else
  let lst_3 = vf |> list_of_conjuncts |> cartesian_3 in
  List.fold_left (fun acc l ->
    match l with
    | [UntrustSum (isum_, b);
       VBinRel (VGeq, VBinOp (VAdd, VVar isum_1, v, _), VVar isum_2);
       VBinRel (VEq, VVar isum, Ite (VCond (VBinRel (VEq, Read (VVar trust, y), VCond VFalse)),
                                     VBinOp (VAdd, VVar isum_3, v1, _), VVar isum_4))]
       when isum_ = isum_1 && isum_1 = isum_2 && isum_2 = isum_3 && isum_3 = isum_4 &&
            not (isum_ = isum) &&
            (is_renamed (fst isum_)) &&
            equal_ve v v1 &&
            trust_map = trust
       ->
       let lst = list_of_conjuncts acc in
       if List.exists (fun vf' -> equal_vf vf' (UntrustSum (isum,b))) lst then acc
       else VAnd (acc, UntrustSum (isum, b))

    | [UntrustSum2 (isum_, s, b);
       VBinRel (VGeq, VBinOp (VAdd, VVar isum_1, v, _), VVar isum_2);
       VBinRel (VEq, VVar isum, Ite (VCond (VBinRel (VEq, Read (VVar trust, y), VCond VFalse)),
                                     VBinOp (VAdd, VVar isum_3, v1, _), VVar isum_4))]
       when isum_ = isum_1 && isum_1 = isum_2 && isum_2 = isum_3 && isum_3 = isum_4 &&
            not (isum_ = isum) &&
            (is_renamed (fst isum_)) &&
            equal_ve v v1 &&
            trust_map = trust
       ->
       let lst = list_of_conjuncts acc in
       if List.exists (fun vf' -> equal_vf vf' (UntrustSum2 (isum,s,b))) lst then acc
       else VAnd (acc, UntrustSum2 (isum, s, b))

    | _ -> acc
  ) vf lst_3

let tactic_5_leak : vformula -> vformula
= fun vf ->
  if not (has_usum vf) then vf
  else
  let lst_5 = try vf |> list_of_conjuncts |> cartesian_5_leak with Stack_overflow -> [] in
  List.fold_left (fun acc l ->
    match l with
    | [UntrustSum (isum_, b_);
       VBinRel (brel, Read (VVar b_1, x), v);
       VBinRel (VEq, VVar b, Write (VVar b_2, x1, VBinOp (VSub, Read (VVar b_3, x2), v1, _)));
       VBinRel (VEq, Read (VVar trust, x3), VCond VFalse);
       VBinRel (VEq, VVar isum, VBinOp (VSub, VVar isum_1, v2, _))]
       when is_renamed (fst b_) && not (is_renamed (fst b)) &&
            b_ = b_1 && b_1 = b_2 && b_2 = b_3 &&
            equal_ve x x1 && equal_ve x1 x2 && equal_ve x2 x3 &&
            equal_ve v v1 && equal_ve v1 v2 &&
            is_renamed (fst isum_) && not (is_renamed (fst isum)) &&
            isum_ = isum_1 &&
            trust = trust_map &&
            (brel = VGeq || brel = VGt)
       -> VAnd (acc, UntrustSum (isum, b))

    | [UntrustSum (isum, b_);
       VBinRel (brel, Read (VVar b_1, x), v);
       VBinRel (VEq, VVar b, Write (VVar b_2, x1, VBinOp (VSub, Read (VVar b_3, x2), v1, _)));
       f; f']
       when is_renamed (fst b_) && not (is_renamed (fst b)) &&
            b_ = b_1 && b_1 = b_2 && b_2 = b_3 &&
            equal_ve x x1 && equal_ve x1 x2 &&
            equal_ve v v1 &&
            not (is_renamed (fst isum)) &&
            (brel = VGeq || brel = VGt)
       -> VAnd (acc, UntrustSum (isum, b))

    | [UntrustSum2 (isum_, s, b_);
       VBinRel (brel, Read (VVar b_1, Read (VVar s1, x)), v);
       VBinRel (VEq, VVar b, Write (VVar b_2, Read (VVar s2,x1), VBinOp (VSub, Read (VVar b_3, Read (VVar s3,x2)), v1, _)));
       VBinRel (VEq, Read (VVar trust, x3), VCond VFalse);
       VBinRel (VEq, VVar isum, VBinOp (VSub, VVar isum_1, v2, _))]
       when b_ = b_1 && b_1 = b_2 && b_2 = b_3 && not (b_ = b) &&
            s = s1 && s1 = s2 && s2 = s3 &&
            equal_ve x x1 && equal_ve x1 x2 && equal_ve x2 x3 &&
            equal_ve v v1 && equal_ve v1 v2 &&
            isum_ = isum_1 && not (isum_ = isum) &&
            trust = trust_map &&
            (brel = VGeq || brel = VGt)
       ->
       let lst = list_of_conjuncts acc in
       if List.exists (fun vf' -> equal_vf vf' (UntrustSum2 (isum,s,b))) lst then acc
       else VAnd (acc, UntrustSum2 (isum, s, b))

    | [UntrustSum2 (isum_, s, b_);
       VBinRel (VGeq, VBinOp (VAdd, VVar isum_1, v, _), VVar isum_2);
       VBinRel (VEq, VVar isum, Ite (VCond (VBinRel (VEq, Read (VVar trust, x), VCond VFalse)),
                                     VBinOp (VAdd, VVar isum_3, v1, _), VVar isum_4));
       VBinRel (VEq, VVar b, Write (VVar b_1, Read (VVar s1,x1), VBinOp (VAdd, Read (VVar b_2, Read (VVar s2,x2)), v2, _)));
       f]
       when isum_ = isum_1 && isum_1 = isum_2 && isum_2 = isum_3 && isum_3 = isum_4 &&
            not (isum_ = isum) &&
            equal_ve v v1 && equal_ve v1 v2 &&
            trust_map = trust &&
            s = s1 && s1 = s2 &&
            equal_ve x x1 && equal_ve x1 x2 &&
            b_ = b_1 && b_1 = b_2 &&
            not (b_ = b)
       ->
       let lst = list_of_conjuncts acc in
       if List.exists (fun vf' -> equal_vf vf' (UntrustSum2 (isum,s,b))) lst then acc
       else VAnd (acc, UntrustSum2 (isum, s, b))

     | [UntrustSum2 (isum, s, b_);
       VBinRel (brel, Read (VVar b_1, Read (VVar s1, x)), v);
       VBinRel (VEq, VVar b, Write (VVar b_2, Read (VVar s2,x1), VBinOp (VSub, Read (VVar b_3, Read (VVar s3,x2)), v1, _)));
       f1;
       f2]
       when b_ = b_1 && b_1 = b_2 && b_2 = b_3 && not (b_ = b) &&
            s = s1 && s1 = s2 && s2 = s3 &&
            equal_ve x x1 && equal_ve x1 x2 &&
            equal_ve v v1 &&
            (brel = VGeq || brel = VGt)
       ->
       let lst = list_of_conjuncts acc in
       if List.exists (fun vf' -> equal_vf vf' (UntrustSum2 (isum,s,b))) lst then acc
       else VAnd (acc, UntrustSum2 (isum, s, b))

    | [UntrustSum (isum, b_);
       VOr (case1, case2);
       VBinRel (brel, Read (VVar b_1, x), v);
       VBinRel (VEq, VVar b__, Write (VVar b_2, x1, VBinOp (VSub, Read (VVar b_3, x2), v1, _)));
       VBinRel (VEq, VVar b, Write (VVar b__1, y, VBinOp (VAdd, Read (VVar b__2, y1), v2, _)))]
       when not (is_renamed (fst isum)) &&
            is_renamed (fst b_) && is_renamed (fst b__) && not (is_renamed (fst b)) &&
            b_ = b_1 && b_1 = b_2 && b_2 = b_3 &&
            b__ = b__1 && b__1 = b__2 &&
            equal_ve x x1 && equal_ve x1 x2 &&
            equal_ve y y1 &&
            equal_ve v v1 && equal_ve v1 v2 &&
            (brel = VGeq || brel = VGt)
       ->
       let true_x = List.exists (fun vf -> match vf with VBinRel (VEq, Read (VVar trust_map, x'), VCond VTrue) when equal_ve x' x -> true | _ -> false) (list_of_conjuncts case1) in
       let true_y = List.exists (fun vf -> match vf with VBinRel (VEq, Read (VVar trust_map, y'), VCond VTrue) when equal_ve y' y -> true | _ -> false) (list_of_conjuncts case1) in
       let false_x = List.exists (fun vf -> match vf with VBinRel (VEq, Read (VVar trust_map, x'), VCond VFalse) when equal_ve x' x -> true | _ -> false) (list_of_conjuncts case2) in
       let false_y = List.exists (fun vf -> match vf with VBinRel (VEq, Read (VVar trust_map, y'), VCond VFalse) when equal_ve y' y -> true | _ -> false) (list_of_conjuncts case2) in
       if true_x && true_y && false_x && false_y then VAnd (acc, UntrustSum (isum, b))
       else acc

    | [UntrustSum (isum, b_);
       VOr (case1, case2);
       VBinRel (brel, Read (VVar b_1, x), v);
       VBinRel (VEq, VVar b__, Write (VVar b_2, y, VBinOp (VAdd, Read (VVar b_3, y1), v1, _)));
       VBinRel (VEq, VVar b, Write (VVar b__1, x1, VBinOp (VSub, Read (VVar b__2, x2), v2, _)))]
       when not (is_renamed (fst isum)) &&
            is_renamed (fst b_) && is_renamed (fst b__) && not (is_renamed (fst b)) &&
            b_ = b_1 && b_1 = b_2 && b_2 = b_3 &&
            b__ = b__1 && b__1 = b__2 &&
            equal_ve x x1 && equal_ve x1 x2 &&
            equal_ve y y1 &&
            equal_ve v v1 && equal_ve v1 v2 &&
            (brel = VGeq || brel = VGt)
       ->
       let true_x = List.exists (fun vf -> match vf with VBinRel (VEq, Read (VVar trust_map, x'), VCond VTrue) when equal_ve x' x -> true | _ -> false) (list_of_conjuncts case1) in
       let true_y = List.exists (fun vf -> match vf with VBinRel (VEq, Read (VVar trust_map, y'), VCond VTrue) when equal_ve y' y -> true | _ -> false) (list_of_conjuncts case1) in
       let false_x = List.exists (fun vf -> match vf with VBinRel (VEq, Read (VVar trust_map, x'), VCond VFalse) when equal_ve x' x -> true | _ -> false) (list_of_conjuncts case2) in
       let false_y = List.exists (fun vf -> match vf with VBinRel (VEq, Read (VVar trust_map, y'), VCond VFalse) when equal_ve y' y -> true | _ -> false) (list_of_conjuncts case2) in
       if true_x && true_y && false_x && false_y then VAnd (acc, UntrustSum (isum, b))
       else acc

    | [UntrustSum (isum, b_);
       VOr (case1, case2);
       VBinRel (VEq, VVar b__, Write (VVar b_1, y, VBinOp (VAdd, Read (VVar b_2, y1), v, _)));
       VBinRel (brel, Read (VVar b__1, x), v1);
       VBinRel (VEq, VVar b, Write (VVar b__2, x1, VBinOp (VSub, Read (VVar b__3, x2), v2, _)))]
       when not (is_renamed (fst isum)) &&
            is_renamed (fst b_) && is_renamed (fst b__) && not (is_renamed (fst b)) &&
            b_ = b_1 && b_1 = b_2 &&
            b__ = b__1 && b__1 = b__2 && b__2 = b__3 &&
            equal_ve x x1 && equal_ve x1 x2 &&
            equal_ve y y1 &&
            equal_ve v v1 && equal_ve v1 v2 &&
            (brel = VGeq || brel = VGt)
       ->
       let true_x = List.exists (fun vf -> match vf with VBinRel (VEq, Read (VVar trust_map, x'), VCond VTrue) when equal_ve x' x -> true | _ -> false) (list_of_conjuncts case1) in
       let true_y = List.exists (fun vf -> match vf with VBinRel (VEq, Read (VVar trust_map, y'), VCond VTrue) when equal_ve y' y -> true | _ -> false) (list_of_conjuncts case1) in
       let false_x = List.exists (fun vf -> match vf with VBinRel (VEq, Read (VVar trust_map, x'), VCond VFalse) when equal_ve x' x -> true | _ -> false) (list_of_conjuncts case2) in
       let false_y = List.exists (fun vf -> match vf with VBinRel (VEq, Read (VVar trust_map, y'), VCond VFalse) when equal_ve y' y -> true | _ -> false) (list_of_conjuncts case2) in
       if true_x && true_y && false_x && false_y then VAnd (acc, UntrustSum (isum, b))
       else acc


    | [UntrustSum (isum_, b_);
       VBinRel (VEq, VVar isum, Ite (VCond (VBinRel (VEq, Read (VVar trust, y), VCond VFalse)),
                                     VBinOp (VAdd, VVar isum_1, v, _), VVar isum_2));
       VBinRel (brel, Read (VVar b_1, x), v1);
       VBinRel (VEq, VVar b__, Write (VVar b_2, x1, VBinOp (VSub, Read (VVar b_3, x2), v2, _)));
       VBinRel (VEq, VVar b, Write (VVar b__1, y1, VBinOp (VAdd, Read (VVar b__2, y2), v3, _)))]
       when is_renamed (fst b_) && is_renamed (fst b__) && not (is_renamed (fst b)) &&
            b_ = b_1 && b_1 = b_2 && b_2 = b_3 &&
            b__ = b__1 && b__1 = b__2 &&
            equal_ve x x1 && equal_ve x1 x2 &&
            equal_ve y y1 && equal_ve y1 y2 &&
            equal_ve v v1 && equal_ve v1 v2 && equal_ve v2 v3 &&
            is_renamed (fst isum_) && not (is_renamed (fst isum)) &&
            isum_ = isum_1 && isum_1 = isum_2 &&
            (brel = VGeq || brel = VGt) &&
            trust = trust_map
       -> VAnd (acc, UntrustSum (isum, b))
    | [UntrustSum (isum, b_);
       VBinRel (VEq, Read (VVar trust, y), VCond VTrue);
       VBinRel (brel, Read (VVar b_1, x), v);
       VBinRel (VEq, VVar b__, Write (VVar b_2, x1, VBinOp (VSub, Read (VVar b_3, x2), v1, _)));
       VBinRel (VEq, VVar b, Write (VVar b__1, y1, VBinOp (VAdd, Read (VVar b__2, y2), v2, _)))]
       when is_renamed (fst b_) && is_renamed (fst b__) && not (is_renamed (fst b)) &&
            b_ = b_1 && b_1 = b_2 && b_2 = b_3 &&
            b__ = b__1 && b__1 = b__2 &&
            equal_ve x x1 && equal_ve x1 x2 &&
            equal_ve y y1 && equal_ve y1 y2 &&
            equal_ve v v1 && equal_ve v1 v2 &&
            (brel = VGeq || brel = VGt) &&
            trust = trust_map
       -> VAnd (acc, VBinRel (VGeq, VVar isum, v)) (* UntrustSum (isum,b))) *)

    | [UntrustSum (isum_, b_);
       VBinRel (brel1, VBinOp (VAdd, VVar isum_1, v, _), VVar isum_2);
       VBinRel (VEq, VVar isum, Ite (VCond (VBinRel (VEq, Read (VVar trust, x), VCond VFalse)),
                                     VBinOp (VAdd, VVar isum_3, v1, _), VVar isum_4));
       VBinRel (brel2, VBinOp (VAdd, Read (VVar b_1, x1), v2, _), Read (VVar b_2, x2));
       VBinRel (VEq, VVar b, Write (VVar b_3, x3, VBinOp (VAdd, Read (VVar b_4, x4), v3, _)))]

       when is_renamed (fst b_) && not (is_renamed (fst b)) &&
            b_ = b_1 && b_1 = b_2 && b_2 = b_3 && b_3 = b_4 &&
            equal_ve x x1 && equal_ve x1 x2 && equal_ve x2 x3 && equal_ve x3 x4 &&
            equal_ve v v1 && equal_ve v1 v2 && equal_ve v2 v3 &&
            is_renamed (fst isum_) && not (is_renamed (fst isum)) &&
            isum_ = isum_1 && isum_1 = isum_2 && isum_2 = isum_3 && isum_3 = isum_4 &&
            (brel1 = VGeq || brel1 = VGt) && (brel2 = VGeq || brel2 = VGt) &&
            (* (brel1 = brel2) && *)
            trust = trust_map
       -> VAnd (acc, UntrustSum (isum, b))
      
    | _ -> acc
  ) vf lst_5

let tactic_7_leak : vformula -> vformula
= fun vf ->
  if not (has_usum vf) then vf
  else
  let lst_7 = try vf |> list_of_conjuncts |> cartesian_7_leak with Stack_overflow -> [] in
  List.fold_left (fun acc l ->
    match l with
    | [UntrustSum (isum_, b_);
       VBinRel (VEq, Read (VVar trust1, VVar this1), VCond VTrue);
       VBinRel (brel, Read (VVar b_1, x), v);
       VBinRel (VEq, VVar b__, Write (VVar b_2, x1, VBinOp (VSub, Read (VVar b_3, x2), v1, _)));
       VBinRel (VEq, VVar b, Write (VVar b__1, VVar this2, VBinOp (VAdd, Read (VVar b__2, VVar this3), v2, _)));
       VBinRel (VEq, Read (VVar trust2, x3), VCond VFalse);
       VBinRel (VEq, VVar isum, VBinOp (VSub, VVar isum_1, v3, _))]
       when is_renamed (fst b_) && is_renamed (fst b__) && not (is_renamed (fst b)) &&
            b_ = b_1 && b_1 = b_2 && b_2 = b_3 &&
            b__ = b__1 && b__1 = b__2 &&
            equal_ve x x1 && equal_ve x1 x2 && equal_ve x2 x3 &&
            equal_ve v v1 && equal_ve v1 v2 && equal_ve v2 v3 &&
            is_renamed (fst isum_) && not (is_renamed (fst isum)) &&
            isum_ = isum_1 &&
            this1 = this_addr && this2 = this_addr && this3 = this_addr &&
            trust1 = trust_map && trust2 = trust_map &&
            (brel = VGeq || brel = VGt)
       -> VAnd (acc, UntrustSum (isum, b))
      (* the order of sub and add is reversed *)
    | [UntrustSum (isum_, b_);
       VBinRel (VEq, Read (VVar trust1, VVar this1), VCond VTrue);
       VBinRel (brel, Read (VVar b_1, x), v);
       VBinRel (VEq, VVar b__, Write (VVar b_2, VVar this2, VBinOp (VAdd, Read (VVar b_3, VVar this3), v1, _)));
       VBinRel (VEq, VVar b, Write (VVar b__1, x1, VBinOp (VSub, Read (VVar b__2, x2), v2, _)));
       VBinRel (VEq, Read (VVar trust2, x3), VCond VFalse);
       VBinRel (VEq, VVar isum, VBinOp (VSub, VVar isum_1, v3, _))]
       when is_renamed (fst b_) && is_renamed (fst b__) && not (is_renamed (fst b)) &&
            b_ = b_1 && b_1 = b_2 && b_2 = b_3 &&
            b__ = b__1 && b__1 = b__2 &&
            equal_ve x x1 && equal_ve x1 x2 && equal_ve x2 x3 &&
            equal_ve v v1 && equal_ve v1 v2 && equal_ve v2 v3 &&
            is_renamed (fst isum_) && not (is_renamed (fst isum)) &&
            isum_ = isum_1 &&
            this1 = this_addr && this2 = this_addr && this3 = this_addr &&
            trust1 = trust_map && trust2 = trust_map &&
            (brel = VGeq || brel = VGt)
       -> VAnd (acc, UntrustSum (isum, b))

    | [UntrustSum (isum_, b_);
       VBinRel (VEq, VVar isum, Ite (VCond (VBinRel (VEq, Read (VVar trust, y), VCond VFalse)),
                                     VBinOp (VAdd, VVar isum_1, msgvalue, _), VVar isum_2));
       VBinRel (VEq, v, VBinOp (VDiv, msgvalue1, div, _));
       VNot (VBinRel (VEq, div1, VInt zero));
       VBinRel (brel, Read (VVar b_1, x), v1);
       VBinRel (VEq, VVar b__, Write (VVar b_2, x1, VBinOp (VSub, Read (VVar b_3, x2), v2, _)));
       VBinRel (VEq, VVar b, Write (VVar b__1, y1, VBinOp (VAdd, Read (VVar b__2, y2), v3, _)))]
       when is_renamed (fst b_) && is_renamed (fst b__) && not (is_renamed (fst b)) &&
            b_ = b_1 && b_1 = b_2 && b_2 = b_3 &&
            b__ = b__1 && b__1 = b__2 &&
            equal_ve x x1 && equal_ve x1 x2 &&
            equal_ve msgvalue (VVar msg_value) && equal_ve msgvalue1 (VVar msg_value) &&
            equal_ve div div1 && BatBig_int.equal zero BatBig_int.zero &&
            equal_ve v v1 && equal_ve v1 v2 && equal_ve v2 v3 &&
            is_renamed (fst isum_) && not (is_renamed (fst isum)) &&
            is_renamed (fst isum_) && not (is_renamed (fst isum)) &&
            isum_ = isum_1 && isum_1 = isum_2 &&
            (brel = VGeq || brel = VGt)
       -> VAnd (acc, UntrustSum (isum, b))
      (* the order of sub and add is reversed *)
    | [UntrustSum (isum_, b_);
       VBinRel (VEq, VVar isum, Ite (VCond (VBinRel (VEq, Read (VVar trust, y), VCond VFalse)),
                                     VBinOp (VAdd, VVar isum_1, msgvalue, _), VVar isum_2));
       VBinRel (VEq, v, VBinOp (VDiv, msgvalue1, div, _));
       VNot (VBinRel (VEq, div1, VInt zero));
       VBinRel (brel, Read (VVar b_1, x), v1);
       VBinRel (VEq, VVar b__, Write (VVar b_2, y1, VBinOp (VAdd, Read (VVar b_3, y2), v2, _)));
       VBinRel (VEq, VVar b, Write (VVar b__1, x1, VBinOp (VSub, Read (VVar b__2, x2), v3, _)))]
       when is_renamed (fst b_) && is_renamed (fst b__) && not (is_renamed (fst b)) &&
            b_ = b_1 && b_1 = b_2 && b_2 = b_3 &&
            b__ = b__1 && b__1 = b__2 &&
            equal_ve x x1 && equal_ve x1 x2 &&
            equal_ve msgvalue (VVar msg_value) && equal_ve msgvalue1 (VVar msg_value) &&
            equal_ve div div1 && BatBig_int.equal zero BatBig_int.zero &&
            equal_ve v v1 && equal_ve v1 v2 && equal_ve v2 v3 &&
            is_renamed (fst isum_) && not (is_renamed (fst isum)) &&
            is_renamed (fst isum_) && not (is_renamed (fst isum)) &&
            isum_ = isum_1 && isum_1 = isum_2 &&
            (brel = VGeq || brel = VGt)
       -> VAnd (acc, UntrustSum (isum, b))

    | [UntrustSum (isum_, b_);
       VOr (case1, case2);
       VBinRel (brel1, VBinOp (VAdd, VVar isum_1, v, _), VVar isum_2);
       VBinRel (VEq, VVar isum, Ite (VCond (VBinRel (VEq, Read (VVar trust, x), VCond VFalse)),
                                     VBinOp (VAdd, VVar isum_3, v1, _), VVar isum_4));
       VBinRel (brel2, VBinOp (VAdd, Read (VVar b_1, y), v2, _), Read (VVar b_2, y1));
       VBinRel (VEq, VVar b, Write (VVar b_3, y2, VBinOp (VAdd, Read (VVar b_4, y3), v3, _)));
       f]
       when is_renamed (fst b_) && not (is_renamed (fst b)) &&
            b_ = b_1 && b_1 = b_2 && b_2 = b_3 && b_3 = b_4 &&
            equal_ve y y1 && equal_ve y1 y2 && equal_ve y2 y3 &&
            equal_ve v v1 && equal_ve v1 v2 && equal_ve v2 v3 &&
            is_renamed (fst isum_) && not (is_renamed (fst isum)) &&
            isum_ = isum_1 && isum_1 = isum_2 && isum_2 = isum_3 && isum_3 = isum_4 &&
            (brel1 = VGeq || brel1 = VGt) && (brel1 = brel2) &&
            trust = trust_map
       ->
       let true_x = List.exists (fun vf -> match vf with VBinRel (VEq, Read (VVar trust_map, x'), VCond VTrue) when equal_ve x' x -> true | _ -> false) (list_of_conjuncts case1) in
       let true_y = List.exists (fun vf -> match vf with VBinRel (VEq, Read (VVar trust_map, y'), VCond VTrue) when equal_ve y' y -> true | _ -> false) (list_of_conjuncts case1) in
       let false_x = List.exists (fun vf -> match vf with VBinRel (VEq, Read (VVar trust_map, x'), VCond VFalse) when equal_ve x' x -> true | _ -> false) (list_of_conjuncts case2) in
       let false_y = List.exists (fun vf -> match vf with VBinRel (VEq, Read (VVar trust_map, y'), VCond VFalse) when equal_ve y' y -> true | _ -> false) (list_of_conjuncts case2) in
       if true_x && true_y && false_x && false_y then VAnd (acc, UntrustSum (isum, b))
       else acc
    | _ -> acc
  ) vf lst_7

let apply : vformula -> vformula
= fun vf ->
  match vf with
  | Imply (pre,con) ->
    let pre = tactic_3 pre in
    let pre = tactic_4 pre in
    let pre = tactic_3_leak pre in
    let pre = tactic_5_leak pre in
    let pre = tactic_7_leak pre in
    Imply (pre,con)
  | _ -> vf (* VTrue or VFalse *)
