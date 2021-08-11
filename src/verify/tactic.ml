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
                | _ -> false
              ) flst in
  let flst3 = List.filter (fun vf ->
                match vf with
                | VBinRel (VEq, VVar _, VInt _) -> true
                | VBinRel (VGeq, VInt _, VVar _) -> true
                | VBinRel (VEq, VVar _, Write (VVar _, x, VBinOp (VSub, Read (VVar _, x1,_), v, _))) -> equal_ve x x1
                | VBinRel (VEq, VVar _, Write (VVar _, x, VBinOp (VAdd, Read (VVar _, x1,_), v, _))) -> equal_ve x x1
                | _ -> false
              ) flst in
  let flst4 = List.filter (fun vf ->
                match vf with
                | VBinRel (VGeq, Read (VVar _,_,_), _) -> true
                | VBinRel (VEq, VVar _, Write (VVar _, x, VBinOp (VSub, Read (VVar _, x1,_), v, _))) -> equal_ve x x1
                | VBinRel (VEq, VVar _, Write (VVar _, x, VBinOp (VAdd, Read (VVar _, x1,_), v, _))) -> equal_ve x x1
                | _ -> false
              ) flst in
  BatList.n_cartesian_product [flst1;flst2;flst3;flst4]

let cartesian_5 : vformula list -> vformula list list
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

let cartesian_6 : vformula list -> vformula list list
= fun flst ->
  let flst1 = List.filter (fun vf -> match vf with NoOverFlow _ -> true | _ -> false) flst in
  let flst2 = List.filter (fun vf -> match vf with SigmaEqual _ -> true | _ -> false) flst in
  let flst3 = List.filter (fun vf -> match vf with VBinRel (VGeq,VInt _,VVar _) | VBinRel (VEq,VVar _,VInt _) -> true | _ -> false) flst in
  let flst4 = List.filter (fun vf -> match vf with VBinRel (VGeq, Read (VVar _, VVar _, _), VVar _) -> true | _ -> false) flst in
  let flst5 = List.filter (fun vf -> match vf with VBinRel (VEq, VVar _, Write (VVar _, VVar _, VBinOp (VSub, Read (VVar _, VVar _,_), VVar _, _))) -> true | _ -> false) flst in
  let flst6 = List.filter (fun vf -> match vf with VBinRel (VEq, VVar _, Write (VVar _, VVar _, VBinOp (VAdd, Read (VVar _, VVar _,_), VVar _, _))) -> true | _ -> false) flst in
  BatList.n_cartesian_product [flst1;flst2;flst3;flst4;flst5;flst6]

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
       VBinRel (VEq, VVar (b__,_), Write (VVar (b_1,_), x, VBinOp (VSub, Read (VVar (b_2,_), x1,_), v, _)));
       VBinRel (VEq, VVar (b,_), Write (VVar (b__1,_), y, VBinOp (VAdd, Read (VVar (b__2,_), y1,_), v1, _)))]
       when is_renamed b_ && is_renamed b__ && not (is_renamed b) &&
            BatString.equal b_ b_1 && BatString.equal b_1 b_2 &&
            BatString.equal b__ b__1 && BatString.equal b__1 b__2 &&
            equal_ve x x1 && equal_ve y y1 &&
            equal_ve v v1
       -> VAnd (acc, SigmaEqual ((b,typ), total))

    | [SigmaEqual ((b_,typ), total);
       VBinRel (VEq, VVar (b__,_), Write (VVar (b_1,_), x, VBinOp (VAdd, Read (VVar (b_2,_), x1,_), v, _)));
       VBinRel (VEq, VVar (b,_), Write (VVar (b__1,_), y, VBinOp (VSub, Read (VVar (b__2,_), y1,_), v1, _)))]
       when is_renamed b_ && is_renamed b__ && not (is_renamed b) &&
            BatString.equal b_ b_1 && BatString.equal b_1 b_2 &&
            BatString.equal b__ b__1 && BatString.equal b__1 b__2 &&
            equal_ve x x1 && equal_ve y y1 &&
            equal_ve v v1
       -> VAnd (acc, SigmaEqual ((b,typ), total))

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
       VBinRel (brel, Read (VVar (b_1,_), x, _), v);
       VBinRel (VEq, VVar (b__,_), Write (VVar (b_2,_), x1, VBinOp (VSub, Read (VVar (b_3,_), x2,_), v1, _)));
       VBinRel (VEq, VVar (b,_), Write (VVar (b__1,_), y, VBinOp (VAdd, Read (VVar (b__2,_), y1,_), v2, _)))]
       when is_renamed b_ && is_renamed b__ && not (is_renamed b) &&
            BatString.equal b_ b_1 && BatString.equal b_1 b_2 && BatString.equal b_2 b_3 &&
            BatString.equal b__ b__1 && BatString.equal b__1 b__2 &&
            equal_ve x x1 && equal_ve x1 x2 &&
            equal_ve y y1 &&
            equal_ve v v1 && equal_ve v1 v2 &&
            (brel = VGeq || brel = VGt)
       -> VAnd (acc, NoOverFlow (b, typ))
    | [NoOverFlow (b_, typ);
       VBinRel (brel, Read (VVar (b_1,_), x, _), v);
       VBinRel (VEq, VVar (b__,_), Write (VVar (b_2,_), y, VBinOp (VAdd, Read (VVar (b_3,_), y1,_), v1, _)));
       VBinRel (VEq, VVar (b,_), Write (VVar (b__1,_), x1, VBinOp (VSub, Read (VVar (b__2,_), x2,_), v2, _)))]
       when is_renamed b_ && is_renamed b__ && not (is_renamed b) &&
            BatString.equal b_ b_1 && BatString.equal b_1 b_2 && BatString.equal b_2 b_3 &&
            BatString.equal b__ b__1 && BatString.equal b__1 b__2 &&
            equal_ve x x1 && equal_ve x1 x2 &&
            equal_ve y y1 &&
            equal_ve v v1 && equal_ve v1 v2 &&
            (brel = VGeq || brel = VGt)
       -> VAnd (acc, NoOverFlow (b, typ))
    | _ -> acc
  ) vf lst_4

let apply : vformula -> vformula
= fun vf ->
  match vf with
  | Imply (pre,con) ->
    let pre = tactic_3 pre in
    let pre = tactic_4 pre in
    Imply (pre,con)
  | _ -> vf (* VTrue or VFalse *)
