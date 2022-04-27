open Lang
open Vlang
open MakeCfg
open Component
open Path
open InvMap
open Vocab
open Options
open VerifyUtils
open Global

let gen_conjunct ~kind : comps -> vformula list
= fun comps ->
  let mvars = BatSet.to_list comps.mapvars in
  let pairs = BatSet.to_list comps.mapmems in
  let reads = ExpSet.to_list comps.reads in
  let ivars = BatSet.to_list comps.ivars in
  let avars = BatSet.to_list comps.avars in
  let a_arrs = BatSet.to_list comps.a_arrs in
  let a_maps = BatSet.to_list comps.a_maps in
  let bvars = BatSet.to_list comps.bvars in
  let ints = BigIntSet.to_list comps.ints in
  let ivars_mvars = BatList.cartesian_product ivars mvars in
  let ints_mvars = BatList.cartesian_product ints mvars in
  let ivars_ivars = BatList.cartesian_product ivars ivars in
  let ints_ivars = BatList.cartesian_product ints ivars in
  let reads_ivars = BatList.cartesian_product reads ivars in
  let l1 =
    List.fold_left (fun acc ((x,xt),(m,mt)) ->
      if is_uint256 xt then (SigmaEqual ((m,mt), VVar (x,xt)))::acc
      else acc 
    ) [] ivars_mvars in
  let l2 =
    List.fold_left (fun acc (n,(m,t)) ->
      (SigmaEqual ((m,t), VInt n))::acc
    ) [] ints_mvars in
  let l3 =
    List.fold_left (fun acc (m,t) ->
      (NoOverFlow (m,t))::acc
    ) [] mvars in
  let l4 = (* x[y] = z *)
    List.fold_left (fun acc (r, (x,xt)) ->
      if xt = get_typ_vexp r then (VBinRel (VEq, r, VVar (x,xt)))::acc
      else acc
    ) [] reads_ivars in
  let l5 = (* x = y *)
    List.fold_left (fun acc ((x,xt),(y,yt)) ->
      if xt=yt then (VBinRel (VEq, VVar (x,xt), VVar (y,yt)))::acc
      else acc
    ) [] ivars_ivars in
  let l6 = (* x >= y *)
    List.fold_left (fun acc ((x,xt),(y,yt)) ->
      if xt=yt then (VBinRel (VGeq, VVar (x,xt), VVar (y,yt)))::acc
      else acc
    ) [] ivars_ivars in
  let l7 = (* x >= n *)
    List.fold_left (fun acc (n, (y,t)) ->
      (VBinRel (VGeq, VVar (y,t), VInt n))::acc
    ) [] ints_ivars in
  let l8 = (* n = x *)
    List.fold_left (fun acc (n, (y,t)) ->
      (VBinRel (VEq, VVar (y,t), VInt n))::acc
    ) [] ints_ivars in
  let l9 = (* n >= x *)
    List.fold_left (fun acc (n, (y,t)) ->
      (VBinRel (VGeq, VInt n, VVar (y,t)))::acc
    ) [] ints_ivars in
  let l10 = (* @TU[addr] = True *)
    List.fold_left (fun acc (x,t) ->
      (VBinRel (VEq, Read (VVar trust_map, VVar (x,t)), VCond VTrue))::acc
    ) [] avars in
  let l11 =
    List.fold_left (fun acc arr ->
      let bv = ("@i", EType (UInt 256)) in
      (ForAll ([bv], VBinRel (VEq, Read (VVar trust_map, Read (VVar arr, VVar bv)), VCond VTrue)))::acc
    ) [] a_arrs in
  let l12 =
    List.fold_left (fun acc map ->
      let bv = ("@i", EType Address) in
      let owner_trust = VBinRel (VEq, Read (VVar trust_map, VVar bv), VCond VTrue) in
      let parent_trust = VBinRel (VEq, Read (VVar trust_map, Read (VVar map, VVar bv)), VCond VTrue) in
      (ForAll ([bv], Imply (VNot (VBinRel (VEq, Read (VVar map, VVar bv), VInt BatBig_int.zero)),
                            VAnd (owner_trust, parent_trust))))::acc
    ) [] a_maps in
  let l13 =
    List.fold_left (fun acc map ->
      (UntrustSum (invest_sum, map))::acc
    ) [] mvars in
  let l14 =
    List.fold_left (fun acc (s,mem) ->
      (UntrustSum2 (invest_sum, s, mem))::acc
    ) [] pairs in
  let l15 =
    List.fold_left (fun acc (x,t) ->
      (VBinRel (VEq, VVar (x,t), VCond VTrue))::acc
    ) [] bvars in
  let l16 =
    List.fold_left (fun acc (x,t) ->
      (VBinRel (VEq, VVar (x,t), VCond VFalse))::acc
    ) [] bvars in
  let l17 = if List.length bvars > 0 then [VFalse] else [] in
  match kind with
  | "tran" -> l1@l2@l3@l4@l5@l6@l7@l8@l9@l10@l11@l12@l13@l14
    (* [] *)
  | "loop" -> l1@l2@l3@l4@l5@l6@l7@l8@l9@l10@l11@l12@l13@l14@l15@l16
    (* [] *)
  | "ext" -> l1@l2@l3@l4@l5@l6@l7@l8@l9@l10@l11@l12@l13@l14@l15@l16
  | "ext_loop" -> l15@l16@l17
    (* l17 *)
  | "ext_view_pure_loop" -> l15@l16
  | "pre" -> l15@l16
  | _ -> assert false

let next ~kind : comps -> InvMap.key -> InvMap.t -> InvMap.t list
= fun comps key invmap ->
  let old_f = InvMap.find key invmap in
  List.fold_left (fun acc f ->
    let new_f = Simplification.simplify (VAnd (old_f,f)) in
    (InvMap.add key new_f invmap)::acc
  ) [] (gen_conjunct ~kind:kind comps)

let next_tran = next ~kind:"tran"
let next_loop = next ~kind:"loop"
let next_ext = next ~kind:"ext"
let next_ext_loop = next ~kind:"ext_loop"
let next_ext_loop2 = next ~kind:"ext_view_pure_loop"

let next_spec : comps -> SpecMap.key -> SpecMap.t -> SpecMap.t list
= fun comps key specmap ->
  let (old_pre,old_post) = SpecMap.find key specmap in
  List.fold_left (fun acc f ->
    let new_pre = Simplification.simplify (VAnd (old_pre,f)) in
    let new_post = VFalse in
    (SpecMap.add key (new_pre,new_post) specmap)::acc
  ) [] (gen_conjunct ~kind:"pre" comps)

let collect_comps_g : Global.t -> Path2.t -> comps
= fun global path ->
  let fk = Path2.get_fkey path in
  let bp = Path2.get_bp path in
  let cfg = Lang.get_cfg (FuncMap.find fk global.fmap) in
  let comps_bp = collect_bp global bp cfg in
  let lst = List.filter (fun ((cname,fname,_),_) ->
              BatString.equal cname !Options.main_contract
              && BatString.equal cname fname
            ) (BatMap.bindings global.fmap) in
  let _ = assert (List.length lst = 1) in
  let cnstr = snd (List.hd lst) in
  let comps_cnstr = collect_f global cnstr in
  {mapvars = BatSet.filter (fun v -> List.mem v global.gvars) comps_cnstr.mapvars;
   mapmems = BatSet.union comps_cnstr.mapmems comps_bp.mapmems;
   reads = ExpSet.filter (fun ve ->
             let set1 = BatSet.map fst (free_ve ve) in
             let set2 = BatSet.map fst (BatSet.of_list global.gvars) in
             BatSet.subset set1 set2
           ) comps_cnstr.reads;
   ivars = BatSet.filter (fun v -> List.mem v global.gvars) comps_cnstr.ivars;
   avars = BatSet.filter (fun v -> List.mem v global.gvars) comps_cnstr.avars;
   a_arrs = BatSet.filter (fun v -> List.mem v global.gvars) comps_cnstr.a_arrs;
   a_maps = BatSet.filter (fun v -> List.mem v global.gvars) comps_cnstr.a_maps;
   bvars = BatSet.filter (fun v -> List.mem v global.gvars) comps_cnstr.bvars;
   ints = BigIntSet.union comps_cnstr.ints comps_bp.ints}

let refine_tran : Global.t -> PathSet2.t -> InvMap.t -> InvMap.t list
= fun global paths invmap ->
  PathSet2.fold (fun (ctx,(fk,nodes)) acc ->
    let (hd, last) = (BatList.hd nodes, BatList.last nodes) in
    let func = FuncMap.find fk global.fmap in
    let comps_g = collect_comps_g global (ctx,(fk,nodes)) in
    match ctx with
    | None ->
      if (is_public_func func || is_external_func func) && (is_entry hd || is_exit last) then
        let cands = next_tran comps_g (Plain trans_node) invmap in
        cands @ acc
      else acc
    | Some ctx -> acc
  ) paths []

let refine_loop : Global.t -> PathSet2.t -> InvMap.t -> InvMap.t list
= fun global paths invmap ->
  PathSet2.fold (fun (ctx,(fk,nodes)) acc ->
    let (hd, last) = (BatList.hd nodes, BatList.last nodes) in
    let func = FuncMap.find fk global.fmap in
    let cfg = get_cfg func in
    let comps_l = collect_bp global nodes cfg in
    let comps_g = collect_comps_g global (ctx,(fk,nodes)) in
    let extern_node_exists = List.exists (fun n -> is_external_call_node n cfg) nodes in
    match ctx with
    | None ->
      let cand1 = if is_loophead hd cfg then next_loop comps_l (Plain hd) invmap
                  else [] in
      let cand2 = if is_loophead last cfg && extern_node_exists then next_loop comps_g (Plain last) invmap
                  else if is_loophead last cfg then next_loop comps_g (Plain last) invmap
                  else [] in
      cand1 @ cand2 @ acc
    | Some ctx when ctx = Lang.extern_node ->
      let cand1 = if is_loophead hd cfg && is_view_pure_f func then next_ext_loop2 comps_g (Ctx (ctx,hd)) invmap
                  else if is_loophead hd cfg then next_ext_loop comps_g (Ctx (ctx,hd)) invmap
                  else [] in
      let cand2 = if is_loophead hd cfg && is_view_pure_f func then next_ext_loop2 comps_g (Ctx (ctx,hd)) invmap
                  else if is_loophead last cfg && extern_node_exists then next_ext_loop comps_l (Ctx (ctx,last)) invmap
                  else if is_loophead last cfg then next_ext_loop comps_g (Ctx (ctx,last)) invmap
                  else [] in
      cand1 @ cand2 @ acc
    | _ -> acc
  ) paths []

let refine_ext : Global.t -> PathSet2.t -> InvMap.t -> InvMap.t list
= fun global paths invmap ->
  PathSet2.fold (fun (ctx,(fk,nodes)) acc ->
    let (hd, last) = (BatList.hd nodes, BatList.last nodes) in
    let func = FuncMap.find fk global.fmap in
    let cfg = get_cfg func in
    let comps_g = collect_comps_g global (ctx,(fk,nodes)) in
    match ctx with
    | None ->
      let cands1 =
        if (is_public_func func || is_external_func func) && is_external_call_node hd cfg then
          next_ext comps_g (Plain Lang.extern_node) invmap
        else [] in
      let cands2 =
        if (is_public_func func || is_external_func func) && is_external_call_node last cfg then
          next_ext comps_g (Plain Lang.extern_node) invmap
        else [] in
      cands1 @ cands2 @ acc
    | Some ctx when ctx = Lang.extern_node ->
      let cands =
        if (is_public_func func || is_external_func func) && (is_entry hd || is_exit last) then
          next_ext comps_g (Plain ctx) invmap
        else [] in
      cands @ acc
    | _ -> acc
  ) paths []

(* make formulas to 'true' except for some specialized formulas *)
let rec special_only : vformula -> vformula
= fun vf ->
  match vf with
  | VAnd (f1,f2) -> VAnd (special_only f1, special_only f2)
  | SigmaEqual _ | NoOverFlow _ | UntrustSum _ | UntrustSum2 _
  | ForAll _ | VBinRel (VEq,Read (VVar ("@TU",_),_),_) -> vf
  | VOr _ | Imply _ -> assert false
  | _ -> VTrue

let rec make_locks_to_true : vformula -> vformula
= fun vf ->
  match vf with
  | VBinRel (VEq,VVar _,VCond VTrue)
  | VBinRel (VEq,VVar _,VCond VFalse) -> VTrue
  | VAnd (f1,f2) -> VAnd (make_locks_to_true f1, make_locks_to_true f2)
  | VOr _ | Imply _ -> assert false
  | _ -> vf

let rec make_locals_to_true : Global.t -> vformula -> vformula
= fun global vf ->
  match vf with
  | VAnd (f1,f2) -> VAnd (make_locals_to_true global f1, make_locals_to_true global f2)
  | VOr _ | Imply _ -> assert false
  | _ ->
    if BatSet.for_all (fun x -> List.mem x global.gvars || List.mem (fst x) global_ghost_var_names) (free_vf vf) then vf
    else VTrue

let sync' all_cutpoints ext_lhs all_lhs target_lhs target_ext_lhs : Global.t -> InvMap.t -> InvMap.t
= fun global invmap ->
  let invmap = (* loop inv => tran inv (excluding local, locks) *)
    BatSet.fold (fun cp acc ->
      let loop_inv = InvMap.find cp acc in
      let trans_inv = InvMap.find (Plain Lang.trans_node) acc in (* trans_inv may be updated at each iteration *)
      InvMap.add (Plain trans_node) (VAnd (make_locals_to_true global (make_locks_to_true loop_inv), trans_inv)) acc
    ) all_lhs invmap in

  let invmap = (* tran inv => loop inv, extern inv, extern loop inv *)
    let trans_inv = InvMap.find (Plain Lang.trans_node) invmap in
    BatSet.fold (fun cp acc ->
      InvMap.add cp (VAnd (trans_inv, InvMap.find cp invmap)) acc
    ) all_cutpoints invmap in

  let invmap = (* extern loop inv => extern inv *)
    if BatSet.is_empty global.extcalls then invmap
    else
      BatSet.fold (fun cp acc ->
        let ext_loopinv = InvMap.find cp invmap in
        let extern_inv = InvMap.find (Plain Lang.extern_node) acc in
        InvMap.add (Plain Lang.extern_node) (VAnd (extern_inv, ext_loopinv)) acc
      ) ext_lhs invmap in

  let invmap = (* extern inv => tran inv (excluding locks), extern loop inv *)
    if BatSet.is_empty global.extcalls then invmap
    else
      let extern_inv = InvMap.find (Plain extern_node) invmap in
      let invmap = InvMap.add (Plain trans_node)
                     (VAnd (make_locals_to_true global (special_only extern_inv), InvMap.find (Plain trans_node) invmap))
                   invmap in
      BatSet.fold (fun cp acc ->
        InvMap.add cp (VAnd (extern_inv, InvMap.find cp invmap)) acc
      ) (BatSet.union ext_lhs target_lhs) invmap in

  let invmap = (* extern inv with locks => extern loop inv as false *)
    if BatSet.is_empty global.extcalls then invmap
    else
      let extern_inv = InvMap.find (Plain Lang.extern_node) invmap in
      BatSet.fold (fun cp acc ->
        if contain_lock extern_inv then InvMap.add cp VFalse acc
        else acc
      ) target_ext_lhs invmap in
  invmap

let sync : Global.t -> InvMap.t -> InvMap.t list
= fun global invmap ->
  let lhs = BatSet.map (fun l -> Plain l) global.lhs_main in
  let lhs2 = BatSet.map (fun l -> Plain l) global.lhs2_main in
  let lhs3 = BatSet.map (fun l -> Plain l) global.lhs3_main in

  let ext_lhs = if BatSet.is_empty global.extcalls then BatSet.empty else BatSet.map (fun l -> Ctx (Lang.extern_node, l)) global.lhs_main in
  let ext_lhs2 = if BatSet.is_empty global.extcalls then BatSet.empty else BatSet.map (fun l -> Ctx (Lang.extern_node, l)) global.lhs2_main in
  let ext_lhs3 = if BatSet.is_empty global.extcalls then BatSet.empty else BatSet.map (fun l -> Ctx (Lang.extern_node, l)) global.lhs3_main in
  let all_cutpoints = if BatSet.is_empty global.extcalls then (assert (BatSet.is_empty ext_lhs); lhs)
                      else BatSet.add (Plain Lang.extern_node) (BatSet.union ext_lhs lhs) in

  let invmap = InvMap.simplify invmap in
  let invmap1 = sync' all_cutpoints ext_lhs lhs lhs ext_lhs global invmap in
  let invmap2 = sync' all_cutpoints ext_lhs lhs lhs2 ext_lhs2 global invmap in
  let invmap3 = sync' all_cutpoints ext_lhs lhs lhs3 ext_lhs3 global invmap in

  let invmap1 = InvMap.simplify invmap1 in
  let invmap2 = InvMap.simplify invmap2 in
  let invmap3 = InvMap.simplify invmap3 in

  [invmap1; invmap2; invmap3]

let refine_spec : Global.t -> PathSet2.t -> SpecMap.t -> SpecMap.t list
= fun global paths specmap ->
  PathSet2.fold (fun (ctx,(fk,nodes)) acc ->
    let comps_g = collect_comps_g global (ctx,(fk,nodes)) in
    let callnodes = BatSet.map fst global.callnodes in
    let intersect = BatSet.intersect callnodes (BatSet.of_list nodes) in
    BatSet.fold (fun n acc2 ->
      (next_spec comps_g n specmap) @ acc2
    ) intersect acc
  ) paths []

let next_spec : Global.t -> PathSet2.t -> InvMap.t -> SpecMap.t -> (InvMap.t * SpecMap.t) list
= fun global paths invmap specmap ->
  let trans_inv = InvMap.find (Plain Lang.trans_node) invmap in
  let specmap1 = BatSet.fold (fun (cn,fk) acc -> SpecMap.add cn (trans_inv, trans_inv) acc) global.callnodes SpecMap.empty in
  let specmap2 =
    BatSet.fold (fun (cn,fk) acc ->
      let f = FuncMap.find fk global.fmap in
      if contain_extern global f then
        let extern_inv = InvMap.find (Plain Lang.extern_node) invmap in
        if not (contain_lock_s extern_inv (get_body f)) then
          SpecMap.add cn (extern_inv, extern_inv) acc
        else
          SpecMap.add cn (trans_inv, trans_inv) acc
      else
        SpecMap.add cn (trans_inv, trans_inv) acc
    ) global.callnodes SpecMap.empty in
  let specmaps = [specmap1;specmap2] in
  List.map (fun specmap -> (invmap,specmap)) specmaps

(* generate refinements from problematic paths *)
let refine : Global.t -> PathSet2.t -> InvMap.t * SpecMap.t -> (InvMap.t * SpecMap.t) list
= fun global paths (invmap,specmap) ->
  let lst =
    let tran = if !Options.intra then [] else refine_tran global paths invmap in
    let loop = refine_loop global paths invmap in
    let ext = refine_ext global paths invmap in
    tran @ loop @ ext in
  let lst = BatList.unique ~eq:InvMap.equal lst in
  let lst = BatList.fold_lefti (fun acc i map -> acc @ (sync global map)) [] lst in
  (* let _ = List.iter (fun i -> print_endline (InvMap.to_string i)) lst in
  let _ = assert false in *)
  let final = List.fold_left (fun acc map -> acc @ (next_spec global paths map specmap)) [] lst in
  final
