open Lang
open Vlang
open Report
open Component
open Path
open InvMap
open Model
open Vocab
open ItvDom
open Options

let gen_conjunct : comps -> vformula list
= fun comps ->
  let mvars = BatSet.to_list comps.mapvars in
  let reads = ExpSet.to_list comps.reads in
  let ivars = BatSet.to_list comps.ivars in
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
      if xt = get_type_vexp r then (VBinRel (VEq, r, VVar (x,xt)))::acc
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
  l1@l2@l3@l4@l5@l6@l7@l8@l9

let next : comps -> Node.t -> InvMap.t -> InvMap.t list
= fun comps node invmap ->
  let old_f = InvMap.find node invmap in
  List.fold_left (fun acc f ->
    let new_f = Simplification.simplify (VAnd (old_f,f)) in
    if equal_vf new_f VTrue then acc
    else
      (InvMap.add node new_f invmap)::acc
  ) [] (gen_conjunct comps)

let collect_comps_g : Global.t -> Path.t -> comps
= fun global path ->
  let fk = Path.get_fkey path in
  let bp = Path.get_bp path in
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
   reads = ExpSet.filter (fun ve ->
             let set1 = BatSet.map fst (free_ve ve) in
             let set2 = BatSet.map fst (BatSet.of_list global.gvars) in
             BatSet.subset set1 set2
           ) comps_cnstr.reads;
   ivars = BatSet.filter (fun v -> List.mem v global.gvars) comps_cnstr.ivars;
   avars = BatSet.filter (fun v -> List.mem v global.gvars) comps_cnstr.avars;
   ints = BigIntSet.union comps_cnstr.ints comps_bp.ints}

let refine_tran : Global.t -> PathSet.t -> InvMap.t -> InvMap.t list
= fun global paths invmap ->
  PathSet.fold (fun (fk,nodes) acc ->
    let (hd, last) = (BatList.hd nodes, BatList.last nodes) in
    let func = FuncMap.find fk global.fmap in
    let comps_g = collect_comps_g global (fk,nodes) in
    if (is_public_func func || is_external_func func) && (is_entry hd || is_exit last) then
      let cands = next comps_g Lang.trans_node invmap in
      cands @ acc
    else acc
  ) paths []

let refine_loop : Global.t -> PathSet.t -> InvMap.t -> InvMap.t list
= fun global paths invmap ->
  PathSet.fold (fun (fk,nodes) acc ->
    let (hd, last) = (BatList.hd nodes, BatList.last nodes) in
    let func = FuncMap.find fk global.fmap in
    let cfg = get_cfg func in
    let comps_l = collect_bp global nodes cfg in
    let cand1 = if is_loophead hd cfg then next comps_l hd invmap else [] in
    let cand2 = if is_loophead last cfg then next comps_l last invmap else [] in
    cand1 @ cand2 @ acc
  ) paths []

let sync : Global.t -> PathSet.t -> InvMap.t -> InvMap.t
= fun global paths invmap ->
  let lhs = global.lhs in
  let trans_inv = InvMap.find Lang.trans_node invmap in
  if equal_vf trans_inv VTrue then invmap
  else
    BatSet.fold (fun lh acc ->
      InvMap.add lh (VAnd (trans_inv, InvMap.find lh invmap)) acc
    ) lhs invmap

(* generate refinements from problematic paths *)
let refine : Global.t -> PathSet.t -> InvMap.t -> InvMap.t list
= fun global paths invmap ->
  let lst =
    (if !Options.intra then [] else refine_tran global paths invmap) @
    (refine_loop global paths invmap) in
  List.map (sync global paths) lst
