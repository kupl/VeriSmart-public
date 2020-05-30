open Lang
open Vlang
open Report
open Component
open Path
open InvMap
open Model
open Vocab
open ItvDom

let gen_conjunct : comps -> vformula list
= fun comps ->
  let mvars = BatSet.to_list comps.mapvars in
  let reads = ExpSet.to_list comps.composites in
  let ivars = BatSet.to_list comps.ivars in
  let ints = BigIntSet.to_list comps.ints in
  let ivars_mvars = BatList.cartesian_product ivars mvars in
  let ints_mvars = BatList.cartesian_product ints mvars in
  let ivars_ivars = BatList.cartesian_product ivars ivars in
  let ints_ivars = BatList.cartesian_product ints ivars in
  let reads_ivars = BatList.cartesian_product reads ivars in
  let l1 =
    List.fold_left (fun acc ((x,xt),(m,mt)) ->
      if is_uint256 xt then (SigmaEqual (VVar (x,xt), (m,mt)))::acc
      else acc 
    ) [] ivars_mvars in
  let l2 =
    List.fold_left (fun acc (n,(m,t)) ->
      (SigmaEqual (VInt n, (m,t)))::acc
    ) [] ints_mvars in 
  let l3 = 
    List.fold_left (fun acc (m,t) -> 
      (NoOverFlow (m,t))::acc
    ) [] mvars in
  let l4 = (* x = y *)
    List.fold_left (fun acc ((x,xt),(y,yt)) ->
      if xt=yt then (VBinRel (VEq, VVar (x,xt), VVar (y,yt)))::acc
      else acc
    ) [] ivars_ivars in
  let l5 = (* x >= y *)
    List.fold_left (fun acc ((x,xt),(y,yt)) ->
      if xt=yt then (VBinRel (VGeq, VVar (x,xt), VVar (y,yt)))::acc
      else acc
    ) [] ivars_ivars in
  let l6 = (* x >= n *)
    List.fold_left (fun acc (n, (y,t)) ->
      (VBinRel (VGeq, VVar (y,t), VInt n))::acc
    ) [] ints_ivars in
  let l7 = (* n = x *)
    List.fold_left (fun acc (n, (y,t)) ->
      (VBinRel (VEq, VVar (y,t), VInt n))::acc
    ) [] ints_ivars in
  let l8 = (* n >= x *)
    List.fold_left (fun acc (n, (y,t)) ->
      (VBinRel (VGeq, VInt n, VVar (y,t)))::acc
    ) [] ints_ivars in
  let l9 = (* x[y] = z *)
    List.fold_left (fun acc (r, (x,xt)) ->
      if xt = get_type_vexp r then (VBinRel (VEq, r, VVar (x,xt)))::acc
      else acc
    ) [] reads_ivars in
  l1@l2@l3@l4@l5@l6@l7@l8@l9

let next : ModelMap.t -> comps -> comps -> Node.t -> InvMap.t -> InvMap.t list
= fun model_map comps_g comps_l node invmap ->
  let old_f = InvMap.find node invmap in
  let comps = if Node.equal node trans_node then comps_g else comps_l in
  List.fold_left (fun acc f ->
    let new_f = Simplification.simplify (VAnd (old_f,f)) in
    if equal_vf new_f VTrue then acc 
    else
      (InvMap.add node new_f invmap)::acc
  ) [] (gen_conjunct comps)

let refine_bp : Global.t -> Path.t -> ModelMap.t -> InvMap.t -> InvMap.t list
= fun global path model_map invmap ->
  let cutpoints = Path.find_cutpoints global path in
  let cutpoints = if !Options.intra then BatSet.remove Lang.trans_node cutpoints else cutpoints in
  let fk = Path.get_fkey path in
  let bp = Path.get_bp path in
  let cfg = Lang.get_cfg (FuncMap.find fk global.fmap) in
  let comps_bp = collect_comps_bp bp cfg in
  let comps_l = comps_bp in
  let comps_g =
    let lst = List.filter (fun ((cname,fname,_),_) ->
                BatString.equal cname !Options.main_contract &&
                BatString.equal cname fname
              ) (BatMap.bindings global.fmap) in
    let _ = assert (List.length lst = 1) in
    let cnstr = snd (List.hd lst) in
    let comps_cnstr = collect_comps_f cnstr in
      {mapvars = BatSet.filter (fun v -> List.mem v global.gvars) comps_cnstr.mapvars;
       composites = ExpSet.filter (fun e ->
                      match e with
                      | Read (VVar x, VVar y, _) -> List.mem x global.gvars && List.mem y global.gvars
                      | _ -> assert false
                   ) comps_cnstr.composites;
       ivars = BatSet.filter (fun v -> List.mem v global.gvars) comps_cnstr.ivars;
       avars = BatSet.filter (fun v -> List.mem v global.gvars) comps_cnstr.avars;
       ints = BigIntSet.union comps_cnstr.ints comps_bp.ints}
  in
  BatSet.fold (fun node acc ->
    let newmaps = next model_map comps_g comps_l node invmap in
    acc @ newmaps
  ) cutpoints []

let sync_loopinv : Node.t BatSet.t -> InvMap.t -> InvMap.t
= fun lhs invmap ->
  let trans_inv = InvMap.find Lang.trans_node invmap in
  if equal_vf trans_inv VTrue then invmap
  else
    BatSet.fold (fun lh acc ->
      let vf = (VAnd (trans_inv, InvMap.find lh invmap)) in
      InvMap.add lh vf acc 
    ) lhs invmap

(* generate refinements from problematic paths *)
let refine : Global.t -> PathSet.t -> ModelMap.t -> InvMap.t -> InvMap.t list
= fun global paths model_map invmap ->
  let lhs = global.lhs in
  let lst =
  PathSet.fold (fun path acc ->
    (refine_bp global path model_map invmap) @ acc
  ) paths [] in
  List.map (sync_loopinv lhs) lst
