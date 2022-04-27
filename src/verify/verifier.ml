open Lang
open Vlang
open MakeCfg
open Query 
open Vocab
open Report
open Semantics
open Component
open Synthesizer
open InvMap
open Path
open ItvDom
open Itv
open Z3Interface
open Model
open Simplification
open Profiler
open Options
open VerifyUtils
open Global

let is_cnstr_path : Global.t -> Path.t -> bool
= fun global path -> is_constructor (FuncMap.find (Path.get_fkey path) global.fmap)

let make_extern_paths : Global.t -> PathSet.t -> PathSet2.t
= fun global paths ->
  let init = PathSet2.of_list (List.map (fun p -> (None,p)) (PathSet.to_list paths)) in
  let paths = PathSet.filter (fun p -> not (is_cnstr_path global p)) paths in
  let paths = PathSet.to_list paths in
  let vpaths = if BatSet.is_empty global.extcalls then PathSet2.empty else PathSet2.of_list (List.map (fun p -> (Some Lang.extern_node, p)) paths) in
  PathSet2.union init vpaths

let make_call_paths' : (Node.t * fkey) -> PathSet.t -> PathSet2.t
= fun (node,fkey) paths ->
  let paths = PathSet.filter (fun p -> fkey = get_fkey p) paths in
  let paths = PathSet.to_list paths in
  let cpaths = PathSet2.of_list (List.map (fun p -> (Some node, p)) paths) in
  cpaths

let make_call_paths : Global.t -> PathSet.t -> PathSet2.t
= fun global paths ->
  BatSet.fold (fun cn acc ->
    let paths' = make_call_paths' cn paths in
    PathSet2.union paths' acc
  ) global.callnodes PathSet2.empty

let augment_paths : Global.t -> PathSet.t -> PathSet2.t
= fun global paths ->
  let extern_paths = make_extern_paths global paths in
  let call_paths = make_call_paths global paths in
  PathSet2.union call_paths extern_paths

let pre_of_internal : Global.t -> InvMap.t -> func -> vformula
= fun global invmap f ->
  let _ = assert (is_internal_func f || is_private_func f) in
  let trans_inv = InvMap.find (Plain Lang.trans_node) invmap in
  if BatSet.is_empty global.extcalls || is_view_pure_f f then trans_inv
  else if contain_extern global f then InvMap.find (Plain Lang.extern_node) invmap
  else trans_inv

let post_of_internal : Global.t -> InvMap.t -> func -> vformula
= fun global invmap f ->
  let _ = assert (is_internal_func f || is_private_func f) in
  let trans_inv = InvMap.find (Plain Lang.trans_node) invmap in
  if BatSet.is_empty global.extcalls || is_view_pure_f f then trans_inv
  else if contain_extern global f then InvMap.find (Plain Lang.extern_node) invmap
  else trans_inv

let pre_of_internal2 : Global.t -> InvMap.t -> func -> vformula
= fun global invmap f ->
  let _ = assert (is_internal_func f || is_private_func f) in
  (* let trans_inv = InvMap.find (Plain Lang.trans_node) invmap in *)
  let extern_inv = InvMap.find (Plain Lang.extern_node) invmap in
  if is_view_pure_f f then extern_inv
  else if contain_lock extern_inv then VFalse
  else extern_inv

let post_of_internal2 : Global.t -> InvMap.t -> func -> vformula
= fun global invmap f ->
  let _ = assert (is_internal_func f || is_private_func f) in
  (* let trans_inv = InvMap.find (Plain Lang.trans_node) invmap in *)
  let extern_inv = InvMap.find (Plain Lang.extern_node) invmap in
  if is_view_pure_f f then extern_inv
  else if contain_lock extern_inv then VFalse
  else extern_inv

let pre_of_public_at_call : Global.t -> InvMap.t -> SpecMap.t -> func -> Node.t -> vformula
= fun global invmap specmap f callnode ->
  let _ = assert (is_public_func f || is_external_func f) in
  let trans_inv = InvMap.find (Plain Lang.trans_node) invmap in
  if not (is_view_pure_f f) then SpecMap.find_pre callnode specmap
  else trans_inv

let post_of_public_at_call : Global.t -> InvMap.t -> SpecMap.t -> func -> Node.t -> vformula
= fun global invmap specmap f callnode ->
  let _ = assert (is_public_func f || is_external_func f) in
  let trans_inv = InvMap.find (Plain Lang.trans_node) invmap in
  if not (is_view_pure_f f) then SpecMap.find_post callnode specmap
  else trans_inv

let post_of_public2 : Global.t -> InvMap.t -> func -> vformula
= fun global invmap f ->
  let _ = assert (is_public_func f || is_external_func f) in
  let extern_inv = InvMap.find (Plain Lang.extern_node) invmap in
  if contain_lock extern_inv && contain_lock_s extern_inv (get_body f) then VFalse
  else extern_inv

let intcall_semantics ctx global invmap specmap callee node =
  match ctx with
  | Some n when n = Lang.extern_node ->
    if is_public_func callee || is_external_func callee then post_of_public2 global invmap callee
    else post_of_internal2 global invmap callee
  | None | Some _ ->
    if is_public_func callee || is_external_func callee then post_of_public_at_call global invmap specmap callee node
    else post_of_internal global invmap callee

let invalidate_ret lvop vf =
  match lvop with
  | None -> vf
  | Some lv ->
    let def = BatSet.to_list (FuncDefUse.get_def_set_lv lv) in
    weaken_vf2 vf def

let handle_internal_call ctx global invmap specmap callee lvop vf node =
  (* 1. remove terms that include variables which may be modified in callee *)
  let k = Lang.get_fkey callee in
  let vf = weaken_vf2 vf (BatSet.to_list (FuncDefUse.find_def_set k global.f_defuse)) in
  (* 2. conjoin with transaction/external call-site invariant *)
  let post = intcall_semantics ctx global invmap specmap callee node in
  let vf = VAnd (vf, post) in
  (* 3. if lv exists, replace target var by true *)
  let final = invalidate_ret lvop vf in
  final

let get_cond_at_cutpoint : Global.t -> InvMap.t -> SpecMap.t -> func -> Path2.t -> Node.t -> vformula
= fun global invmap specmap func (nop,path) node ->
  let cfg = get_cfg func in
  match nop with
  | None ->
    if is_loophead node cfg then InvMap.find (Plain node) invmap
    else
      let cname = (get_finfo func).scope_s in
      let trans_inv = InvMap.find (Plain Lang.trans_node) invmap in
      if BatString.equal cname !main_contract then
        if is_entry node && is_constructor func then VTrue else
        if is_entry node && (is_public_func func || is_external_func func) then trans_inv else
        if is_exit node && (is_public_func func || is_external_func func) then trans_inv else
        if is_entry node && (is_internal_func func || is_private_func func) then pre_of_internal global invmap func else
        if is_exit node && (is_internal_func func || is_private_func func) then post_of_internal global invmap func else
        if is_external_call_node node cfg then InvMap.find (Plain Lang.extern_node) invmap else
        if is_internal_call_node global.fmap global.cnames node cfg then
          let callee = get_callee_of_intcall global func (find_stmt node cfg) in
          if is_public_func callee || is_external_func callee then
            pre_of_public_at_call global invmap specmap callee node
          else pre_of_internal global invmap callee
        else failwith "get_cond_at_cutpoint : not a cutpoint !"
      else VTrue (* functions not in a main contract *)
  | Some ctx when ctx = Lang.extern_node -> (* external context *)
    let extern_inv = InvMap.find (Plain ctx) invmap in
    if is_loophead node cfg then InvMap.find (Ctx (ctx,node)) invmap
    else
      let cname = (get_finfo func).scope_s in
      if BatString.equal cname !main_contract then
        if is_entry node && is_constructor func then assert false else
        if is_entry node && (is_public_func func || is_external_func func) then extern_inv else
        if is_exit node && (is_public_func func || is_external_func func) then post_of_public2 global invmap func else
        if is_entry node && (is_internal_func func || is_private_func func) then pre_of_internal2 global invmap func else
        if is_exit node && (is_internal_func func || is_private_func func) then post_of_internal2 global invmap func else
        if is_external_call_node node cfg then extern_inv else
        if is_internal_call_node global.fmap global.cnames node cfg then
          let callee = get_callee_of_intcall global func (find_stmt node cfg) in
          if is_public_func callee || is_external_func callee then extern_inv
          else pre_of_internal2 global invmap callee
        else failwith "get_cond_at_cutpoint : not a cutpoint !"
      else VTrue (* functions not in a main contract *)
  | Some ctx -> (* static call context *)
    if is_loophead node cfg then SpecMap.find_post ctx specmap
    else
      let cname = (get_finfo func).scope_s in
      (* if BatString.equal cname !main_contract then *)
      if List.mem cname global.base_names then
        if is_entry node && is_constructor func then assert false else
        if is_entry node && (is_public_func func || is_external_func func) then SpecMap.find_pre ctx specmap else
        if is_exit node && (is_public_func func || is_external_func func) then SpecMap.find_post ctx specmap else
        if is_entry node && (is_internal_func func || is_private_func func) then assert false else
        if is_exit node && (is_internal_func func || is_private_func func) then assert false else
        if is_external_call_node node cfg then InvMap.find (Plain Lang.extern_node) invmap else
        if is_internal_call_node global.fmap global.cnames node cfg then
          let callee = get_callee_of_intcall global func (find_stmt node cfg) in
          if is_public_func callee || is_external_func callee then
            pre_of_public_at_call global invmap specmap callee node
          else pre_of_internal global invmap callee (* not 'pre_of_internal2' ! *)
        else failwith "get_cond_at_cutpoint : not a cutpoint !"
      else VTrue (* functions not in a main contract *)


let tu_each ve tf =
  match get_typ_vexp ve with
  | EType Address -> VBinRel (VEq, Read (VVar trust_map, ve), tf)
  | Array (EType Address,_) ->
    let bv = ("@i", EType (UInt 256)) in
    ForAll ([bv], VBinRel (VEq, Read (VVar trust_map, Read (ve, VVar bv)), tf))
  | _ -> assert false

let all_trusted : vexp list -> vformula
= fun vexps ->
  List.fold_left (fun acc ve ->
    let f = tu_each ve (VCond VTrue) in
    if equal_vf f VTrue then f
    else VAnd (acc,f)
  ) VTrue vexps

let all_untrusted : vexp list -> vformula
= fun vexps ->
  List.fold_left (fun acc ve ->
    let f = tu_each ve (VCond VFalse) in
    if equal_vf f VTrue then f
    else VAnd (acc,f)
  ) VTrue vexps

let is_addr_or_addr_array (_,typ) =
  match typ with
  | EType Address | Array (EType Address,_) -> true
  | _ -> false

let get_addr_related_params : var list -> var list
= fun vars -> List.filter is_addr_or_addr_array vars

let trusted_user_constraint : Global.t -> func -> Path.t -> Node.t -> vformula -> vformula
= fun global func path node vf ->
  let params = List.map (fun (v,vinfo) -> (v,vinfo.vtyp)) (Lang.get_params func) in
  let addr_params = List.map (fun v -> VVar v) (get_addr_related_params params) in
  let hc_addrs1 = List.map (fun n -> VCast (EType Address, VInt n)) (BigIntSet.to_list global.hc_addrs) in
  let hc_addrs2 = List.filter (fun v -> is_address (snd v) && is_constant_address global v) global.gvars in
  let hc_addrs2 = List.map (fun v -> VVar v) hc_addrs2 in
  let hc_addrs = hc_addrs1 @ hc_addrs2 in
  let trusted_base = [VVar this_addr; VCast (EType Address, VInt BatBig_int.zero)] @ hc_addrs in
  if is_constructor func && is_entry node then
    let t = all_trusted ((VVar msg_sender)::(addr_params @ trusted_base)) in
    VAnd (vf, t)
  else if is_entry node then
    let t' = all_trusted trusted_base in
    let t = all_trusted ((VVar msg_sender)::addr_params) in
    let u = all_untrusted ((VVar msg_sender)::addr_params) in
    VAnd (vf, VAnd (t', VOr (t,u)))
  else if is_loophead node (get_cfg func) then
    let t = all_trusted trusted_base in
    VAnd (vf, t)
  else assert false

let init_invest_if_cnstr : func -> vformula
= fun func ->
  if is_constructor func then
    VAnd (ForAll ([("@i", EType Address)], VBinRel (VEq, Read (VVar invest_map, VVar ("@i", EType Address)), VInt BatBig_int.zero)),
      VBinRel (VEq, VVar invest_sum, VCast (EType (UInt 256), VInt BatBig_int.zero)))
  else VTrue

let inc_invest_if_payable : bool -> func -> vformula -> vformula
= fun is_entry func vf ->
  if is_payable func && is_entry then
    (* Invest[msg.sender] := Invest[msg.sender] + msg.value *)
    (* Invest_sum := if (untrusted) Invest_sum + msg.value else Invest_sum *)
    let target1, target2 = VVar invest_map, VVar invest_sum in
    let rep1, rep2 = rename target1, rename target2 in
    let ve1, ve2 =
      Write (target1, VVar msg_sender, VBinOp (VAdd, Read (target1, VVar msg_sender), VVar msg_value, EType (UInt 256))),
      VBinOp (VAdd, target2, VVar msg_value, EType (UInt 256)) in
    let vf' = rewrite_vf (rewrite_vf vf target1 rep1) target2 rep2 in
    let ve1', ve2' = rewrite_ve ve1 target1 rep1, rewrite_ve ve2 target2 rep2 in
    let ite = Ite (VCond (VBinRel (VEq, Read (VVar trust_map, VVar msg_sender), VCond VFalse)), ve2', rep2) in
    let test = VBinRel (VGeq, VBinOp (VAdd, rep2, VVar msg_value, EType (UInt 256)), rep2) in
    VAnd (test,
      VAnd (vf', VAnd (VBinRel (VEq, target1, ve1'), VBinRel (VEq, target2, ite))))
  else vf

let investor_constraint : bool -> func -> vformula -> vformula
= fun is_entry func vf ->
  let vf = VAnd (vf, init_invest_if_cnstr func) in
  let vf = inc_invest_if_payable is_entry func vf in
  vf

let this_sender_eq_possible : vformula -> vformula
= fun vf ->
  if !PatternAnalysis.may_call_itself then vf
  else VAnd (vf, VNot (VBinRel (VEq, VVar this_addr, VVar msg_sender)))

let calldata_length : func -> vformula
= fun func ->
  let typs = List.map (fun (_,info) -> info.vtyp) (get_params func) in
  let b = List.for_all (fun t -> is_uintkind t || is_sintkind t || is_address t || is_bool t) typs in
  if b then
    let size = 4 + (List.length typs * 32) in (* 4 bytes for function signature + #arg * 32  *)
    VBinRel (VEq, VVar ("msg.data.length", EType (UInt 256)), VInt (BatBig_int.of_int size))
  else VTrue

let get_startf_endf : Global.t -> InvMap.t -> SpecMap.t -> Path2.t -> vformula * vformula
= fun global invmap specmap vpath ->
  let path = snd vpath in
  let bp = Path.get_bp path in
  let func = FuncMap.find (Path.get_fkey path) global.fmap in
  let cfg = get_cfg func in
  let (start, mid, last) = (BatList.hd bp, Path.get_mid bp, BatList.last bp) in
  let _ = assert (is_entry start || is_loophead start cfg) in
  let _ = assert (is_exit last || is_loophead last cfg || is_internal_call_node global.fmap global.cnames last cfg || is_external_call_node last cfg) in
  (* formula at starting node *)
  let startf = get_cond_at_cutpoint global invmap specmap func vpath start in
  let startf = Label (1,startf) in
  let startf = trusted_user_constraint global func path start startf in
  let startf = investor_constraint (is_entry start) func startf in
  let startf = this_sender_eq_possible startf in
  let startf = VAnd (startf, calldata_length func) in
  (* formula at end node *)
  let endf = get_cond_at_cutpoint global invmap specmap func vpath last in
  let endf = Label (1,endf) in
  (startf, endf)

let finalize_safety_cond : vformula -> query list -> query list
= fun state qs ->
  List.map (fun q ->
    {q with vc2 = match q.vc2 with Imply _ -> q.vc2 | _ -> Imply (state, q.vc2)}
  ) qs

let convert_stmt ctx invmap specmap : Global.t -> func -> Node.t -> vformula * query list -> vformula * query list
= fun global curf node (vf,qs) ->
  let stmt = find_stmt node (Lang.get_cfg curf) in
  match stmt with
  | Call (lvop,e,args,ethop,gasop,loc,_) when is_internal_call global.fmap global.cnames stmt ->
    let _ = assert (no_eth_gas_modifiers stmt) in
    let qs' = finalize_safety_cond vf qs in (* delayed safety checking for internal calls *)
    let callee = get_callee_of_intcall global curf stmt in
    let vf' = handle_internal_call ctx global invmap specmap callee lvop vf node in
    (vf', qs')

  | Call _ when is_external_call_node node (Lang.get_cfg curf) ->
    let defset = List.fold_left (fun acc (fk,(defs,_,_)) ->
                   if is_constructor (FuncMap.find fk global.fmap) then acc
                   else BatSet.union defs acc
                 ) BatSet.empty (FuncDefUse.bindings global.f_defuse) in
    let fields = Global.get_all_fields global in
    let field_names = List.map fst fields in
    let g_defs = BatSet.filter (fun d -> List.mem d (List.map fst global.gvars) (* global variables *)
                                         || d = "@Invest_sum"                   (* may be altered in payable *)
                                         || List.mem d field_names              (* structure fields *)
                 ) defset in
    (* let _ = print_endline "" in
    let _ = print_endline (string_of_set Vocab.id defset) in
    let _ = print_endline (string_of_list Vocab.id field_names) in
    let _ = print_endline (string_of_set Vocab.id g_defs) in *)
    let qs' = finalize_safety_cond vf qs in (* delayed safety checking for external calls *)
    let vf' = List.fold_left weaken_vf vf (BatSet.to_list g_defs) in
    let vf' = VAnd (vf', InvMap.find (InvMap.Plain Lang.extern_node) invmap) in
    (vf', qs')

  | _ -> convert_stmt global curf node (vf,qs)

let gen_vc : Global.t -> InvMap.t -> SpecMap.t -> PathSet2.t -> vformula * vformula -> Path2.t -> vformula * query list
= fun global invmap specmap vpaths (startf,endf) (ctx,path) ->
  let mid = Path.get_bp path |> Path.get_mid in
  let func = FuncMap.find (Path.get_fkey path) global.fmap in
  let cfg = get_cfg func in
  let extern_ctx = match ctx with Some n -> n = Lang.extern_node | _ -> false in
  let (sp, qs) =
    List.fold_left (fun (acc_vf, acc_qs) node ->
      let new_qs = CollectQuery2.collect ~extern_ctx:extern_ctx global cfg acc_vf path node in
      convert_stmt ctx invmap specmap global func node (acc_vf, acc_qs @ new_qs)
    ) (startf, []) mid in
  let qs = finalize_safety_cond sp qs in
  let formula = Imply (sp, endf) in
  (formula, qs)

let rec get_all_vcs : Global.t -> InvMap.t -> SpecMap.t -> PathSet2.t ->
                      (Path2.t * vformula) list * (Path2.t * query) list
= fun global invmap specmap vpaths ->
  PathSet2.fold (fun vpath (acc_vc,acc_qs) ->
    let (startf, endf) = get_startf_endf global invmap specmap vpath in
    let (vc',qs') = gen_vc global invmap  specmap vpaths (startf,endf) vpath in
    let qs' = List.map (fun q' -> (vpath,q')) qs' in
    (acc_vc @ [(vpath,vc')], qs'@acc_qs)
  ) vpaths ([],[])

let get_numeric_info : Loc.t BatSet.t -> ItvDom.Mem.t -> vformula
= fun locs mem ->
  Mem.fold (fun (id,t) v acc ->
    let itv = Val.itv_of v in
    (* interval values, propagated to
     * non-numerical typed variables, should not be reflected *)
    if Itv.is_top itv || not (is_uintkind t) then acc else
    if not (BatSet.mem (id,t) locs) then acc
    else
      (match itv with
       | Itv (V l, V u) when BatBig_int.equal l u ->
         let f = VBinRel (VEq, VVar (id,t), VInt u) in
         VAnd (acc,f)
       | Itv (V l, V u) ->
         let f1 = VBinRel (VGeq, VInt u, VVar (id,t)) in
         let f2 = VBinRel (VGeq, VVar (id,t), VInt l) in
         VAnd (acc, VAnd (f1,f2))
       | _ -> acc) 
  ) mem VTrue

(* get numeric lenth informaion *)
let get_numeric_info2 : ItvDom.Mem.t -> ExpSet.t -> vformula
= fun mem len_exps ->
  let v = Mem.find ("length", EType (UInt 256)) mem in
  let itv = Val.itv_of v in
  match itv with
  | Itv (V l, V u) when BatBig_int.equal l u ->
    ExpSet.fold (fun e acc ->
      let r = VBinRel (VEq, e, VInt u) in
      if equal_vf acc VTrue then r
      else VAnd (acc, r)
    ) len_exps VTrue
  | _ -> VTrue

let rec collect_len_exp : vformula -> ExpSet.t
= fun vf ->
  match vf with
  | Imply (f1,f2) -> ExpSet.union (collect_len_exp f1) (collect_len_exp f2)
  | VAnd (f1,f2) -> ExpSet.union (collect_len_exp f1) (collect_len_exp f2)
  | VNot f -> collect_len_exp f
  | VBinRel (_,e1,e2) -> ExpSet.union (collect_len_exp_e e1) (collect_len_exp_e e2)
  | _ -> ExpSet.empty

and collect_len_exp_e : vexp -> ExpSet.t
= fun ve ->
  match ve with
  | VBinOp (_,e1,e2,_) -> ExpSet.union (collect_len_exp_e e1) (collect_len_exp_e e2)
  | Read (VVar ("length",t), VVar _) -> ExpSet.singleton ve
  | _ -> ExpSet.empty

let add_numeric_info : ItvDom.Mem.t -> vformula -> vformula 
= fun mem vf ->
  match vf with
  | Imply (pre,con) ->
    let locs = BatSet.union (free_vf pre) (free_vf con) in
    let len_exps = collect_len_exp vf in
    let f1 = get_numeric_info locs mem in
    let f2 = get_numeric_info2 mem len_exps in
    Imply (VAnd (pre,VAnd (f1,f2)), con)
  | _ -> assert false

let rec addrs_vf : vformula -> ExpSet.t
= fun vf ->
  match vf with
  | VTrue | VFalse -> ExpSet.empty
  | VNot f -> addrs_vf f
  | VAnd (f1,f2) | VOr (f1,f2) -> ExpSet.union (addrs_vf f1) (addrs_vf f2)
  | VBinRel (_,e1,e2) -> ExpSet.union (addrs_ve e1) (addrs_ve e2)
  | Imply (f1,f2) -> ExpSet.union (addrs_vf f1) (addrs_vf f2)
  | SigmaEqual _ | NoOverFlow _ | UntrustSum _ | UntrustSum2 _ -> ExpSet.empty
  | ForAll (bvs,f) ->
    let bvset = ExpSet.of_list (List.map (fun bv -> VVar bv) bvs) in
    ExpSet.diff (addrs_vf f) bvset
  | Label (_,f) -> addrs_vf f

and addrs_ve : vexp -> ExpSet.t
= fun ve ->
  match ve with
  | VInt _ -> ExpSet.empty
  | VVar v ->
    if is_address (snd v) then ExpSet.singleton ve else ExpSet.empty
  | Read (e1,e2) ->
    let union = ExpSet.union (addrs_ve e1) (addrs_ve e2) in
    if is_address (get_typ_vexp ve) then ExpSet.add ve union
    else union
  | Write (e1,e2,e3) ->
    ExpSet.union (addrs_ve e1) (ExpSet.union (addrs_ve e2) (addrs_ve e3))
  | VBinOp (bop,e1,e2,typ) ->
    let union = ExpSet.union (addrs_ve e1) (addrs_ve e2) in
    if is_address typ then ExpSet.add ve union
    else union
  | VUnOp (uop,e,typ) ->
    if is_address typ then ExpSet.add ve (addrs_ve e)
    else addrs_ve e
  | VCast (typ,e) ->
    if is_address typ then ExpSet.add ve (addrs_ve e)
    else addrs_ve e
  | VCond f -> addrs_vf f
  | Ite (e1,e2,e3) -> ExpSet.union (addrs_ve e1) (ExpSet.union (addrs_ve e2) (addrs_ve e3))
  | Uninterp (_,args,_) -> List.fold_left (fun acc e' -> ExpSet.union (addrs_ve e') acc) ExpSet.empty args

(* @return true : safe
 * @return false : don't know *)
let inspect_query_one : Global.t -> Mem.t -> Path2.t -> query -> bool * Z3.Model.model option
= fun global mem path q ->
  match q.kind with
  | IO ->
    let vc = if !Options.refined_vcgen then q.vc2 else q.vc in
    let final = add_numeric_info mem vc in
    is_valid_wrapper final
  | DZ ->
    let final = add_numeric_info mem q.vc in
    is_valid_wrapper final
  | ASSERT ->
    let final = add_numeric_info mem q.vc in
    is_valid_wrapper final
  | KILL -> is_valid_wrapper q.vc
  | ETH_LEAK ->
    (if not !Options.refined_vcgen then q.vc
     else
       (match q.org_q with
        | Org_Stmt (Call (lvop,Lv (Var (fname,_)),args,_,_,loc,_))
          when List.mem fname ["selfdestruct";"suicide"] -> q.vc
        | Org_Stmt (Call (lvop,Lv (MemberAccess (e,fname,_,_)),args,_,_,loc,_))
          when is_address (get_type_exp e) && List.mem fname ["transfer";"send"] -> q.vc2
        | Org_Stmt (Call (lvop, Lv (MemberAccess (e,"call",_,_)), args, Some eth, gasop, loc, id))
          when is_address (get_type_exp e) -> q.vc2
        | _ -> assert false))
    |> is_valid_wrapper
  | RE_EL | RE ->
    let vc = if !Options.refined_vcgen then q.vc2 else q.vc in
    is_valid_wrapper vc
  | TX_ORG ->
    let vc = if !Options.refined_vcgen then q.vc2 else q.vc in
    is_valid_wrapper vc
  | ERC20 -> raise NotImplemented

exception Encountered_Unsafe_Query of Path.t * string

let proven : Query.src -> QMap.t -> bool
= fun qid qmap ->
  QMap.find qid qmap
  |> (fun (stat,_,_) -> stat = Proven)

let fkeys_of_paths : PathSet.t -> fkey BatSet.t
= fun paths ->
  PathSet.fold (fun path acc ->
    BatSet.add (Path.get_fkey path) acc
  ) paths BatSet.empty

(* all queries in 'qs_bundle' have same query ids. *)
let inspect_query_bundle : Global.t -> Mem.t -> (Path2.t * query) list -> Query.status * PathSet2.t
= fun global mem qs_bundle ->
  List.fold_left (fun (acc, acc_c, failed) (path,q) ->
    let cfg = FuncMap.find (Path2.get_fkey path) global.fmap |> get_cfg in
    let comps = Component.collect_bp global (Path2.get_bp path) cfg in
    (* if failed && Component.subset comps acc_c then (acc, acc_c, failed) *)
    if failed (* && Component.subset comps acc_c *) then (PathSet2.add path acc, acc_c, failed)
    else
      let (proven,_) = inspect_query_one global mem path q in
      match proven with
      | true -> (acc, acc_c, failed)
      | false -> (PathSet2.add path acc, Component.union comps acc_c, true)
  ) (PathSet2.empty, Component.empty_comps, false) qs_bundle
  |> (fun (a,b,failed) ->
      if failed then (UnProven, a)
      else (assert (PathSet2.is_empty a); (Proven, a)))

let compare_query' (_,q1) (_,q2) = compare_query q1 q2
let group' pairs = BatList.group compare_query' pairs

let verify_safety : Global.t -> Mem.t -> (Path2.t * query) list -> QMap.t ->
                    PathSet2.t * QMap.t * ModelMap.t
= fun global mem qs qmap_prev ->
  let qss = group' qs in
  BatList.fold_lefti (fun (acc_p, acc_qmap, acc_m) i qs_bundle ->
    let (kind,loc,str) = Query.get_src (snd (List.hd qs_bundle)) in
    if !Options.verbose then
      (prerr_string (string_of_int (i+1) ^ "/" ^ string_of_int (List.length qss) ^ " ... ");
       prerr_string ("[" ^ to_string_kind_simple kind ^ "]" ^ " "); prerr_string ("line " ^ string_of_int loc ^ ", " ^ str ^ " ... "); flush stderr);
    if proven (kind,loc,str) qmap_prev then
      let _ = if !Options.verbose then prerr_endline "proven" in
      (acc_p, acc_qmap, acc_m)
    else
      let (status, unproven_paths) = inspect_query_bundle global mem qs_bundle in
      if PathSet2.is_empty unproven_paths then
        let _ = assert (status = Proven) in
        let fkeys = List.map fst qs_bundle |> List.map snd |> PathSet.of_list |> fkeys_of_paths in
        let acc_qmap' = QMap.add (kind,loc,str) (status, fkeys, !iter) acc_qmap in
        let _ = if !Options.verbose then prerr_endline (Query.to_string_status status) in
        (acc_p, acc_qmap', acc_m)
      else
        let _ = assert (status = UnProven) in
        let fkeys = List.map snd (PathSet2.to_list unproven_paths) |> PathSet.of_list |> fkeys_of_paths in
        let acc_qmap' = QMap.add (kind,loc,str) (status, fkeys, !iter) acc_qmap in
        let _ = if !Options.verbose then prerr_endline "unproven" in
        let acc_p' = PathSet2.union unproven_paths acc_p in
        (acc_p', acc_qmap', acc_m)
  ) (PathSet2.empty, qmap_prev, ModelMap.empty) qss

let debug_verify path vc res =
  print_endline (Path2.to_string path);
  print_endline (to_string_vformula vc);
  print_endline (string_of_bool (fst res) ^ "\n")

let verify_inductiveness : Global.t -> Mem.t -> (Path2.t * vformula) list ->
                           PathSet2.t * ModelMap.t
= fun global mem pairs ->
  List.fold_left (fun (acc_p, acc_m, acc_c, failed) (path,vc) ->
    let vc = add_numeric_info mem vc in
    let proven = is_valid_wrapper vc in
    let cfg = FuncMap.find (Path2.get_fkey path) global.fmap |> get_cfg in
    let comps = Component.collect_bp global (Path2.get_bp path) cfg in
    (* if failed (* && Component.subset comps acc_c *) then (PathSet2.add path acc_p, acc_m, acc_c, failed)
    else *)
      let _ = if !Options.debug = "invmap" && not (fst proven) then debug_verify path vc proven in
      match proven with
      | true,_ -> (acc_p, acc_m, acc_c, failed)
      | false,Some m -> (PathSet2.add path acc_p, acc_m, Component.union comps acc_c, true)
      | false,None -> (PathSet2.add path acc_p, acc_m, Component.union comps acc_c, true)
    ) (PathSet2.empty,ModelMap.empty,Component.empty_comps,false) pairs
  |> (fun (a,b,c,d) -> (a,b))

let print_invmap inductive invmap specmap =
  if inductive && !Options.verbose then
    (prerr_endline "";
     prerr_endline ("=============== Invariants Found ===============");
     prerr_endline ("Iter: " ^ (string_of_int !iter) ^ " " ^
                    "Total elapsed : " ^ string_of_float (Sys.time () -. !Profiler.start_cpu));
     prerr_endline (InvMap.to_string invmap ^ "\n" ^ SpecMap.to_string specmap))
  else ()
    (* (prerr_endline "";
     prerr_endline (InvMap.to_string invmap)) *)

let verify : Global.t -> InvMap.t -> SpecMap.t -> Mem.t -> PathSet2.t ->
             (Path2.t * vformula) list -> (Path2.t * query) list -> QMap.t ->
             bool * PathSet2.t * QMap.t * ModelMap.t
= fun global invmap specmap mem vpaths vcs qs qmap_prev ->
  let (unproven_paths1, model_map) = verify_inductiveness global mem vcs in
  if not (PathSet2.is_empty unproven_paths1) then (false, unproven_paths1, qmap_prev, model_map)
  else
    let _ = assert (PathSet2.is_empty unproven_paths1) in
    let _ = print_invmap true invmap specmap in
    let (unproven_paths2, qmap, model_map) = verify_safety global mem qs qmap_prev in
    (true, unproven_paths2, qmap, model_map)

let rec unlikely : (var * vexp) -> vformula -> bool
= fun (x,e) vf ->
  match vf with
  | VAnd (f1,f2) -> unlikely (x,e) f1 || unlikely (x,e) f2
  | SigmaEqual (x',e') ->
    if x = x' && not (equal_ve e e') then true
    else false
  | ForAll _ -> false
  | VNot _ | Imply _ | VOr _ | Label _ -> assert false
  | _ -> false

let rec cost_vf' : vformula -> vformula -> int
= fun whole vf ->
  match vf with
  | VTrue -> 0 | VFalse -> 5
  | VAnd (f1,f2) -> cost_vf' whole f1 + cost_vf' whole f2
  | VBinRel (VEq,Read (VVar ("@TU",_),_),_) -> 1
  | VBinRel (VEq,VVar _,VCond VTrue) -> 3
  | VBinRel (VEq,VVar _,VCond VFalse) -> 30
  | VBinRel (VEq,e1,e2) ->
    let vars = BatSet.union (free_ve e1) (free_ve e2) in
    let b = BatSet.exists (fun (x,_) -> BatString.exists x "inline") vars in
    if b then 200 else 40
  | VBinRel (_,e1,e2) -> 50
  | SigmaEqual (x,e) -> if unlikely (x,e) whole then 200 else 20
  | NoOverFlow _ -> 18
  | UntrustSum _ -> 15
  | UntrustSum2 _ -> 15
  | ForAll _ -> 1
  | VNot _ | Imply _
  | VOr _ | Label _ -> assert false

let cost_vf vf = cost_vf' vf vf

let cost : InvMap.t * SpecMap.t -> int
= fun (invmap,specmap) ->
  let cost1 =
    BatMap.foldi (fun n f acc ->
      let penalty = if equal_vf f VFalse && n = Plain Lang.extern_node then 200 else 0 in
      acc + (cost_vf f) + penalty
    ) invmap 0 in
  (* let cost2 = BatMap.fold (fun (pre,post) acc -> acc + cost_vf pre + cost_vf post) specmap 0 in *)
  cost1

module Workset = struct
  type work = InvMap.t * SpecMap.t
 
  let to_string_work : work -> string
  = fun (invmap,specmap) -> InvMap.to_string invmap ^ "\n" ^ SpecMap.to_string specmap

  module OrderedType = struct
    type t = work
    let compare t1 t2 = Stdlib.compare (cost t1) (cost t2)
  end
  
  module Heap = BatHeap.Make (OrderedType)
  
  (* type of workset : heap * (string set) *)
  type t = Heap.t * string BatSet.t
  let empty = (Heap.empty, BatSet.empty)
  
  let explored : work -> t -> bool
  = fun work (_,sset) -> BatSet.mem (to_string_work work) sset

  let add : work -> t -> t
  = fun work (heap,sset) ->
    if explored work (heap,sset) then (heap,sset)
    else
      (Heap.add work heap, BatSet.add (to_string_work work) sset)
 
  let choose : t -> (work * t) option
  = fun (heap,sset) ->
    try
      let elem = Heap.find_min heap in
      Some (elem, (Heap.del_min heap, sset))
    with
      | _ -> None

  let merge (invmap1,specmap1) (invmap2,specmap2) =
    (InvMap.merge invmap1 invmap2, SpecMap.merge specmap1 specmap2)

  let propagate : work -> t -> t
  = fun work (heap,sset) ->
    let lst = Heap.to_list heap in
    let workset = List.map to_string_work lst in
    List.fold_left (fun (acc_w,acc_ws,acc_v) w' ->
      let w' = merge w' work in
      if List.mem (to_string_work w') workset || not (explored w' (acc_w,acc_v)) then
        let acc_w' = if List.mem (to_string_work w') acc_ws then acc_w else Heap.add w' acc_w in
        (acc_w', (to_string_work w')::acc_ws, BatSet.add (to_string_work w') acc_v)
      else (acc_w,acc_ws,acc_v)
    ) (Heap.empty,[],sset) lst
    |> (fun (a,b,c) -> (a,c))

  let workset_info : t -> string
  = fun (heap,sset) ->
    "To explore : " ^ (string_of_int (Heap.size heap)) ^
    " Explored : " ^ (string_of_int (BatSet.cardinal sset))
end

(******************)
(******************)
(*** Main Loop  ***)
(******************)
(******************)

let verify_start_time = ref 0.0

let gen_vc_verbose global (invmap, specmap) vpaths =
  let _ = if !Options.verbose then Profiler.start "Generating VCs ... " in
  let (vcs, qs) = get_all_vcs global invmap specmap vpaths in
  let _ = if !Options.verbose then Profiler.finish "Generating VCs ... " in
  (vcs, qs)

let verify_verbose global (invmap, specmap) mem vpaths vcs qs qmap_prev =
  let _ = if !Options.verbose then Profiler.start "Checking validity of VCs ... " in
  let (inductive, unproven_paths, qmap, model_map) = verify global invmap specmap mem vpaths vcs qs qmap_prev in
  let _ = if !Options.verbose then (Profiler.finish "Checking validity of VCs ... "; prerr_endline "") in
  (inductive, unproven_paths, qmap, model_map)

let get_atoms formula = formula |> list_of_conjuncts |> FormulaSet.of_list

let rec work : Global.t -> ItvDom.Mem.t -> PathSet2.t -> Workset.t ->
               QMap.t * InvMap.t * SpecMap.t -> QMap.t * InvMap.t * SpecMap.t
= fun global mem vpaths workset (qmap_prev, invmap_known, specmap_known) ->
  if Sys.time () -. !verify_start_time > float_of_int !Options.verify_timeout then (qmap_prev, invmap_known, specmap_known)
  else
  let _ = iter := !iter + 1 in
  let _ = if !iter mod 10 = 0 then (prerr_string ("Iter : " ^ string_of_int !iter ^ " ");
                                    prerr_endline ((Workset.workset_info workset) ^ " Total elapsed : " ^ string_of_float (Sys.time () -. !Profiler.start_cpu))) in
  match Workset.choose workset with
  | None -> (qmap_prev, invmap_known, specmap_known)
  | Some (((invmap_cand, specmap_cand) as cand), remaining_workset) ->
    let _ = if !Options.debug = "invmap" then prerr_endline ("Cost : " ^ string_of_int (cost cand) ^ "\n" ^ Workset.to_string_work cand) in
    let (vcs, qs) = gen_vc_verbose global cand vpaths in
    let (inductive, unproven_paths, qmap, model_map) = verify_verbose global cand mem vpaths vcs qs qmap_prev in
    let _ = if !Options.debug = "invmap" then prerr_endline ("Inductive ? : " ^ string_of_bool inductive ^ "\n") in

    if PathSet2.is_empty unproven_paths then (qmap, invmap_cand, specmap_cand)
    else
      let refinements = refine global unproven_paths cand in
      let refinements = List.map (fun (i,s) -> (InvMap.simplify i, SpecMap.simplify s)) refinements in
      let new_workset = List.fold_left (fun acc r -> Workset.add r acc) remaining_workset refinements in
      let (new_workset, new_invmap_known, new_specmap_known) =
        if inductive then
          let (invmap_known', specmap_known') = Workset.merge cand (invmap_known,specmap_known) in
          (Workset.propagate cand new_workset, invmap_known', specmap_known')
        else (new_workset, invmap_known, specmap_known) in
      work global mem vpaths new_workset (qmap, new_invmap_known, new_specmap_known)


let scan_node: Global.t -> cfg -> Path2.t -> Node.t -> QMap.t -> QMap.t
= fun global g (ctx,path) node qmap ->
  let extern_ctx = match ctx with Some n -> n = Lang.extern_node | _ -> false in
  let queries = CollectQuery2.collect ~extern_ctx:extern_ctx global g VTrue path node in
  List.fold_left (fun acc q ->
    let k = QMap.mk_key q in
    let fkeys = try QMap.find k acc |> (fun (_,b,_) -> b) with Not_found -> BatSet.empty in
    QMap.add k (UnProven, BatSet.add (get_fkey path) fkeys, 0) acc
  ) qmap queries

let scan_path: Global.t -> Path2.t -> QMap.t -> QMap.t
= fun global path qmap ->
  let (fk, mid) = (Path2.get_fkey path, path |> Path2.get_bp |> Path.get_mid) in
  let cfg = get_cfg (FuncMap.find fk global.fmap) in
  List.fold_left (fun acc n ->
    scan_node global cfg path n acc
  ) qmap mid
 
let init_qmap: Global.t -> PathSet2.t -> QMap.t
= fun global paths ->
  PathSet2.fold (fun p acc ->
    scan_path global p acc
  ) paths QMap.empty

let collect_cutpoints' : Global.t -> Path.t ->
                         Node.t BatSet.t * Node.t BatSet.t * Node.t BatSet.t * Node.t BatSet.t ->
                         Node.t BatSet.t * Node.t BatSet.t * Node.t BatSet.t * Node.t BatSet.t
= fun global (fk,nodes) (lhs,lhs2,lhs3,extcalls) ->
  let f = FuncMap.find fk global.fmap in
  let cfg = get_cfg f in
  let (hd,last) = (BatList.hd nodes, BatList.last nodes) in
  let b1 = is_entry hd || is_loophead hd cfg in
  let b2 = is_exit last || is_loophead last cfg || is_internal_call_node global.fmap global.cnames last cfg || is_external_call_node last cfg in
  let _ = assert (b1 && b2) in
  List.fold_left (fun (acc_lh,acc_lh2,acc_lh3,acc_ext) n ->
    if is_loophead n cfg && not (is_view_pure_f f) then
      if not (contain_dead_intcall_cfg global f) then
        (BatSet.add n acc_lh, BatSet.add n acc_lh2, BatSet.add n acc_lh3, acc_ext)
      else (BatSet.add n acc_lh, BatSet.add n acc_lh2, acc_lh3, acc_ext)
    else if is_loophead n cfg then (BatSet.add n acc_lh, acc_lh2, acc_lh3, acc_ext)
    else if is_external_call_node n cfg then (acc_lh, acc_lh2, acc_lh3, BatSet.add n acc_ext)
    else if is_internal_call_node global.fmap global.cnames n cfg then (acc_lh, acc_lh2, acc_lh3, acc_ext)
    else if is_entry n || is_exit n then (acc_lh, acc_lh2, acc_lh3, acc_ext)
    else assert false
  ) (lhs,lhs2,lhs3,extcalls) [hd;last]

let collect_cutpoints : Global.t -> PathSet.t ->
                        Node.t BatSet.t * Node.t BatSet.t * Node.t BatSet.t * Node.t BatSet.t
= fun global paths ->
  PathSet.fold (collect_cutpoints' global)
    paths (BatSet.empty, BatSet.empty, BatSet.empty, BatSet.empty)

let collect_callnodes' : Global.t -> Path.t -> (Node.t * fkey) BatSet.t -> (Node.t * fkey) BatSet.t
= fun global (fk,nodes) callnodes ->
  let f = FuncMap.find fk global.fmap in
  let cfg = get_cfg f in
  List.fold_left (fun acc node ->
    if is_internal_call_node global.fmap global.cnames node cfg then
      let callee = get_callee_of_intcall global f (find_stmt node cfg) in
      if (is_public_func callee || is_external_func callee) && not (is_view_pure_f callee)
        then BatSet.add (node, Lang.get_fkey callee) acc
      else acc
    else acc
  ) callnodes nodes

let collect_callnodes : Global.t -> PathSet.t -> (Node.t * fkey) BatSet.t
= fun global paths -> PathSet.fold (collect_callnodes' global) paths BatSet.empty

let init_invmap : Node.t BatSet.t * Node.t BatSet.t -> InvMap.t
= fun (lhs,extcalls) ->
  let l_extern = if BatSet.is_empty extcalls then BatSet.empty
                 else BatSet.map (fun l -> Ctx (Lang.extern_node, l)) lhs in
  (* let l_call = BatSet.empty in *)
  let l_plain = BatSet.map (fun l -> Plain l) lhs in
  let cutpoints = if BatSet.is_empty extcalls then BatSet.add (Plain Lang.trans_node) (BatSet.union l_extern l_plain)
                  else BatSet.add (Plain Lang.extern_node) (BatSet.add (Plain Lang.trans_node) (BatSet.union l_extern l_plain)) in
  BatSet.fold (fun cp acc -> InvMap.add cp VTrue acc) cutpoints InvMap.empty

let init_specmap : (Node.t * fkey) BatSet.t -> SpecMap.t
= fun callnodes ->
  BatSet.fold (fun (n,fk) acc -> SpecMap.add n (VTrue,VTrue) acc) callnodes SpecMap.empty


let augment_global : PathSet.t -> Global.t -> Global.t
= fun paths global ->
  let paths_main = PathSet.filter (fun ((c,f,typs),_) -> c = !Options.main_contract) paths in
  let (lhs,lhs2,_,extcalls) = collect_cutpoints global paths in
  let (lhs_main, lhs2_main, lhs3_main, _) = collect_cutpoints global paths_main in
  let callnodes = collect_callnodes global paths in
  let callnodes_main = collect_callnodes global paths_main in
  {global with lhs=lhs; lhs2=lhs2; lhs_main=lhs_main; lhs2_main=lhs2_main; lhs3_main=lhs3_main;
               callnodes = callnodes; callnodes_main=callnodes_main; extcalls=extcalls}

let init : Global.t -> PathSet2.t -> InvMap.t * SpecMap.t * Workset.t * QMap.t
= fun global vpaths ->
  let invmap0 = init_invmap (global.lhs, global.extcalls) in
  let specmap0 = init_specmap global.callnodes in
  let workset0 = Workset.add (invmap0,specmap0) Workset.empty in
  let qmap0 = init_qmap global vpaths in
  (invmap0, specmap0, workset0, qmap0)

let do_verify : Global.t -> ItvDom.Mem.t -> PathSet.t -> QMap.t
= fun global mem paths ->
  verify_start_time := Sys.time();
  iter := 0;
  let global = augment_global paths global in
  let vpaths = augment_paths global paths in
  let (invmap0,specmap0,workset0,qmap0) = init global vpaths in
  let (qmap,_,_) = work global mem vpaths workset0 (qmap0, invmap0, specmap0) in
  qmap

let run : Global.t -> ItvDom.Mem.t -> PathSet.t -> QMap.t
= fun global mem paths -> do_verify global mem paths
