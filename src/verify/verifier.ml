open Lang
open Vlang
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

let get_cond_cutpoint : Global.t -> InvMap.t -> func -> Node.t -> vformula
= fun global invmap func node ->
  if is_loophead node (get_cfg func) then InvMap.find node invmap
  else
    let cname = (get_finfo func).scope_s in
    if BatString.equal cname !main_contract then
      if is_entry node && is_constructor func then VTrue else
      if is_entry node && (is_public_func func || is_external_func func) then InvMap.find Lang.trans_node invmap else
      if is_exit node && (is_public_func func || is_external_func func) then InvMap.find Lang.trans_node invmap else
      if is_entry node && (is_internal_func func || is_private_func func) then VTrue else
      if is_exit node && (is_internal_func func || is_private_func func) then VTrue
      else failwith "get_cond_cutpoint : not a cutpoint !"
    else VTrue (* functions not in a main contract *)

let get_startf_endf : Global.t -> InvMap.t -> Path.t -> vformula * vformula
= fun global invmap path ->
  let bp = Path.get_bp path in
  let func = FuncMap.find (Path.get_fkey path) global.fmap in
  let (start, mid, last) = (BatList.hd bp, Path.get_mid bp, BatList.last bp) in
  let startf = get_cond_cutpoint global invmap func start in
  let endf = get_cond_cutpoint global invmap func last in
  (startf, endf)

let gen_vc : Global.t -> vformula * vformula -> Path.t -> vformula * query list
= fun global (startf,endf) path ->
  let mid = Path.get_bp path |> Path.get_mid in
  let func = FuncMap.find (Path.get_fkey path) global.fmap in
  let cfg = get_cfg func in
  let (sp, qs) =
    List.fold_left (fun (acc_vf, acc_qs) node ->
      let new_qs = CollectQuery.collect global cfg acc_vf path node in
      convert_stmt global func node (acc_vf, acc_qs @ new_qs)
    ) (startf, []) mid in
  let qs = List.map (fun q -> {q with vc2 = Imply (sp, q.vc2)}) qs in
  let formula = Imply (sp, endf) in
  (formula, qs)

let get_all_vcs : Global.t -> InvMap.t -> PathSet.t ->
                  (Path.t * vformula) list * (Path.t * query) list
= fun global invmap paths ->
  PathSet.fold (fun path (acc_vc,acc_qs) ->
    let (startf, endf) = get_startf_endf global invmap path in
    let (vc',qs') = gen_vc global (startf,endf) path in
    let qs' = List.map (fun q' -> (path,q')) qs' in
    (acc_vc @ [(path,vc')], qs'@acc_qs)
  ) paths ([],[])

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
  | Read (VVar ("length",t), VVar _, EType (UInt 256)) -> ExpSet.singleton ve
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

let rec include_or : vformula -> bool
= fun vf ->
  match vf with
  | VTrue | VFalse -> false
  | VNot f -> include_or f
  | VAnd (f1,f2) -> include_or f1 || include_or f2
  | VOr (f1,f2) -> true
  | VBinRel (_,e1,e2) -> false
  | Imply _ -> true (* this case may exist, e.g., NoOverflow *)
  | SigmaEqual _ | NoOverFlow _ -> assert false
  | ForAll (_,f) -> include_or f
  | Label _ -> assert false

let rec has_mul_div_f : vformula -> bool
= fun vf ->
  match vf with
  | VTrue | VFalse -> false
  | VNot f -> has_mul_div_f f
  | VAnd (f1,f2) -> has_mul_div_f f1 || has_mul_div_f f2
  | VOr (f1,f2) -> has_mul_div_f f1 || has_mul_div_f f2
  | VBinRel (_,e1,e2) -> has_mul_div_e e1 || has_mul_div_e e2
  | Imply (f1,f2) -> has_mul_div_f f1 || has_mul_div_f f2
  | SigmaEqual _ | NoOverFlow _ -> assert false
  | ForAll (_,f) -> has_mul_div_f f
  | Label _ -> assert false

and has_mul_div_e : vexp -> bool
= fun ve ->
  match ve with
  | VInt _ | VVar _ -> false
  | Read (e1,e2,_) -> has_mul_div_e e1 || has_mul_div_e e2
  | Write (e1,e2,e3) -> has_mul_div_e e1 || has_mul_div_e e2 || has_mul_div_e e3
  | VBinOp (vbop,e1,e2,_) -> vbop=VMul || vbop=VDiv || has_mul_div_e e1 || has_mul_div_e e2
  | VUnOp (_,e,_) -> has_mul_div_e e
  | VCast (_,e) -> has_mul_div_e e
  | VCond f -> has_mul_div_f f
  | Ite (e1,e2,e3) -> has_mul_div_e e1 || has_mul_div_e e2 || has_mul_div_e e3
  | Uninterp (_,args,_) -> List.fold_left (fun acc e' -> has_mul_div_e e' || acc) false args

let is_complex : vformula -> bool
= fun vf -> include_or vf && has_mul_div_f vf

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

let is_valid_wrapper : vformula -> bool * Z3.Model.model option
= fun vf ->
  let vf = Simplification.remove_pow vf in
  let vf = Simplification.fix (fun vf -> vf |> normalize |> propagate_eq) vf in
  let vf = Tactic.apply vf in
  let b = try Template.valid_template vf with Stack_overflow -> false in
  if b then (true,None)
  else
    let vf = TransformPredicate.transform vf in (* special predicates are transformed in here *)
    if is_invalid_approx vf then (false,None)
    else
      Z3Interface.is_valid vf

(* @return true : safe
 * @return false : don't know *)
let check_safety_one : Global.t -> Mem.t -> query -> bool * Z3.Model.model option
= fun global mem q ->
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
  | KILL | ETH_LEAK | ERC20 -> failwith "NotImplemented"

exception Encountered_Unsafe_Query of Path.t * string

let proved : Query.src -> QMap.t -> bool
= fun qid qmap ->
  QMap.find qid qmap
  |> (fun (stat,_,_) -> stat = Proven)

let fkeys_of_paths : PathSet.t -> fkey BatSet.t
= fun paths ->
  PathSet.fold (fun path acc ->
    BatSet.add (Path.get_fkey path) acc
  ) paths BatSet.empty

(* all queries in 'qs_bundle' have same query ids. *)
let inspect_query_bundle : Global.t -> Mem.t -> (Path.t * query) list -> PathSet.t
= fun global mem qs_bundle ->
  fst(
  List.fold_left (fun (acc,failed) (path,q) ->
    if failed then (acc, failed)
    else
      let (b,_) = check_safety_one global mem q in
      match b with
      | true -> (acc, failed)
      | false -> (PathSet.add path acc, true)
  ) (PathSet.empty,false) qs_bundle)

let compare_query' (_,q1) (_,q2) = compare_query q1 q2
let group' pairs = BatList.group compare_query' pairs

let verify_safety : Global.t -> Mem.t -> (Path.t * query) list -> QMap.t ->
                    PathSet.t * QMap.t * ModelMap.t
= fun global mem qs qmap_prev ->
  let qss = group' qs in
  BatList.fold_lefti (fun (acc_p, acc_qmap, acc_m) i qs_bundle ->
    let (kind,loc,str) = Query.get_src (snd (List.hd qs_bundle)) in
    if !Options.verbose then
      (prerr_string (string_of_int (i+1) ^ "/" ^ string_of_int (List.length qss) ^ " ... ");
       prerr_string ("[" ^ to_string_kind_simple kind ^ "]" ^ " "); prerr_string ("line " ^ string_of_int loc ^ ", " ^ str ^ " ... "); flush stderr);
    if proved (kind,loc,str) qmap_prev then
      let _ = if !Options.verbose then prerr_endline "proven" in
      (acc_p, acc_qmap, acc_m)
    else
      let unproven_paths = inspect_query_bundle global mem qs_bundle in
      if PathSet.is_empty unproven_paths then
        let fkeys = List.map fst qs_bundle |> PathSet.of_list |> fkeys_of_paths in
        let acc_qmap' = QMap.add (kind,loc,str) (Proven, fkeys, !iter) acc_qmap in
        let _ = if !Options.verbose then prerr_endline "proven" in
        (acc_p, acc_qmap', acc_m)
      else
        let fkeys = fkeys_of_paths unproven_paths in
        let acc_qmap' = QMap.add (kind,loc,str) (UnProven, fkeys, !iter) acc_qmap in
        let _ = if !Options.verbose then prerr_endline "unproven" in
        let acc_p' = PathSet.union unproven_paths acc_p in
        (acc_p', acc_qmap', acc_m)
  ) (PathSet.empty, qmap_prev, ModelMap.empty) qss

let debug_verify path vc res =
  print_endline (Path.to_string path);
  print_endline (to_string_vformula vc);
  print_endline (string_of_bool (fst res) ^ "\n")

let verify_inductiveness : Global.t -> Mem.t -> (Path.t * vformula) list ->
                           PathSet.t * ModelMap.t
= fun global mem pairs ->
  List.fold_left (fun (acc_p, acc_m) (path,vc) ->
    let vc = add_numeric_info mem vc in
    let res = is_valid_wrapper vc in
    let _ = if !Options.debug = "invmap" && not (fst res) then debug_verify path vc res in
    match res with
    | true,_ -> (acc_p, acc_m)
    | false,Some m -> (PathSet.add path acc_p, acc_m)
    | false,None -> (PathSet.add path acc_p, acc_m)
  ) (PathSet.empty,ModelMap.empty) pairs

let verify : Global.t -> Mem.t -> InvMap.t -> PathSet.t ->
             (Path.t * vformula) list -> (Path.t * query) list -> QMap.t ->
             bool * PathSet.t * QMap.t * ModelMap.t
= fun global mem invmap paths vcs qs qmap_prev ->
  let (unproven_paths1, model_map) = verify_inductiveness global mem vcs in
  if not (PathSet.is_empty unproven_paths1) then (false, unproven_paths1, qmap_prev, model_map)
  else
    (if !Options.verbose then
       (prerr_endline "";
        prerr_endline ("=============== Invariants Found ===============");
        prerr_endline ("Iter: " ^ (string_of_int !iter) ^ " " ^
                       "Total elapsed : " ^ string_of_float (Sys.time () -. !Profiler.start_cpu));
        prerr_endline (InvMap.to_string invmap));
     let (unproven_paths2, qmap, model_map) = verify_safety global mem qs qmap_prev in
     (true, PathSet.union unproven_paths1 unproven_paths2, qmap, model_map))

let rec cost_vf : vformula -> int
= fun vf ->
  match vf with
  | VTrue -> 0 | VFalse -> 2
  | VAnd (f1,f2) -> 2 + cost_vf f1 + cost_vf f2
  | VBinRel (_,e1,e2) -> 2
  | SigmaEqual _ | NoOverFlow _ -> 1
  | VNot _ | Imply _ | ForAll _
  | VOr _ | Label _ -> assert false

let cost_map : InvMap.t -> int
= fun m -> BatMap.fold (fun f acc -> acc + cost_vf f) m 0

let cost m = cost_map m

module Workset = struct
  type work = InvMap.t
  
  module OrderedType = struct
    type t = work
    let compare t1 t2 = Stdlib.compare (cost t1) (cost t2)
  end
  
  module Heap = BatHeap.Make (OrderedType)
  
  (* type of workset : heap * (string set) *)
  type t = Heap.t * string BatSet.t
  let empty = (Heap.empty, BatSet.empty)
  
  let explored : work -> t -> bool
  = fun work (_,sset) -> BatSet.mem (InvMap.to_string work) sset

  let add : work -> t -> t
  = fun work (heap,sset) ->
    if explored work (heap,sset) then (heap,sset)
    else
      (Heap.add work heap, BatSet.add (InvMap.to_string work) sset)
 
  let choose : t -> (work * t) option
  = fun (heap,sset) ->
    try
      let elem = Heap.find_min heap in
      Some (elem, (Heap.del_min heap, sset))
    with
      | _ -> None

  let propagate : work -> t -> t
  = fun work (heap,sset) ->
    let lst = Heap.to_list heap in
    let workset = List.map InvMap.to_string lst in
    List.fold_left (fun (acc_w,acc_ws,acc_v) w' ->
      let w' = InvMap.merge w' work in
      if List.mem (InvMap.to_string w') workset || not (explored w' (acc_w,acc_v)) then
        let acc_w' = if List.mem (InvMap.to_string w') acc_ws then acc_w else Heap.add w' acc_w in
        (acc_w', (InvMap.to_string w')::acc_ws, BatSet.add (InvMap.to_string w') acc_v)
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

let gen_vc_verbose global invmap_cand paths =
  let _ = if !Options.verbose then Profiler.start "Generating VCs ... " in
  let (vcs, qs) = get_all_vcs global invmap_cand paths in
  let _ = if !Options.verbose then Profiler.finish "Generating VCs ... " in
  (vcs, qs)

let verify_verbose global mem invmap_cand paths vcs qs qmap_prev =
  let _ = if !Options.verbose then Profiler.start "Checking validity of VCs ... " in
  let (inductive, unproven_paths, qmap, model_map) = verify global mem invmap_cand paths vcs qs qmap_prev in
  let _ = if !Options.verbose then (Profiler.finish "Checking validity of VCs ... "; prerr_endline "") in
  (inductive, unproven_paths, qmap, model_map)


let rec work : PathSet.t -> Global.t -> ItvDom.Mem.t -> Workset.t -> InvMap.t -> QMap.t -> QMap.t
= fun paths global mem workset known qmap_prev ->
  if Sys.time () -. !verify_start_time > float_of_int !Options.verify_timeout then qmap_prev
  else
  let _ = iter := !iter + 1 in
  let _ = if !iter mod 10 = 0 then (prerr_string ("Iter : " ^ string_of_int !iter ^ " ");
                                    prerr_endline ((Workset.workset_info workset) ^ " Total elapsed : " ^ string_of_float (Sys.time () -. !Profiler.start_cpu))) in
  match Workset.choose workset with
  | None -> qmap_prev
  | Some (invmap_cand, remaining_workset) ->
    let _ = if !Options.debug = "invmap" then prerr_endline ("Cost : " ^ string_of_int (cost_map invmap_cand) ^ "\n" ^ InvMap.to_string invmap_cand) in
    let (vcs, qs) = gen_vc_verbose global invmap_cand paths in
    let (inductive, unproven_paths, qmap, model_map) = verify_verbose global mem invmap_cand paths vcs qs qmap_prev in
    let _ = if !Options.debug = "invmap" then prerr_endline ("Inductive ? : " ^ string_of_bool inductive ^ "\n") in

    if PathSet.is_empty unproven_paths then qmap
    else
      let refinements = refine global unproven_paths invmap_cand in
      let refinements = List.map InvMap.simplify refinements in
      let new_workset = List.fold_left (fun acc r -> Workset.add r acc) remaining_workset refinements in
      let (new_workset, new_known) =
        if inductive then
          (Workset.propagate invmap_cand new_workset, InvMap.merge invmap_cand known)
        else (new_workset, known)
      in
      work paths global mem new_workset new_known qmap

let scan_node: Global.t -> cfg -> Path.t -> Node.t -> QMap.t -> QMap.t
= fun global g path node qmap ->
  let queries = CollectQuery.collect global g VTrue path node in
  List.fold_left (fun acc q ->
    let k = QMap.mk_key q in
    let fkeys = try QMap.find k acc |> (fun (_,b,_) -> b) with Not_found -> BatSet.empty in
    QMap.add k (UnProven, BatSet.add (get_fkey path) fkeys, 0) acc
  ) qmap queries

let scan_path: Global.t -> Path.t -> QMap.t -> QMap.t
= fun global path qmap ->
  let (fk,nodes) = (Path.get_fkey path, Path.get_bp path) in
  let cfg = get_cfg (FuncMap.find fk global.fmap) in
  List.fold_left (fun acc n ->
    scan_node global cfg path n acc
  ) qmap nodes
 
let init_qmap: Global.t -> PathSet.t -> QMap.t
= fun global paths ->
  PathSet.fold (fun p acc ->
    scan_path global p acc
  ) paths QMap.empty

let collect_cutpoints' : Global.t -> Path.t -> Node.t BatSet.t -> Node.t BatSet.t
= fun global (fk,nodes) lhs ->
  let cfg = get_cfg (FuncMap.find fk global.fmap) in
  let (hd,last) = BatList.hd nodes, BatList.last nodes in
  let b1 = is_entry hd || is_loophead hd cfg in
  let b2 = is_exit last || is_loophead last cfg in
  let _ = assert (b1 && b2) in
  List.fold_left (fun acc n ->
    if is_loophead n cfg then BatSet.add n acc
    else if is_entry n || is_exit n then acc
    else assert false
  ) lhs [hd;last]

let collect_cutpoints : Global.t -> PathSet.t -> Node.t BatSet.t
= fun global paths -> PathSet.fold (collect_cutpoints' global) paths BatSet.empty

let init_invmap : Node.t BatSet.t -> InvMap.t
= fun lhs ->
  let cutpoints = BatSet.add Lang.trans_node lhs in
  BatSet.fold (fun cp acc -> InvMap.add cp VTrue acc) cutpoints InvMap.empty

let run : Global.t -> ItvDom.Mem.t -> PathSet.t -> QMap.t
= fun global mem paths ->
  verify_start_time := Sys.time();
  iter := 0;
  let lhs = collect_cutpoints global paths in
  let global = {global with lhs = lhs} in
  let invmap0 = init_invmap lhs in
  let workset0 = Workset.add invmap0 Workset.empty in
  let qmap0 = init_qmap global paths in
  work paths global mem workset0 invmap0 qmap0
