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

let iter = ref 0

(****************************)
(****************************)
(*** Verification helpers ***)
(****************************)
(****************************)

let apply_fst_tactic : vformula -> vformula
= fun vf ->
  if not (has_sigeq vf) then vf
  else
  let lst_3 = vf |> list_of_conjuncts |> cartesian_three in
  List.fold_left (fun acc l ->
    match l with
    | [SigmaEqual (total, (b_,typ)); 
       VBinRel (VEq, VVar (b__,_), Write (VVar (b_1,_), VVar (x,_), VBinOp (VSub, Read (VVar (b_2,_), VVar (x1,_),_), VVar (v,_), _)));
       VBinRel (VEq, VVar (b,_), Write (VVar (b__1,_), VVar (y,_), VBinOp (VAdd, Read (VVar (b__2,_), VVar (y1,_),_), VVar (v1,_), _)))]
       when is_renamed b_ && is_renamed b__ && not (is_renamed b) &&
            BatString.equal b_ b_1 && BatString.equal b_1 b_2 &&
            BatString.equal b__ b__1 && BatString.equal b__1 b__2 &&
            BatString.equal x x1 && BatString.equal y y1 && 
            BatString.equal v v1 
       -> VAnd (acc, SigmaEqual (total, (b,typ)))
    | [SigmaEqual (total, (b_,typ)); 
       VBinRel (VEq, VVar (b__,_), Write (VVar (b_1,_), VVar (x,_), VBinOp (VAdd, Read (VVar (b_2,_), VVar (x1,_),_), VVar (v,_), _)));
       VBinRel (VEq, VVar (b,_), Write (VVar (b__1,_), VVar (y,_), VBinOp (VSub, Read (VVar (b__2,_), VVar (y1,_),_), VVar (v1,_), _)))]
       when is_renamed b_ && is_renamed b__ && not (is_renamed b) &&
            BatString.equal b_ b_1 && BatString.equal b_1 b_2 &&
            BatString.equal b__ b__1 && BatString.equal b__1 b__2 &&
            BatString.equal x x1 && BatString.equal y y1 && 
            BatString.equal v v1 
       -> VAnd (acc, SigmaEqual (total, (b,typ)))
    | _ -> acc
  ) vf lst_3

let apply_snd_tactic : vformula -> vformula
= fun vf ->
  if not (has_noflow vf) then vf
  else
  let lst_4 = try vf |> list_of_conjuncts |> cartesian_four with Stack_overflow -> assert false in
  List.fold_left (fun acc l ->
    match l with
    | [NoOverFlow (b_, typ);
       VBinRel (VGeq, Read (VVar (b_1,_), VVar (x,_), _), VVar (v,_));
       VBinRel (VEq, VVar (b__,_), Write (VVar (b_2,_), VVar (x1,_), VBinOp (VSub, Read (VVar (b_3,_), VVar (x2,_),_), VVar (v1,_), _)));
       VBinRel (VEq, VVar (b,_), Write (VVar (b__1,_), VVar (y,_), VBinOp (VAdd, Read (VVar (b__2,_), VVar (y1,_),_), VVar (v2,_), _)))]
       when is_renamed b_ && is_renamed b__ && not (is_renamed b) &&
            BatString.equal b_ b_1 && BatString.equal b_1 b_2 &&  BatString.equal b_2 b_3 &&
            BatString.equal b__ b__1 && BatString.equal b__1 b__2 &&
            BatString.equal x x1 &&  BatString.equal x1 x2 && 
            BatString.equal y y1 && 
            BatString.equal v v1 && BatString.equal v1 v2 
       -> VAnd (acc, NoOverFlow (b, typ))
    | [NoOverFlow (b_, typ);
       VBinRel (VGeq, Read (VVar (b_1,_), VVar (x,_), _), VVar (v,_));
       VBinRel (VEq, VVar (b__,_), Write (VVar (b_2,_), VVar (y,_), VBinOp (VAdd, Read (VVar (b_3,_), VVar (y1,_),_), VVar (v1,_), _)));
       VBinRel (VEq, VVar (b,_), Write (VVar (b__1,_), VVar (x1,_), VBinOp (VSub, Read (VVar (b__2,_), VVar (x2,_),_), VVar (v2,_), _)))]
       when is_renamed b_ && is_renamed b__ && not (is_renamed b) &&
            BatString.equal b_ b_1 && BatString.equal b_1 b_2 &&  BatString.equal b_2 b_3 &&
            BatString.equal b__ b__1 && BatString.equal b__1 b__2 &&
            BatString.equal x x1 &&  BatString.equal x1 x2 && 
            BatString.equal y y1 && 
            BatString.equal v v1 && BatString.equal v1 v2 
       -> VAnd (acc, NoOverFlow (b, typ))
    | _ -> acc
  ) vf lst_4

let apply_tactics : vformula -> vformula
= fun vf ->
  match vf with
  | Imply (pre,con) ->
    let pre = apply_fst_tactic pre in
    let pre = apply_snd_tactic pre in
    Imply (pre,con)
  | _ -> vf (* VTrue or VFalse *)

let get_cond_at_cutpoint : Global.t -> InvMap.t -> func -> Node.t -> vformula 
= fun global invmap func node ->
  if is_loophead node (get_cfg func) then InvMap.find node invmap
  else
    let cname = (get_finfo func).scope_s in
    if BatString.equal cname !main_contract then
      if is_entry node && (get_finfo func).is_constructor then VTrue else
      if is_entry node && (is_public_func func || is_external_func func) then InvMap.find Lang.trans_node invmap else
      if is_exit node && (is_public_func func || is_external_func func) then InvMap.find Lang.trans_node invmap else
      if is_entry node && (is_internal_func func || is_private_func func) then VTrue else
      if is_exit node && (is_internal_func func || is_private_func func) then VTrue
      else failwith "get_cond_cutpoint : not a cutpoint !"
    else VTrue (* functions not in a main contract *)

(**************************)
(**************************)
(*** Verification cores ***)
(**************************)
(**************************)

let gen_vc_bp : Global.t -> ItvDom.Mem.t -> InvMap.t -> Path.t ->
                vformula * query list
= fun global mem invmap path ->
  let fk = Path.get_fkey path in
  let bp = Path.get_bp path in
  let cfg = Global.get_cfg fk global in
  let func = FuncMap.find fk global.fmap in
  let (cp_entry, mid, cp_exit) = (List.hd bp, Path.get_mid bp, BatList.last bp) in
  let startf = get_cond_at_cutpoint global invmap func cp_entry in
  let (sp, qs) =
    List.fold_left (fun (acc_vf, acc_qs) node ->
      let assertion = if !check_assert then Assertion.collect_queries global acc_vf path (find_stmt node cfg) else [] in
      let overflow = if !check_io then Overflow.collect_queries acc_vf path (find_stmt node cfg) else [] in
      let new_qs = assertion @ overflow in
      convert_stmt global func node (acc_vf, acc_qs @ new_qs)
    ) (startf, []) mid in
  let g = get_cond_at_cutpoint global invmap func cp_exit in
  let formula = Imply (sp,g) in
  (formula, qs)

let gen_vc : Global.t -> ItvDom.Mem.t -> InvMap.t -> PathSet.t ->
             vformula list * query list
= fun global mem invmap paths ->
  PathSet.fold (fun path (acc_vc,acc_qs) ->
    let (vc',qs') = gen_vc_bp global mem invmap path in
    (acc_vc@[vc'], qs'@acc_qs)
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

let is_invalid_approx : vformula -> bool
= fun vf ->
  match vf with
  | Imply (pre,con) ->
    if not (BatSet.subset (free_vf con) (free_vf pre))
      then true
    else false
  | VFalse -> false
  | _ -> assert false

let is_valid_wrapper : vformula -> bool * Z3.Model.model option
= fun vf ->
  let vf = Simplification.remove_pow vf in
  let vf = fix_normalize vf in
  let vf = apply_tactics vf in
  let b = try Template.valid_template vf with Stack_overflow -> false in
  if b then (true,None)
  else
    let vf = transform vf in (* special predicates are transformed in here *)
    if is_invalid_approx vf then (false,None) 
    else
      Z3Interface.is_valid vf

(* @return true : safe
 * @return false : don't know *)
let check_safety_one : Global.t -> Mem.t -> query -> bool * Z3.Model.model option
= fun global mem q ->
  match q.kind with
  | IO ->
    let final = add_numeric_info mem q.vc in
    is_valid_wrapper final
  | DZ ->
    let final = add_numeric_info mem q.vc in
    is_valid_wrapper final
  | ASSERT ->
    let final = add_numeric_info mem q.vc in
    is_valid_wrapper final
  | ERC20 | ERC721 | LEAK | SUICIDE | ACCESS -> raise (Failure "NotImplemented")

exception Encountered_Unsafe_Query of Path.t * string

(* all queries in 'qs_bundle' have same query ids. *)
let inspect_query_bundle : Global.t -> Mem.t -> query list -> PathSet.t
= fun global mem qs_bundle ->
  fst(
  List.fold_left (fun (acc,failed) q ->
    if failed then (acc, failed)
    else
      let (b,_) = check_safety_one global mem q in
      match b with
      | true -> (acc, failed)
      | false -> (PathSet.add q.path acc, true)
  ) (PathSet.empty,false) qs_bundle)

let proved : Query.src -> QMap.t -> bool
= fun qid qmap ->
  let (stat,_) = QMap.find qid qmap in
  stat = Proven

let verify_safety : Global.t -> Mem.t -> query list -> QMap.t ->
                    PathSet.t * QMap.t * ModelMap.t
= fun global mem qs qmap_prev ->
  let qss = group qs in
  BatList.fold_lefti (fun (acc_p, acc_qmap, acc_m) i qs_bundle ->
    let (kind,loc,str) = Query.get_src (List.hd qs_bundle) in
    if proved (kind,loc,str) qmap_prev then (acc_p, acc_qmap, acc_m)
    else
      let unproven_paths = inspect_query_bundle global mem qs_bundle in
      if PathSet.is_empty unproven_paths then
        (acc_p, QMap.add (kind,loc,str) (Proven, !iter) acc_qmap, acc_m)
      else
        (PathSet.union unproven_paths acc_p, acc_qmap, acc_m)
  ) (PathSet.empty, qmap_prev, ModelMap.empty) qss

let verify_inductiveness : Global.t -> Mem.t -> PathSet.t -> vformula list ->
                           PathSet.t * ModelMap.t
= fun global mem paths vcs ->
  let paths = PathSet.to_list paths in
  List.fold_left2 (fun (acc_p, acc_m) path vc ->
    let vc = add_numeric_info mem vc in
    match is_valid_wrapper vc with
    | true,_ -> (acc_p, acc_m)
    | false,Some m -> (PathSet.add path acc_p, acc_m)
    | false,None -> (PathSet.add path acc_p, acc_m)
  ) (PathSet.empty,ModelMap.empty) paths vcs

let verify : Global.t -> Mem.t -> InvMap.t -> PathSet.t -> vformula list -> query list -> QMap.t ->
             bool * PathSet.t * QMap.t * ModelMap.t
= fun global mem invmap paths vcs qs qmap_prev ->
  let (unproven_paths1, model_map) = verify_inductiveness global mem paths vcs in
  if not (PathSet.is_empty unproven_paths1) then (false, unproven_paths1, qmap_prev, model_map)
  else
     let (unproven_paths2, qmap, model_map) = verify_safety global mem qs qmap_prev in
     (true, PathSet.union unproven_paths1 unproven_paths2, qmap, model_map)

let rec cost_vf : vformula -> int
= fun vf ->
  match vf with
  | VTrue | VFalse -> 2
  | VAnd (f1,f2) -> 2 + cost_vf f1 + cost_vf f2
  | VBinRel (_,e1,e2) -> 2
  | SigmaEqual _ -> 1
  | NoOverFlow _ -> 1
  | VNot _ | Imply _
  | ForAll _ | VOr _ | Label _ -> raise (Failure "cost_vf")

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
  = fun work (_,sset) ->
    BatSet.mem (InvMap.to_string work) sset

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
    let lst' = List.map (InvMap.merge work) lst in
    let lst' = BatList.unique_cmp ~cmp:(fun a b -> BatString.compare (InvMap.to_string a) (InvMap.to_string b)) lst' in
    let heap' = Heap.of_list lst' in
    let new_sset = BatSet.of_list (List.map InvMap.to_string lst') in 
    let sset' = BatSet.union new_sset sset in 
    (heap',sset')

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

let rec work : PathSet.t -> Global.t -> ItvDom.Mem.t -> Workset.t -> InvMap.t -> QMap.t -> QMap.t
= fun paths global mem workset known qmap_prev ->
  iter := !iter + 1;
  if !iter mod 10 = 0 then
    (prerr_string ("Iter : " ^ string_of_int !iter ^ " ");
     prerr_endline ((Workset.workset_info workset) ^ " Total elapsed : " ^ string_of_float (Sys.time () -. !Profiler.start_time)));
  if Sys.time () -. !Profiler.start_time > float_of_int !Options.verify_timeout then qmap_prev
  else
  match Workset.choose workset with
  | None -> qmap_prev
  | Some (invmap_cand, remaining_workset) ->
    let (vcs, qs) = gen_vc global mem invmap_cand paths in
    let (is_inductive, unproven_paths, qmap, model_map) = verify global mem invmap_cand paths vcs qs qmap_prev in
    if PathSet.is_empty unproven_paths then qmap
    else
      let refinements = refine global unproven_paths model_map invmap_cand in
      let refinements = List.map InvMap.simplify refinements in
      let new_workset = List.fold_left (fun acc r -> Workset.add r acc) remaining_workset refinements in
      let (new_workset, new_known) =
        if is_inductive then (Workset.propagate invmap_cand new_workset, InvMap.merge invmap_cand known)
        else (new_workset, known)
      in
      work paths global mem new_workset new_known qmap

let scan_node: Global.t -> cfg -> Path.t -> Node.t -> QMap.t -> QMap.t
= fun global g path node qmap ->
  let assertion = if !check_assert then Assertion.collect_queries global VTrue path (find_stmt node g) else [] in
  let overflow = if !check_io then Overflow.collect_queries VTrue path (find_stmt node g) else [] in
  let queries = assertion @ overflow in
  List.fold_left (fun acc q ->
    QMap.add (QMap.mk_key q) (UnProven, 0) acc
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

let run : Global.t -> ItvDom.Mem.t -> PathSet.t -> QMap.t
= fun global mem paths ->
  iter := 0;
  let init_workset = Workset.add InvMap.empty Workset.empty in
  let qmap = init_qmap global paths in
  work paths global mem init_workset InvMap.empty qmap
