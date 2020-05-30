open Lang
open MakeCfg

type t = fkey * Node.t list
and path = t

let dummy_path = (("","",[]), []) 

let get_fkey : path -> fkey
= fun (k,_) -> k

let get_bp : path -> Node.t list
= fun (_,bp) -> bp

let to_string : path -> string
= fun (k,bp) ->
  to_string_fkey k ^ " : " ^ to_string_path bp

let get_mid : 'a list -> 'a list
= fun lst -> 
  match lst with
  | [] -> []
  | hd::tl -> BatList.remove_at (List.length tl - 1) tl

let to_cutpoint : Node.t -> Node.t
= fun node ->
  match node with
  | ENTRY -> Node 0
  | EXIT -> Node 0
  | _ -> node

let find_cutpoints : Global.t -> path -> Node.t BatSet.t
= fun global (k,bp) ->
  let cfg = Global.get_cfg k global in
  let func = FuncMap.find k global.fmap in
  (* let b = is_public_func func && List.exists (fun n -> is_entry n || is_exit n) bp in *)
  (* let lhs = BatSet.filter (fun n -> is_loophead n cfg) (BatSet.of_list bp) in *)
  let (hd, last) = (BatList.hd bp, BatList.last bp) in
  let _ = assert (is_entry hd || is_loophead hd cfg) in
  let _ = assert (is_exit last || is_loophead last cfg) in
  let lst =
  List.filter (fun n ->
    is_loophead n cfg ||
    ((is_entry n || is_exit n) && (is_public_func func || is_external_func func))
  ) [hd;last] in
  BatSet.map to_cutpoint (BatSet.of_list lst)

(***************************)
(***************************)
(** Basic Path Generation **)
(***************************)
(***************************)

(* returns (processed path set, processing path set, visited root nodes) *)
(* 'root node' here means cutpoint. *)
let gen_onestep_bp_path : cfg -> node list -> node BatSet.t -> 
                         (node list BatSet.t * node list BatSet.t * node BatSet.t)
= fun g path visited_roots -> 
  let last = BatList.last path in
  let nexts = succ last g in
  List.fold_left (fun (processed, processing, acc_visited_roots) next ->
    if is_loophead next g (* || is_callnode next g *) || is_exit next then
      let processed' = BatSet.add (path@[next]) processed in
      let processing' = if BatSet.mem next visited_roots then processing else BatSet.add [next] processing in
      let acc_visited_roots' = BatSet.add next visited_roots in
      (processed', processing', acc_visited_roots')
    else
      (processed, BatSet.add (path@[next]) processing, acc_visited_roots)
  ) (BatSet.empty, BatSet.empty, visited_roots) nexts

let gen_onestep_bp : cfg ->
                    (node list BatSet.t * node list BatSet.t * node BatSet.t) -> 
                    (node list BatSet.t * node list BatSet.t * node BatSet.t)
= fun g (processed, processing, visited_roots) ->
  (* whenever this function is called,
     "processed" and "visited_roots" are accumulated, while processing is reinitialized *)
  BatSet.fold (fun path (acc1, acc2, acc3) ->
    let (new_processed, new_processing, new_visited_roots) = gen_onestep_bp_path g path acc3 in
    (BatSet.union new_processed acc1, BatSet.union new_processing acc2, BatSet.union new_visited_roots acc3)
  ) processing (processed, BatSet.empty, visited_roots)

let rec fix f g (processed,processing,visited_roots) =
  let (processed',processing',visited_roots') = f g (processed,processing,visited_roots) in
    if BatSet.is_empty processing' then (processed',processing',visited_roots')
    else fix f g (processed',processing',visited_roots')

let gen_basic_paths_cfg : cfg -> node list BatSet.t
= fun g ->
  let (basic_paths,_,_) = 
    fix gen_onestep_bp g (BatSet.empty, BatSet.singleton [Node.entry], BatSet.singleton Node.entry) in
  basic_paths

let rec bfs : cfg -> node BatSet.t -> (node * node list) BatSet.t -> node list BatSet.t -> node list BatSet.t
= fun g seeds works bps -> (* works: pending paths *)
  if BatSet.is_empty works then bps
  else
    let ((n,path), works) = BatSet.pop_min works in
    if is_exit n then
      bfs g seeds works (BatSet.add path bps)
    else if is_loophead n g then
      let nexts = succ n g in
      let works = if BatSet.mem n seeds then works else List.fold_left (fun acc n' -> BatSet.add (n', [n;n']) acc) works nexts in
      let seeds = BatSet.add n seeds in
      bfs g seeds works (BatSet.add path bps)
    else
      let nexts = succ n g in
      let works = List.fold_left (fun acc n' -> BatSet.add (n',path@[n']) acc) works nexts in
      bfs g seeds works bps

let rec bfs2 : cfg -> node -> node list -> node list BatSet.t
= fun g n path ->
  if is_exit n then BatSet.singleton path
  else
    let nexts = succ n g in
    List.fold_left (fun acc n' ->
      BatSet.union (bfs2 g n' (path@[n'])) acc
    ) BatSet.empty nexts

let generate_basic_paths : pgm -> pgm
= fun pgm ->
  List.map (fun c ->
    let funcs = get_funcs c in
    let funcs' =
      List.map (fun f ->
        let g = get_cfg f in
        let bps = gen_basic_paths_cfg g in
        let g' = {g with basic_paths = bps} in
        update_cfg f g'
      ) funcs in
    update_funcs funcs' c
  ) pgm

(****************************)
(****************************)
(** Collecting Basic Paths **)
(****************************)
(****************************)

module PathSet = BatSet.Make (struct type t = path let compare = Stdlib.compare end)

let collect_bps_f : func -> PathSet.t
= fun f ->
  let fk = Lang.get_fkey f in
  let bps = (Lang.get_cfg f).basic_paths in
  BatSet.fold (fun bp acc ->
    PathSet.add (fk,bp) acc
  ) bps PathSet.empty
    
let collect_bps_c : contract -> PathSet.t
= fun c ->
  let funcs = get_funcs c in
  List.fold_left (fun acc f ->
    PathSet.union (collect_bps_f f) acc
  ) PathSet.empty funcs 

let collect_bps : pgm -> PathSet.t 
= fun p ->
  List.fold_left (fun acc c ->
    PathSet.union (collect_bps_c c) acc
  ) PathSet.empty p

let generate : pgm -> PathSet.t
= fun pgm ->
  Profiler.start "Generating Paths ... ";
  let pgm = generate_basic_paths pgm in
  let paths = collect_bps pgm in
  Profiler.finish "Generating Paths ... ";
  Profiler.print_log ("- paths : " ^ string_of_int (PathSet.cardinal paths));
  prerr_endline "";
  paths
