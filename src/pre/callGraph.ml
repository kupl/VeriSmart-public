open Lang
open Vocab
open FuncMap

type edge = fkey * fkey

let to_string_edge (k1,k2) = to_string_fkey k1 ^ " -> " ^ to_string_fkey k2
let to_string_edges edges = string_of_set ~first:"[" ~last:"]" ~sep:",\n" to_string_edge edges
let print_edges edges = print_endline (to_string_edges edges)

let edges_n : id list -> FuncMap.t -> func -> Node.t -> edge BatSet.t -> edge BatSet.t
= fun cnames fmap curf node edges ->
  let stmt = find_stmt node (Lang.get_cfg curf) in
  match stmt with
  | Call (_,Lv (Var ("contract_init",_)),args,_,_,_,_) ->
    let cnstr_exp, cnstr_args = List.hd args, List.tl args in
    let _ = assert (List.mem (to_string_exp cnstr_exp) cnames) in
    let callees = FuncMap.find_matching_funcs (to_string_exp cnstr_exp) cnstr_exp (List.map get_type_exp cnstr_args) cnames fmap in
    let _ = assert (BatSet.cardinal callees = 1) in
    let callee = BatSet.choose callees in
    BatSet.add (get_fkey curf, get_fkey callee) edges
  | Call (lvop,e,args,ethop,gasop,loc,_) (* built-in functions *)
    when FuncMap.is_undef e (List.map get_type_exp args) fmap ->
    edges
  | Call (_,e,args,_,_,loc,_) -> (* static or object calls *)
    let caller_cname = (get_finfo curf).scope_s in
    let callees = FuncMap.find_matching_funcs caller_cname e (List.map get_type_exp args) cnames fmap in
    BatSet.fold (fun callee acc ->
      BatSet.add (get_fkey curf, get_fkey callee) acc
    ) callees edges
  | _ -> edges

let rec edges_s : id list -> FuncMap.t -> func -> stmt -> edge BatSet.t -> edge BatSet.t
= fun cnames fmap curf stmt edges ->
  match stmt with
  | Assign _ | Decl _ -> edges
  | Seq (s1,s2) -> edges |> edges_s cnames fmap curf s1 |> edges_s cnames fmap curf s2
  | Call (lvop,e,args,ethop,gasop,loc,_) (* built-in functions *)
    when FuncMap.is_undef e (List.map get_type_exp args) fmap -> edges
  | Call (_,e,args,_,_,loc,_) -> (* static or object calls *)
    let caller_cname = (get_finfo curf).scope_s in
    let callees = FuncMap.find_matching_funcs caller_cname e (List.map get_type_exp args) cnames fmap in
    BatSet.fold (fun callee acc ->
      BatSet.add (get_fkey curf, get_fkey callee) acc
    ) callees edges
  | Skip -> edges
  | If (e,s1,s2,i) -> edges |> edges_s cnames fmap curf s1 |> edges_s cnames fmap curf s2
  | While (e,s) -> edges_s cnames fmap curf s edges
  | Break | Continue | Return _
  | Throw | Assume _ | Assert _
  | Assembly _ | PlaceHolder -> edges
  | Unchecked (lst,_) -> list_fold (edges_s cnames fmap curf) lst edges

let edges_f ?(inlined_cfg=true) : id list -> FuncMap.t -> func -> edge BatSet.t -> edge BatSet.t
= fun cnames fmap f edges ->
  if inlined_cfg then
    let nodes = nodes_of (get_cfg f) in
    list_fold (edges_n cnames fmap f) nodes edges
  else
    edges_s cnames fmap f (get_body f) edges

let edges_c ?(inlined_cfg=true) : id list -> FuncMap.t -> contract -> edge BatSet.t -> edge BatSet.t
= fun cnames fmap c edges ->
  list_fold (edges_f ~inlined_cfg cnames fmap) (get_funcs c) edges

let edges_p ?(inlined_cfg=true) : id list -> FuncMap.t -> pgm -> edge BatSet.t
= fun cnames fmap p ->
  list_fold (edges_c ~inlined_cfg cnames fmap) p BatSet.empty

let collect_call_edges ?(inlined_cfg=true) : id list -> FuncMap.t -> pgm -> edge BatSet.t
= fun cnames fmap p ->
  edges_p ~inlined_cfg cnames fmap p

let init_callees : pgm -> fkey BatSet.t
= fun p ->
  let main = get_main_contract p in
  let funcs = List.filter (fun f -> (get_finfo f).fvis = Public || (get_finfo f).fvis = External || is_constructor f) (get_funcs main) in
  BatSet.of_list (List.map get_fkey funcs)

let onestep_callees : fkey BatSet.t -> edge BatSet.t -> fkey BatSet.t
= fun callees edges ->
  BatSet.fold (fun (k1,k2) acc ->
    if BatSet.mem k1 callees then BatSet.add k2 acc
    else acc
  ) edges callees

let onestep_callers : fkey BatSet.t -> edge BatSet.t -> fkey BatSet.t
= fun callers edges ->
  BatSet.fold (fun (k1,k2) acc ->
    if BatSet.mem k2 callers then BatSet.add k1 acc
    else acc
  ) edges callers

let rec fix f : fkey BatSet.t -> edge BatSet.t -> fkey BatSet.t
= fun fkeys edges ->
  let next = f fkeys edges in
  if BatSet.subset next fkeys then next
  else fix f next edges

let transitive_callees : fkey BatSet.t -> edge BatSet.t -> fkey BatSet.t
= fun init edges -> fix onestep_callees init edges

let transitive_callers : fkey BatSet.t -> edge BatSet.t -> fkey BatSet.t
= fun init edges -> fix onestep_callers init edges

let compute_reachable_funcs : id list -> FuncMap.t -> pgm -> fkey BatSet.t
= fun cnames fmap p -> transitive_callees (init_callees p) (collect_call_edges cnames fmap p)

let rm_unreach_c : fkey BatSet.t -> contract -> contract
= fun reachable c ->
  let funcs = get_funcs c in
  let funcs' = List.filter (fun f -> BatSet.mem (get_fkey f) reachable) funcs in
  update_funcs funcs' c

let remove_unreachable_funcs : pgm -> pgm
= fun p ->
  let cnames = get_cnames p in
  let fmap = FuncMap.mk_fmap p in
  let all = get_all_fkeys p in
  let reachable = compute_reachable_funcs cnames fmap p in
  let p' = List.map (rm_unreach_c reachable) p in
  prerr_endline ("- all funcs : " ^ string_of_int (BatSet.cardinal all));
  prerr_endline ("- reachable : " ^ string_of_int (BatSet.cardinal reachable));
  if !Options.debug = "log" then prerr_endline (string_of_set to_string_fkey ~sep:", " reachable);
  p'
