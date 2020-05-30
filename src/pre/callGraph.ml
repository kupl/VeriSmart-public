open Lang
open Vocab
open FuncMap

let compute_call_edges_n : id list -> FuncMap.t -> Node.t -> cfg -> (fkey * fkey) BatSet.t
= fun cnames fmap n g ->
  let (cname,_,_) = g.signature in
  let stmt = find_stmt n g in
  match stmt with
  | Call (_,Lv (Var ("contract_init",_)),args,_,_) ->
    let cnstr_exp, cnstr_args = List.hd args, List.tl args in
    let _ = assert (List.mem (to_string_exp cnstr_exp) cnames) in
    let callees = find_matching_funcs (to_string_exp cnstr_exp) cnstr_exp (List.map get_type_exp cnstr_args) cnames fmap in
    let _ = assert (BatSet.cardinal callees = 1) in
    let callee = BatSet.choose callees in
    BatSet.singleton (g.signature, get_fkey callee)
  | Call (_,e,args,_,_)
    when FuncMap.is_undef e (List.map get_type_exp args) fmap ->
    BatSet.empty
  | Call (_,e,args,loc,_) ->
    let callees = find_matching_funcs cname e (List.map get_type_exp args) cnames fmap in
    BatSet.fold (fun callee acc ->
      BatSet.add (g.signature, get_fkey callee) acc 
    ) callees BatSet.empty
  | _ -> BatSet.empty

let compute_call_edges_f : id list -> FuncMap.t -> func -> (fkey * fkey) BatSet.t
= fun cnames fmap f ->
  let g = get_cfg f in
  let nodes = nodes_of g in
  List.fold_left (fun acc n ->
    BatSet.union (compute_call_edges_n cnames fmap n g) acc 
  ) BatSet.empty nodes

let compute_call_edges_c : id list -> FuncMap.t -> contract -> (fkey * fkey) BatSet.t
= fun cnames fmap c ->
  let funcs = get_funcs c in
  List.fold_left (fun acc f ->
    BatSet.union (compute_call_edges_f cnames fmap f) acc 
  ) BatSet.empty funcs

let compute_call_edges_p : id list -> FuncMap.t -> pgm -> (fkey * fkey) BatSet.t
= fun cnames fmap p ->
  List.fold_left (fun acc c ->
    BatSet.union (compute_call_edges_c cnames fmap c) acc
  ) BatSet.empty p

let compute_call_edges : id list -> FuncMap.t -> pgm -> (fkey * fkey) BatSet.t
= fun cnames fmap p -> compute_call_edges_p cnames fmap p

let init_callees : pgm -> fkey BatSet.t
= fun p ->
  let main = get_main_contract p in
  let funcs = List.filter (fun f -> (get_finfo f).fvis = Public || (get_finfo f).fvis = External || is_constructor f) (get_funcs main) in 
  BatSet.of_list (List.map get_fkey funcs)

let onestep_callees : fkey BatSet.t -> (fkey * fkey) BatSet.t -> fkey BatSet.t
= fun callees edges ->
  BatSet.fold (fun (k1,k2) acc ->
    if BatSet.mem k1 callees then BatSet.add k2 acc
    else acc
  ) edges callees

let rec compute_trans_callees : fkey BatSet.t -> (fkey * fkey) BatSet.t -> fkey BatSet.t
= fun callees edges ->
  let callees' = onestep_callees callees edges in
    if BatSet.subset callees' callees then callees'
    else compute_trans_callees callees' edges
  
let compute_reachable_funcs : id list -> FuncMap.t -> pgm -> fkey BatSet.t
= fun cnames fmap p -> compute_trans_callees (init_callees p) (compute_call_edges cnames fmap p)

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
