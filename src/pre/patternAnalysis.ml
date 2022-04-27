open Vocab
open Lang
open MakeCfg
open Path
open Global

let may_violate_cei = ref false
let may_call_itself = ref false

let may_update_state_f : Global.t -> func -> bool
= fun global f ->
  let defs = FuncDefUse.find_def_set (Lang.get_fkey f) global.f_defuse in
  let field_names = Global.get_all_fields global |> List.map fst in
  is_payable f
  || BatSet.exists (fun d -> List.mem d (List.map fst global.gvars) || d = "@Invest_sum" || List.mem d field_names) defs

let is_state_manipulating_assign : Global.t -> stmt -> bool
= fun global stmt ->
  let fields = Global.get_all_fields global in
  let field_names = List.map fst fields in
  match stmt with
  | Assign (lv,_,_) ->
    let defs = FuncDefUse.get_def_set_lv lv in
    BatSet.exists (fun d -> List.mem d (List.map fst global.gvars) || d = "@Invest_sum" || List.mem d field_names) defs
  | _ -> false

let may_update_state : Global.t -> func -> Node.t -> bool
= fun global curf n ->
  let g = get_cfg curf in
  let stmt = find_stmt n g in
  match stmt with
  | _ when is_state_manipulating_assign global stmt -> true
  | Call (lvop,e,args,ehtop,gasop,loc,_) when is_undef_call global.fmap stmt ->
    (match lvop with
     | None -> false
     | Some lv ->
       let fields = Global.get_all_fields global in
       let field_names = List.map fst fields in
       let defs = FuncDefUse.get_def_set_lv lv in
       BatSet.exists (fun d -> List.mem d (List.map fst global.gvars) || d = "@Invest_sum" || List.mem d field_names) defs)
  | Call (lvop,e,args,ehtop,gasop,loc,_) when is_internal_call global.fmap global.cnames stmt ->
    let _ = assert (no_eth_gas_modifiers stmt) in
    let callee = get_callee_of_intcall global curf stmt in
    may_update_state_f global callee
  | _ -> false

let callee_contain_extcall : Global.t -> func -> Node.t -> cfg -> bool
= fun global f n g ->
  let callee = get_callee_of_intcall global f (find_stmt n g) in
  contain_extern global callee

let get_ext_nodes : Global.t -> Path.t -> int list
= fun global (fk,nodes) ->
  let f = FuncMap.find fk global.fmap in
  let g = get_cfg f in
  BatList.fold_lefti (fun acc i n ->
    if is_external_call_node n g then acc @ [i]
    else if is_internal_call_node global.fmap global.cnames n g then
      if callee_contain_extcall global f n g then acc @ [i]
      else acc
    else acc
  ) [] nodes

let get_state_nodes : Global.t -> Path.t -> int list
= fun global (fk,nodes) ->
  let f = FuncMap.find fk global.fmap in
  BatList.fold_lefti (fun acc i n ->
    if may_update_state global f n then acc @ [i]
    else acc
  ) [] nodes

let check_cei' : Global.t -> Path.t -> bool
= fun global path ->
  let ext_nodes = get_ext_nodes global path in
  let state_nodes = get_state_nodes global path in
  (* let _ = print_endline (Path.to_string path) in *)
  List.for_all (fun e ->
    List.for_all (fun s ->
      (* let _ = print_endline (string_of_int e) in
      let _ = print_endline (string_of_int s) in
      let  _ = print_endline "" in *)
      s < e) state_nodes
  ) ext_nodes

let check_cei : Global.t -> PathSet.t -> bool
= fun global paths -> PathSet.for_all (check_cei' global) paths

let check_recursive'' : Global.t -> cfg -> Node.t -> bool
= fun global g node ->
  let stmt = find_stmt node g in
  match stmt with
    (* built-in functions *)
  | Call (lvop,e,args,ethop,gasop,loc,_) when FuncMap.is_undef e (List.map get_type_exp args) global.fmap -> false
  | Call (lvop,e,args,ethop,gasop,loc,_) when is_internal_call global.fmap global.cnames stmt -> false
    (* external call *)
  | Call (lvop,e,args,ethop,gasop,loc,_) ->
    let rcv = match e with Lv (MemberAccess (rcv,_,_,_)) -> rcv | _ -> assert false in
    (match get_type_exp rcv with
     | Contract c -> List.mem c global.base_names
     | _ -> assert false)
  | _ -> false

let check_recursive' : Global.t -> Path.t -> bool
= fun global (fk,nodes) ->
  let f = FuncMap.find fk global.fmap in
  let g = get_cfg f in
  List.exists (check_recursive'' global g) nodes

let check_recursive : Global.t -> PathSet.t -> bool
= fun global paths -> PathSet.exists (check_recursive' global) paths

let run : Global.t -> PathSet.t -> unit
= fun global paths ->
  let _ = may_call_itself := check_recursive global paths in
  let _ = may_violate_cei := not (check_cei global paths) in
  let _ = print_endline ("[INFO] Violate CEI: " ^ string_of_bool !may_violate_cei) in
  let _ = print_endline ("[INFO] msg.sender = this possible: " ^ string_of_bool !may_call_itself) in
  ()
