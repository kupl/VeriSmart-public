open Lang
open MakeCfg
open Vocab
open FuncMap
open Options

let inline_cnt = ref 0
let update_inline_cnt () = inline_cnt:=!inline_cnt+1
let inline_label () = "__inline" ^ (string_of_int !inline_cnt)

let postprocess : cfg -> cfg
= fun g ->
  let g' =
    fold_edges (fun n1 n2 acc ->
      if is_exception_node n1 acc then
        acc |> remove_edge n1 n2 |> add_edge n1 Node.exit
      else acc
    ) g g
  in
  remove_unreach g'

let rec msg_lv lv =
  match lv with
  | Var x -> lv
  | MemberAccess (e,x,xinfo,typ) -> MemberAccess (msg_e e, x, xinfo, typ)
  | IndexAccess (e,None,_) -> assert false
  | IndexAccess (e1,Some e2,typ) -> IndexAccess (msg_e e1, Some (msg_e e2), typ)
  | Tuple (eoplst,typ) ->
    eoplst
    |> List.map (fun eop -> match eop with None -> None | Some e -> Some (msg_e e))
    |> (fun eoplst' -> Tuple (eoplst',typ))

and msg_e exp =
  match exp with
  | Int _ | Real _ | Str _ -> exp
  | Lv lv when to_string_lv lv = "msg.sender" -> Lv (Var ca)
  | Lv lv -> Lv (msg_lv lv)
  | Cast (t,e) -> Cast (t, msg_e e)
  | BinOp (bop,e1,e2,einfo) -> BinOp (bop, msg_e e1, msg_e e2, einfo)
  | UnOp (uop,e,t) -> UnOp (uop, msg_e e, t)
  | True | False | ETypeName _ -> exp
  | _ -> assert false

let rec msg_s stmt =
  match stmt with
  | Assign (lv,e,loc) -> Assign (msg_lv lv, msg_e e, loc)
  | Decl lv -> Decl (msg_lv lv)
  | Seq (s1,s2) -> Seq (msg_s s1, msg_s s2)
  | Call (lvop, e, args, ethop, gasop, loc, id) ->
    let lvop' = match lvop with None -> lvop | Some lv -> Some (msg_lv lv) in
    let e' = msg_e e in
    let args' = List.map msg_e args in
    let ethop' = match ethop with None -> ethop | Some e -> Some (msg_e e) in
    let gasop' = match gasop with None -> gasop | Some e -> Some (msg_e e) in
    Call (lvop', e', args', ethop', gasop', loc, id)
  | Skip -> stmt
  | If (e,s1,s2,i) -> If (msg_e e, msg_s s1, msg_s s2, i)
  | While (e,s) -> While (msg_e e, msg_s s)
  | Break | Continue -> stmt
  | Return (eop,loc) ->
    let eop' = match eop with None -> eop | Some e -> Some (msg_e e) in
    Return (eop',loc)
  | Throw -> stmt
  | Assume (e,loc) -> Assume (msg_e e, loc)
  | Assert (e,vtyp,loc) -> Assert (msg_e e, vtyp, loc)
  | Assembly _ | PlaceHolder -> stmt
  | Unchecked _ -> assert false

let replace_msg : cfg -> cfg
= fun g ->
  fold_node (fun n acc ->
    if BatSet.mem n acc.extern_set then
      add_node_stmt n (msg_s (find_stmt n acc)) acc
    else acc
  ) g g

(* after inlining, there may exist exception node somewhere in the middle. *)
let connect_exception_to_exit : cfg -> cfg
= fun g ->
  fold_edges (fun n1 n2 acc ->
    if is_exception_node n1 acc then
      acc |> remove_edge n1 n2 |> add_edge n1 Node.exit
    else acc
  ) g g

let postprocess : cfg -> cfg
= fun g -> g |> connect_exception_to_exit |> remove_unreach |> replace_msg

let rename_stmt' : func -> var list -> id list -> stmt -> stmt
= fun callee gvars cnames stmt ->
  let lab = inline_label () in
  match stmt with
  | Return (None,_) -> Skip
  | Return (Some e,loc) ->
    let ret_params = get_ret_params callee in
    let lv = params_to_lv ret_params in
    Assign (rename_lv lab gvars lv, rename_e lab gvars e, loc)
  | If _ | Seq _ | While _
  | Break | Continue | Unchecked _ -> assert false
  | _ -> rename_stmt lab gvars cnames stmt

let replace_node : Node.t -> (Node.t * stmt) -> cfg -> cfg
= fun target (new_node,new_stmt) g ->
  let preds = pred target g in
  let succs = succ target g in
  let g = remove_node target g in
  let g = add_node_stmt new_node new_stmt g in
  let g = List.fold_left (fun acc p -> add_edge p new_node acc) g preds in
  let g = List.fold_left (fun acc s -> add_edge new_node s acc) g succs in
  g

let copy_node : func -> var list -> id list -> Node.t -> cfg -> cfg
= fun callee gvars cnames node g ->
  if is_entry node then g else
  if is_exit node then g
  else
    let copied_node = Node.make () in
    let copied_stmt = rename_stmt' callee gvars cnames (find_stmt node g) in
    let g' = replace_node node (copied_node, copied_stmt) g in
    { g' with outpreds_of_lh = if BatSet.mem node g.outpreds_of_lh then BatSet.add copied_node g'.outpreds_of_lh else g'.outpreds_of_lh;
              lh_set = if BatSet.mem node g.lh_set then BatSet.add copied_node g'.lh_set else g'.lh_set;
              lx_set = if BatSet.mem node g.lx_set then BatSet.add copied_node g'.lx_set else g'.lx_set;
              continue_set = if BatSet.mem node g.continue_set then BatSet.add copied_node g'.continue_set else g'.continue_set;
              break_set = if BatSet.mem node g.break_set then BatSet.add copied_node g'.break_set else g'.break_set;
              extern_set = if BatSet.mem node g.extern_set then BatSet.add copied_node g'.extern_set else g'.extern_set
    }

(* returns (entry_node * exit_node * copied graph) *)
let mk_cfg_copy : func -> var list -> id list -> cfg ->
                  Node.t * Node.t * cfg
= fun callee gvars cnames g ->
  let nodes = nodes_of g in
  let g = List.fold_left (fun g' n -> copy_node callee gvars cnames n g') g nodes in
  let entry_node = Node.make () in
  let exit_node = Node.make () in
  let g = replace_node Node.entry (entry_node,Skip) g in
  let g = replace_node Node.exit (exit_node,Skip) g in
  (entry_node, exit_node, g)

(*
let is_recursive_callnode : ctx -> int -> Node.t -> bool
= fun ctx site n ->
  let ctx_n = try BatMap.find n ctx with Not_found -> [] in
  let inlined = List.find_all (fun (l,s') -> site = s') ctx_n in
  List.length inlined >= 2
*)

let is_uint_assign_node n g =
  match find_stmt n g with
  | Assign (lv,_,_) when is_uintkind (get_type_lv lv) -> true
  | _ -> false

let inline_n : var list -> id list -> FuncMap.t -> func -> Node.t -> cfg ->
               bool * cfg
= fun gvars cnames fmap caller n g ->
  let stmt = find_stmt n g in
  match stmt with
  | Call (lvop,e,args,_,_,loc,_)
    when FuncMap.is_undef e (List.map get_type_exp args) fmap -> (* built-in functions *)
    (false, g)

  | Call (lvop,Lv (Var ("@extern",_)),args,_,_,loc,_) when (get_fname caller) = "@extern" ->
    let _ = assert (!Options.mode = "exploit") in
    let g = replace_node n (n,Skip) g in
    (true, g)

  | Call (lvop,e,args,_,_,loc,_) when is_internal_call fmap cnames stmt ->
    let cname = (get_finfo caller).scope_s in
    let callees = FuncMap.find_matching_funcs cname e (List.map get_type_exp args) cnames fmap in
    let _ = assert (BatSet.cardinal callees = 1) in
    let callee = BatSet.choose callees in
    let size_of g =
      fold_node (fun n acc ->
        if not (Preprocess2.is_pseudo_stmt_node n g) && is_uint_assign_node n g then acc+1
        else if is_internal_call_node fmap cnames n g then acc+1
        else acc
      ) g 0
    in
    let _ = if !Options.debug = "inline" then print_endline (get_fname callee ^ ", " ^ string_of_int (size_of (get_cfg callee))) in
    let excessive = size_of (get_cfg callee) > 5 || has_loop (get_cfg callee) in
    if not (!Options.mode="exploit") && excessive && not !Options.inline_enforce then (false, g)
    else
      (* Do inlining, if exploit mode or not excessive *)
      let _ = update_inline_cnt () in
      let (callee_e, callee_x, callee_g) = mk_cfg_copy callee gvars cnames (get_cfg callee) in
      let preds = pred n g in
      let succs = succ n g in
      let g = remove_node n g in
      let input_node = Node.make () in
      let input_stmt = (* input_params <- args *)
        try
         let lv = rename_lv (inline_label()) gvars (params_to_lv (get_params callee)) in
         Assign (lv, args_to_exp args, loc)
        with NoParameters -> Skip
      in 
      let g = add_node_stmt input_node input_stmt g in 
      let g = List.fold_left (fun acc p -> add_edge p input_node acc) g preds in
      let g = add_node_stmt callee_e (find_stmt callee_e callee_g) g in
      let g = add_edge input_node callee_e g in
      let g =
        G.fold_edges (fun src dst acc ->
          let acc = add_node_stmt src (find_stmt src callee_g) acc in
          let acc = add_node_stmt dst (find_stmt dst callee_g) acc in
          add_edge src dst acc
        ) callee_g.graph g in
      let ret_node = Node.make () in
      let ret_stmt = 
        (match lvop with
         | None -> Skip
         | Some lv -> (* lv <- ret_params when 'lv:= call()' *)
           let e = rename_e (inline_label()) gvars (Lv (params_to_lv (get_ret_params callee))) in
           Assign (lv,e,loc))
      in
      let g = add_node_stmt ret_node ret_stmt g in
      let g = add_edge callee_x ret_node g in
      let g = List.fold_left (fun acc s -> add_edge ret_node s acc) g succs in
      { g with outpreds_of_lh = BatSet.union callee_g.outpreds_of_lh g.outpreds_of_lh;
               lh_set = BatSet.union callee_g.lh_set g.lh_set;
               lx_set = BatSet.union callee_g.lx_set g.lx_set;
               continue_set = BatSet.union callee_g.continue_set g.continue_set;
               break_set = BatSet.union callee_g.break_set g.break_set;
               extern_set = if get_fname callee ="@extern" then BatSet.union (BatSet.of_list (nodes_of (callee_g))) g.extern_set else g.extern_set;
      }
      |> (fun g -> (true,g))
  | Call _ -> (false, g) (* object call *)
  | _ -> (false, g)

let inline_f ~extern:b : var list -> id list -> FuncMap.t -> func -> bool * func
= fun gvars cnames fmap f ->
  if b && not (get_fname f = "@extern") then (false, f)
  else
    let g = get_cfg f in
    let nodes = nodes_of g in
    let (changed, g') =
      List.fold_left (fun (acc_changed, acc_g) n ->
        let (new_changed, new_g) = inline_n gvars cnames fmap f n acc_g in
        (acc_changed || new_changed, new_g)
      ) (false,g) nodes
    in
    let g'' = postprocess g' in
    (changed, update_cfg f g'') (* cfg is updated whenever inlining is conducted. *)

let inline_c ~extern:b : var list -> id list -> FuncMap.t -> contract -> bool * contract
= fun gvars cnames fmap c ->
  let funcs = get_funcs c in
  let (changed, funcs) =
    List.fold_left (fun (acc_changed, acc_funcs) f ->
      let (changed', f') = inline_f ~extern:b gvars cnames fmap f in
      (acc_changed || changed', acc_funcs @ [f'])
    ) (false,[]) funcs
  in
  (changed, update_funcs funcs c)

(* inline once *)
let inline_p ~extern:b : pgm -> bool * pgm
= fun p ->
  let gvars = get_gvars p in
  let fmap = FuncMap.mk_fmap p in
  let cnames = get_cnames p in
  let base_names,_ = Global.get_basenames p in
  List.fold_left (fun (acc_changed, acc_p) c ->
    let (changed', c') =
      (* currently, inline only main and its parent (to handle 'super' keyword) contracts *)
      if List.mem (get_cname c) base_names then
        inline_c ~extern:b gvars cnames fmap c
      else (false, c) in
    (acc_changed || changed', acc_p@[c'])
  ) (false,[]) p

let is_target_node cnames fmap n g =
  let stmt = find_stmt n g in
  match stmt with
  | Call (lvop,e,args,_,_,loc,_) when (FuncMap.is_undef e (List.map get_type_exp args) fmap) -> false
  | Call _ -> is_internal_call fmap cnames stmt
  | _ -> false

let remove_call_f cnames fmap f =
  let g = get_cfg f in
  let g' =
    fold_node (fun n acc ->
      if is_target_node cnames fmap n acc then add_node_stmt n Throw acc
      else acc
    ) g g
  in
  let g'' = postprocess g' in
  (update_cfg f g'')

let remove_call_c cnames fmap c =
  let funcs' = List.map (remove_call_f cnames fmap) (get_funcs c) in
  update_funcs funcs' c

let remove_call_p p =
  let cnames = get_cnames p in
  let fmap = FuncMap.mk_fmap p in
  List.map (remove_call_c cnames fmap) p

let rec inline_ntimes ~extern:b : int -> pgm -> pgm
= fun n p ->
  let _ = assert (n>=0) in
  if n=0 then
    if !Options.mode="exploit" && not b then remove_call_p p
    else p
  else
    let (changed,p') = inline_p ~extern:b p in
    if not changed then p'
    else inline_ntimes ~extern:b (n-1) p'

let run : pgm -> pgm
= fun p ->
  p
  |> inline_ntimes ~extern:true !Options.inline_depth (* finitize @extern first *)
  |> inline_ntimes ~extern:false !Options.inline_depth
