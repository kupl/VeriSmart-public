open Lang
open MakeCfg
open Vocab
open FuncMap
open Options

let inline_cnt = ref 0
let update_inline_cnt () = inline_cnt:=!inline_cnt+1
let inline_label () = "__inline" ^ (string_of_int !inline_cnt)

(* after inlining, there may exist exception node somewhere in the middle. *)
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

let rec rename_lv : var list -> lv -> lv
= fun gvars lv ->
  match lv with
  | Var (id,vinfo) ->
    if List.mem (id,vinfo.vtype) gvars then lv
    else Var (id ^ inline_label(), vinfo)
  | MemberAccess (e,id,id_info,typ) when is_enum typ -> lv
  | MemberAccess (e,id,id_info,typ) -> MemberAccess (rename_e gvars e, id, id_info, typ) 
  | IndexAccess (e,None,_) -> raise (Failure "rename_lv")
  | IndexAccess (e1,Some e2,typ) -> IndexAccess (rename_e gvars e1, Some (rename_e gvars e2), typ)
  | Tuple (eoplst,typ) ->
    let eoplst' = 
      List.map (fun eop ->
        match eop with
        | None -> None
        | Some e -> Some (rename_e gvars e)
      ) eoplst
    in
    Tuple (eoplst',typ)

and rename_e : var list -> exp -> exp
= fun gvars exp ->
  match exp with
  | Int _ | Real _ | Str _ -> exp
  | Lv lv ->
    if List.mem (to_string_lv lv) Lang.keyword_vars then Lv lv
    else Lv (rename_lv gvars lv)
  | Cast (typ,e) -> Cast (typ, rename_e gvars e)
  | BinOp (bop,e1,e2,einfo) -> BinOp (bop, rename_e gvars e1, rename_e gvars e2, einfo)
  | UnOp (uop,e,typ) -> UnOp (uop, rename_e gvars e, typ)
  | True | False -> exp
  | ETypeName _ -> exp 
  | IncTemp _ | DecTemp _ | CallTemp _
  | CondTemp _ | AssignTemp _ -> raise (Failure "rename_e")

let rec rename_stmt : func -> var list -> id list -> Node.t -> stmt -> stmt
= fun callee gvars cnames copy_node stmt ->
  match stmt with
  | Assign (lv,exp,loc) -> Assign (rename_lv gvars lv, rename_e gvars exp, loc)
  | Decl lv -> Decl (rename_lv gvars lv)
  | Call (lvop, e, exps, loc, site) ->
    let lvop' =
      (match lvop with
       | None -> lvop
       | Some lv -> Some (rename_lv gvars lv)) in
    let e' =
      (match e with
       | e when List.mem (to_string_exp e) built_in_funcs -> e
       | Lv (Var (fname,info)) -> e
       | Lv (MemberAccess (Lv (Var (prefix,prefix_info)) as arr, fname, fname_info, typ)) ->
         if List.mem prefix cnames || BatString.equal prefix "super" then e
         else Lv (MemberAccess (rename_e gvars arr, fname, fname_info, typ))
       | _ -> e) in
    let exps' =
      if BatString.equal (to_string_exp e) "struct_init" || BatString.equal (to_string_exp e) "contract_init"
        then (List.hd exps)::(List.map (rename_e gvars) (List.tl exps)) (* Rule: the first arg is struct/contract name, see preprocess.ml *)
      else List.map (rename_e gvars) exps in
    Call (lvop', e', exps', loc, site)
  | Skip -> Skip
  | Return (None,_) -> Skip
  | Return (Some e,loc) ->
    let ret_params = get_ret_params callee in
    let lv = params_to_lv ret_params in
    Assign (rename_lv gvars lv, rename_e gvars e, loc)
  | Throw -> Throw
  | Assume (e,loc) -> Assume (rename_e gvars e, loc)
  | Assert (e,loc) -> Assert (rename_e gvars e, loc)
  | Assembly (lst,loc) ->
    let gnames = List.map fst gvars in
    let lst' =
      List.map (fun (x,refid) ->
        if List.mem x gnames then (x,refid)
        else (x ^ inline_label (), refid) 
      ) lst
    in
    Assembly (lst',loc)
  | If _ | Seq _ | While _
  | Break | Continue -> failwith "rename_stmt"

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
    let copied_stmt = rename_stmt callee gvars cnames copied_node (find_stmt node g) in
    let g' = replace_node node (copied_node, copied_stmt) g in
    { g' with pre_set = if BatSet.mem node g.pre_set then BatSet.add copied_node g'.pre_set else g'.pre_set;
              lh_set = if BatSet.mem node g.lh_set then BatSet.add copied_node g'.lh_set else g'.lh_set;
              lx_set = if BatSet.mem node g.lx_set then BatSet.add copied_node g'.lx_set else g'.lx_set;
              continue_set = if BatSet.mem node g.continue_set then BatSet.add copied_node g'.continue_set else g'.continue_set;
              break_set = if BatSet.mem node g.break_set then BatSet.add copied_node g'.break_set else g'.break_set;
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

let inline_n : var list -> id list -> FuncMap.t -> func -> Node.t -> cfg ->
               bool * cfg
= fun gvars cnames fmap caller n g ->
  let stmt = find_stmt n g in
  match stmt with
  | Call (lvop,e,args,loc,_)
    when FuncMap.is_undef e (List.map get_type_exp args) fmap ->
    (false, g) (* built-in functions *)
  | Call (lvop,e,args,loc,_) when is_static_call cnames stmt ->
    let cname = (get_finfo caller).scope_s in
    let callees = FuncMap.find_matching_funcs cname e (List.map get_type_exp args) cnames fmap in
    let _ = assert (BatSet.cardinal callees = 1) in
    let callee = BatSet.choose callees in
    let size_of g =
      fold_node (fun n acc ->
        if is_skip_node n g || is_exception_node n g then acc
        else acc+1
      ) g 0 in
    let _ = if !Options.debug = "inline" then print_endline (get_fname callee ^ ", " ^ string_of_int (size_of (get_cfg callee))) in
    let excessive = size_of (get_cfg callee) > 20 || has_loop (get_cfg callee) in
    if excessive && not !Options.inline_enforce then (false, g)
    else
      (* Do inlining, if not excessive *)
      let _ = update_inline_cnt () in
      let (callee_e, callee_x, callee_g) = mk_cfg_copy callee gvars cnames (get_cfg callee) in
      let preds = pred n g in
      let succs = succ n g in
      let g = remove_node n g in
      let input_node = Node.make () in
      let input_stmt = (* input_params <- args *)
        try
         let lv = rename_lv gvars (params_to_lv (get_params callee)) in 
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
           let e = rename_e gvars (Lv (params_to_lv (get_ret_params callee))) in
           Assign (lv,e,loc))
      in
      let g = add_node_stmt ret_node ret_stmt g in
      let g = add_edge callee_x ret_node g in
      let g = List.fold_left (fun acc s -> add_edge ret_node s acc) g succs in
      let g = { g with pre_set = BatSet.union callee_g.pre_set g.pre_set;
                       lh_set = BatSet.union callee_g.lh_set g.lh_set;
                       lx_set = BatSet.union callee_g.lx_set g.lx_set;
                       continue_set = BatSet.union callee_g.continue_set g.continue_set;
                       break_set = BatSet.union callee_g.break_set g.break_set;}
      in
      (true, g)
  | Call _ -> (false, g) (* object call *)
  | _ -> (false, g)

let inline_f : var list -> id list -> FuncMap.t -> func -> bool * func
= fun gvars cnames fmap f ->
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

let inline_c : var list -> id list -> FuncMap.t -> contract -> bool * contract
= fun gvars cnames fmap c ->
  let funcs = get_funcs c in
  let (changed, funcs) =
    List.fold_left (fun (acc_changed, acc_funcs) f ->
      let (changed', f') = inline_f gvars cnames fmap f in
      (acc_changed || changed', acc_funcs @ [f'])
    ) (false,[]) funcs
  in
  (changed, update_funcs funcs c)

(* inline once *)
let inline_p : pgm -> bool * pgm
= fun p ->
  let gvars = get_gvars p in
  let fmap = FuncMap.mk_fmap p in
  let cnames = get_cnames p in
  List.fold_left (fun (acc_changed, acc_p) c ->
    let (changed', c') =
      if BatString.equal (get_cname c) !Options.main_contract (* currently, inline only functions within main contract *)
        then inline_c gvars cnames fmap c
      else (false, c) in
    (acc_changed || changed', acc_p@[c'])
  ) (false,[]) p

(* inline until no function calls exist. *)
let rec inline_all : pgm -> pgm
= fun p ->
  let (changed, p') = inline_p p in
  if not changed then p'
  else inline_all p'

let is_target_node cnames fmap n g =
  let stmt = find_stmt n g in
  match stmt with
  | Call (lvop,e,args,loc,_) when (FuncMap.is_undef e (List.map get_type_exp args) fmap) -> false
  | Call _ -> is_static_call cnames stmt
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

let rec inline_ntimes : int -> pgm -> pgm
= fun n p ->
  let _ = assert (n>=0) in
  if n=0 then p
  else
    let (changed,p') = inline_p p in
    if not changed then p'
    else inline_ntimes (n-1) p'

let run : pgm -> pgm
= fun p -> inline_ntimes !Options.inline_depth p
