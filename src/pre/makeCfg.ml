open Lang
open Options

let nodesof : cfg -> node list
= fun g -> G.fold_vertex (fun x l -> x :: l) g.graph []

(* unconditionally add edges *)
let add_edge : node -> node -> cfg -> cfg
= fun n1 n2 g -> {g with graph = G.add_edge g.graph n1 n2}

let remove_edge : node -> node -> cfg -> cfg
= fun n1 n2 g -> {g with graph = G.remove_edge g.graph n1 n2}

let add_node : node -> cfg -> cfg
= fun n g -> {g with graph = G.add_vertex g.graph n}

let remove_node : node -> cfg -> cfg
= fun n g ->
  { g with graph = G.remove_vertex g.graph n;
           stmt_map = BatMap.remove n g.stmt_map;
           pre_set = BatSet.remove n g.pre_set;
           lh_set = BatSet.remove n g.lh_set;
           lx_set = BatSet.remove n g.lx_set;
           continue_set = BatSet.remove n g.continue_set;
           break_set = BatSet.remove n g.break_set;
  }

let fold_node f g acc = G.fold_vertex f g.graph acc 
let fold_edges f g acc = G.fold_edges f g.graph acc

let find_stmt : node -> cfg -> stmt
= fun n g -> 
  try if n = Node.ENTRY || n = Node.EXIT then Skip
      else BatMap.find n g.stmt_map
  with _ -> raise (Failure ("No stmt found in the given node " ^ Node.to_string n))

let add_stmt : node -> stmt -> cfg -> cfg
= fun n s g -> {g with stmt_map = BatMap.add n s g.stmt_map}

let add_node_stmt : node -> stmt -> cfg -> cfg
= fun n s g -> g |> add_node n |> add_stmt n s

let pred : node -> cfg -> node list
= fun n g -> G.pred g.graph n

let succ : node -> cfg -> node list
= fun n g -> G.succ g.graph n

let rec has_break_cont : stmt -> bool
= fun s ->
  match s with
  | Assign _ | Decl _ -> false
  | Seq (s1,s2) -> has_break_cont s1 || has_break_cont s2
  | Call _ -> false
  | Skip -> false
  | If (e,s1,s2) -> has_break_cont s1 || has_break_cont s2
  | While _ -> false (* must consider outer loop only. *)
  | Break | Continue -> true
  | Return _ | Throw -> false
  | Assume _ | Assert _ | Assembly _ -> false

let rec trans : stmt -> node option -> node option -> (node * cfg) -> (node * cfg)
= fun stmt lhop lxop (n,g) -> (* lhop : header of dominant loop, lxop : exit of dominant loop, n: interface node *)
  match stmt with
  | Seq (s,While (e,s')) when has_break_cont s ->
    let lh = Node.make () in
    let lx = Node.make () in
    let (n1,g1) = trans s (Some lh) (Some lx) (n,g) in
    let g2 = g1 |> add_node_stmt lh Skip |> add_edge n1 lh in
    let (n3,g3) = trans (Assume (e,0)) (Some lh) (Some lx) (lh,g2) in
    let (n4,g4) = trans s' (Some lh) (Some lx) (n3,g3) in
    let g5 = add_edge n4 lh g4 in
    let (n6,g6) = trans (Assume (UnOp (LNot,e,EType Bool), 0)) lhop lxop (lh,g5) in
    let g7 = g6 |> add_node_stmt lx Skip |> add_edge n6 lx in
    let preds_of_lh = BatSet.of_list (pred lh g2) in
    let _ = assert (BatSet.mem n1 preds_of_lh) in
    let g8 = {g7 with pre_set = BatSet.union preds_of_lh g7.pre_set; lh_set = BatSet.add lh g7.lh_set; lx_set = BatSet.add lx g7.lx_set} in
    (lx, g8)
  | Seq (s1,s2) -> trans s2 lhop lxop (trans s1 lhop lxop (n,g))
  | If (e,s1,s2) ->
    let (tn,g1) = trans (Assume (e,0)) lhop lxop (n,g) in (* tn: true branch assume node *)
    let (tbn,g2) = trans s1 lhop lxop (tn,g1) in
    let (fn,g3) = trans (Assume (UnOp (LNot,e,EType Bool), 0)) lhop lxop (n,g2) in (* fn: false branch assume node *)
    let (fbn,g4) = trans s2 lhop lxop (fn,g3) in
    let join = Node.make () in
    let g5 = g4 |> add_node_stmt join Skip |> add_edge tbn join |> add_edge fbn join in
    (join, g5)
  | While (e,s) ->
    let lh = Node.make () in
    let lx = Node.make () in
    let g1 = g |> add_node_stmt lh Skip |> add_edge n lh in
    let (n2,g2) = trans (Assume (e,0)) (Some lh) (Some lx) (lh,g1) in
    let (n3,g3) = trans s (Some lh) (Some lx) (n2,g2) in
    let g4 = add_edge n3 lh g3 in
    let (n5,g5) = trans (Assume (UnOp (LNot,e,EType Bool), 0)) lhop lxop (lh,g4) in
    let g6 = g5 |> add_node_stmt lx Skip |> add_edge n5 lx in
    let g7 = {g6 with pre_set = BatSet.add n g6.pre_set; lh_set = BatSet.add lh g6.lh_set; lx_set = BatSet.add lx g6.lx_set} in
    (lx, g7)
  | Break ->
    let lx = (match lxop with Some lx -> lx | None -> raise (Failure "Loop exit should exist")) in
    let n' = Node.make () in
    let g' = g |> add_node_stmt n' Skip |> add_edge n n' |> add_edge n' lx in
    (n', {g' with break_set = BatSet.add n' g'.break_set})
  | Continue ->
    let lh = (match lhop with Some lh -> lh | None -> raise (Failure "Loop header should exist")) in
    let n' = Node.make () in
    let g' = g |> add_node_stmt n' Skip |> add_edge n n' |> add_edge n' lh in
    (n', {g' with continue_set = BatSet.add n' g'.continue_set})
  | Return (eop,_) ->
    let n' = Node.make () in
    (Node.exit, g |> add_node_stmt n' stmt |> add_edge n n' |> add_edge n' Node.exit)
  | Assume (BinOp (LAnd,e1,e2,_), loc) ->
    let (n1,g1) = trans (Assume (e1,loc)) lhop lxop (n,g) in
    let (n2,g2) = trans (Assume (e2,loc)) lhop lxop (n1,g1) in
    (n2,g2)
  | Assume (BinOp (LOr,e1,e2,einfo), loc) ->
    let (n1,g1) = trans (Assume (e1,loc)) lhop lxop (n,g) in
    let neg = Assume (BinOp (LAnd, UnOp (LNot,e1,EType Bool), e2, einfo), loc) in
    let (n2,g2) = trans neg lhop lxop (n,g1) in (* should be n, not n1 *)
    let join = Node.make () in
    (join, g2 |> add_node_stmt join Skip |> add_edge n1 join |> add_edge n2 join)
  | Assume (UnOp (LNot, UnOp (LNot,e,t1), t2), loc) -> (* !!e -> e *)
    let stmt' = Assume (e,loc) in
    trans stmt' lhop lxop (n,g)
  | Assume (UnOp (LNot, BinOp (LAnd,e1,e2,einfo), t), loc) -> (* !(e1 && e2) -> !e1 || !e2 *)
    let _ = assert (is_bool t) in
    let stmt' = Assume (BinOp (LOr, UnOp (LNot,e1,t), UnOp (LNot,e2,t), einfo), loc) in
    trans stmt' lhop lxop (n,g)
  | Assume (UnOp (LNot, BinOp (LOr,e1,e2,einfo), t), loc) -> (* !(e1 || e2) -> !e1 && !e2 *)
    let _ = assert (is_bool t) in
    let stmt' = Assume (BinOp (LAnd, UnOp (LNot,e1,t), UnOp (LNot,e2,t), einfo), loc) in
    trans stmt' lhop lxop (n,g)
  | Assume (e,loc) -> (* assumed to be an atomic predicate *)
    let n' = Node.make () in
    let g' = g |> add_node_stmt n' stmt |> add_edge n n' in
    (n',g')
  | Assert (e,loc) -> (* assumed to be an atomic predicate *)
    let n' = Node.make () in
    let g' = g |> add_node_stmt n' stmt |> add_edge n n' in
    (n',g')
  | _ -> 
    let n' = Node.make () in
    (n', g |> add_node_stmt n' stmt |> add_edge n n') 

(* disconnect edges starting from
 * either of
 * an exit, exception (throw or revert), continue, break *)
let disconnect : cfg -> cfg
= fun g ->
  fold_edges (fun n1 n2 acc ->
    if Node.equal n1 Node.exit then
      remove_edge n1 n2 acc else
    if is_exception_node n1 acc then
      acc |> remove_edge n1 n2 |> add_edge n1 Node.exit else (* normalize so that every function has exit node at the end. *)
    if is_continue_node n1 acc && not (is_loophead n2 acc) then
      remove_edge n1 n2 acc else
    if is_break_node n1 acc && not (is_loopexit n2 acc) then
      remove_edge n1 n2 acc
    else acc
  ) g g

let remove_unreach : cfg -> cfg
= fun g ->
  let onestep g nodes = BatSet.fold (fun n acc -> BatSet.union (BatSet.of_list (succ n g)) acc) nodes nodes in
  let reachable = Vocab.fix (onestep g) (BatSet.singleton Node.entry) in
  fold_node (fun n acc ->
    if BatSet.mem n reachable then acc
    else remove_node n acc
  ) g g

(* remove spurious loopheader *)
let inspect_lh : cfg -> cfg
= fun g ->
  fold_node (fun n acc ->
    if is_loophead n acc then
      if List.length (pred n acc) = 1 then (* only precondition exists *)
        {acc with lh_set = BatSet.remove n acc.lh_set}
      else if List.length (pred n acc) >=2 then acc 
      else raise (Failure "should not exist")
    else acc
  ) g g

let unroll : cfg -> cfg
= fun g ->
  let next_node n =
    (match n with
     | Node.ENTRY | Node.EXIT -> raise (Failure "invalid input")
     | Node.Node id -> Node.Node (id+1))
  in
  let (untargeted_lhs, g) =
  fold_edges (fun n1 n2 (tbd_lhs,acc) ->
    if is_loophead n2 acc then
      if is_outer_pred_of_lh n1 acc then (tbd_lhs,acc)
      else
        let acc' = remove_edge n1 n2 acc in
        (* given a loopheader id 'n', its corresponding
         * loopexit id is 'n+1'.
         * See 'trans' function *)
        let loopexit = next_node n2 in 
        let acc'' = add_edge n1 loopexit acc' in
        (BatSet.add n2 tbd_lhs, acc'')
    else (tbd_lhs, acc) 
  ) g (BatSet.empty,g)
  in
  let g = {g with lh_set = BatSet.diff g.lh_set untargeted_lhs} in
  let _ = assert (not (has_loop g)) in
  g

let rec double_loop : stmt -> stmt
= fun stmt ->
  match stmt with
  | Assign _ | Decl _ -> stmt
  | Seq (s1,s2) -> Seq (double_loop s1, double_loop s2)
  | Call _ | Skip -> stmt
  | If (e,s1,s2) -> If (e, double_loop s1, double_loop s2)
  | While (e,s) ->
    let s' = double_loop s in
    Seq (While (e,s'), While (e,s'))
  | Break | Continue | Return _
  | Throw | Assume _ | Assert _ | Assembly _ -> stmt

let convert : stmt -> cfg
= fun stmt ->
  let (n,g) = trans stmt None None (Node.entry, Lang.empty_cfg) in
  let g = add_edge n Node.exit g in
  let g = disconnect g in
  let g = remove_unreach g in
  let g = inspect_lh g in
  g

let run : pgm -> pgm
= fun pgm ->
  List.map (fun contract ->
    let funcs = get_funcs contract in 
    let funcs' =
      List.map (fun func ->
        let body = get_body func in
        let g = convert body in
        let g = {g with signature = get_fkey func} in 
        update_finfo {(get_finfo func) with cfg = g} func
      ) funcs
    in
    update_funcs funcs' contract 
  ) pgm
