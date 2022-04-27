open Lang
open MakeCfg
open Vlang
open Vocab
open CallGraph
open Options

let call_extern rcv loc =
  Call (None, Lv (Var ("@extern", dummy_vinfo)), [rcv], None, None, loc, -1)

let is_pseudo_stmt_node : node -> cfg -> bool
= fun n g ->
  let stmt = find_stmt n g in
  match stmt with
  | Assign (lv,e,_) ->
    BatSet.exists (fun x -> BatString.starts_with (fst x) "@") (BatSet.union (var_lv lv) (var_exp e))
  | Assume (e,_) ->
    BatSet.exists (fun x -> BatString.starts_with (fst x) "@") (var_exp e)
  | _ -> false

(**************************************************)
(*** Desugar built-in functions that send money ***)
(**************************************************)

let rec convert_call_s : id list -> FuncMap.t -> stmt -> stmt
= fun cnames fmap stmt ->
  match stmt with
  | Assign _ | Decl _ -> stmt
  | Seq (s1,s2) -> Seq (convert_call_s cnames fmap s1, convert_call_s cnames fmap s2)

  | Call (lvop, Lv (MemberAccess (e,"call",_,_)), args, Some eth, gasop, loc, id)
    when is_address (get_type_exp e) ->
   
    let balance_info = mk_vinfo ~typ:(EType (UInt 256)) () in
    let this_info = mk_vinfo ~typ:(Contract !main_contract) () in
    let this = Cast (EType Address, Lv (Var ("this", this_info))) in
    let this_balance = MemberAccess (this,"balance", balance_info, EType (UInt 256)) in
    let rcv_balance = MemberAccess (e, "balance", balance_info, EType (UInt 256)) in

    let invest_map = Var ("@Invest", mk_vinfo ~typ:(Mapping (Address, EType (UInt 256))) ()) in
    let rcv_invest = IndexAccess (Lv invest_map, Some e, EType (UInt 256)) in

    let eth' =
      match eth with
      | BinOp (Mul, Lv v1, Lv (Var (v,_)), _) when BatString.starts_with v "sellPrice" -> Lv v1
      | _ -> eth in
    let invest_sum = Var ("@Invest_sum", mk_vinfo ~typ:(EType (UInt 256)) ()) in
    let trust_map = Var ("@TU", mk_vinfo ~typ:(Mapping (Address, EType Bool)) ()) in
    let not_trusted = mk_eq (Lv (IndexAccess (Lv trust_map, Some e, EType Bool))) False in
    let invest_sum_stmt = If (not_trusted, Assign (invest_sum, mk_sub (Lv invest_sum) eth', dummy_loc), Skip, dummy_ifinfo) in

    let cond1 = mk_ge (Lv this_balance) eth in
    let cond2 = mk_ge (mk_add (Lv rcv_balance) eth) (Lv rcv_balance) in
    let true_b = Seq (Assign (this_balance, mk_sub (Lv this_balance) eth, dummy_loc), Assign (rcv_balance, mk_add (Lv rcv_balance) eth, dummy_loc)) in
    let true_b = Seq (true_b, Assign (rcv_invest, mk_sub (Lv rcv_invest) eth, dummy_loc)) in
    let true_b = Seq (true_b, invest_sum_stmt) in
    let true_b = Seq (true_b, call_extern e loc) in
    (* let true_b = Seq (call_extern e loc, true_b) in *)

    let true_b = Seq (stmt, true_b) in
    let false_b = Skip in
    let true_b, false_b =
      (match lvop with
       | None -> true_b, false_b
       | Some (Tuple (Some (Lv (Var v))::_,_))
       | Some (Var v) -> Seq (true_b, Assign (Var v, True, dummy_loc)), Seq (false_b, Assign (Var v, False, dummy_loc))
       | _  -> assert false) in
    let if_stmt = If (mk_and cond1 cond2, true_b, false_b, dummy_ifinfo) in
    if_stmt

  | Call (lvop,Lv (MemberAccess (e,instr,_,_)),args, _, _, loc, _)
    when is_address (get_type_exp e) && List.mem instr ["send"; "transfer"] ->
    let _ = assert (no_eth_gas_modifiers stmt) in
    let _ = assert (List.length args = 1) in
    let eth = List.hd args in
    let balance_info = mk_vinfo ~typ:(EType (UInt 256)) () in
    let this_info = mk_vinfo ~typ:(Contract !main_contract) () in
    let this = Cast (EType Address, Lv (Var ("this", this_info))) in
    let this_balance = MemberAccess (this,"balance", balance_info, EType (UInt 256)) in
    let rcv_balance = MemberAccess (e, "balance", balance_info, EType (UInt 256)) in

    let invest_map = Var ("@Invest", mk_vinfo ~typ:(Mapping (Address, EType (UInt 256))) ()) in
    let rcv_invest = IndexAccess (Lv invest_map, Some e, EType (UInt 256)) in

    let eth' =
     match eth with
     | BinOp (Mul, Lv v1, Lv (Var (v,_)), _) when BatString.starts_with v "sellPrice" -> Lv v1
     | _ -> eth in
    let invest_sum = Var ("@Invest_sum", mk_vinfo ~typ:(EType (UInt 256)) ()) in
    let trust_map = Var ("@TU", mk_vinfo ~typ:(Mapping (Address, EType Bool)) ()) in
    let not_trusted = mk_eq (Lv (IndexAccess (Lv trust_map, Some e, EType Bool))) False in
    let invest_sum_stmt = If (not_trusted, Assign (invest_sum, mk_sub (Lv invest_sum) eth', dummy_loc), Skip, dummy_ifinfo) in

    let cond1 = mk_ge (Lv this_balance) eth in
    let cond2 = mk_ge (mk_add (Lv rcv_balance) eth) (Lv rcv_balance) in
    let true_b = Seq (Assign (this_balance, mk_sub (Lv this_balance) eth, dummy_loc), Assign (rcv_balance, mk_add (Lv rcv_balance) eth, dummy_loc)) in
    let true_b = Seq (true_b, Assign (rcv_invest, mk_sub (Lv rcv_invest) eth, dummy_loc)) in
    let true_b = Seq (true_b, invest_sum_stmt) in
    let true_b = Seq (stmt, true_b) in
    let false_b =
      if instr = "transfer" then Throw
      else if instr = "send" then
        (match lvop with
         | None -> Skip
         | Some lv -> Assign (lv, False, dummy_loc))
      else assert false in
    let if_stmt = If (mk_and cond1 cond2, true_b, false_b, dummy_ifinfo) in
    (match instr with
     | "transfer" -> if_stmt
     | "send" -> if_stmt
     | _ -> assert false)

    (* built-in functions *)
  | Call (lvop,e,args,ethop,gasop,loc,_)
    when FuncMap.is_undef e (List.map get_type_exp args) fmap -> stmt

    (* internal call *)
  | Call (lvop,e,args,ethop,gasop,loc,_)
    when is_internal_call fmap cnames stmt -> stmt

    (* external calls *)
  | Call (lvop,e,args,ethop,gasop,loc,_) ->
    let rcv = match e with Lv (MemberAccess (rcv,_,_,_)) -> rcv | _ -> assert false in
    let callees = FuncMap.find_matching_funcs "" e (List.map get_type_exp args) cnames fmap in
    if BatSet.for_all is_view_pure_f callees then stmt (* non-modifiable calls are considered to be harmless *)
    else
      Seq (stmt, call_extern rcv loc)

  | Skip -> stmt
  | If (e,s1,s2,i) -> If (e, convert_call_s cnames fmap s1, convert_call_s cnames fmap s2, i)
  | While (e,s) -> While (e, convert_call_s cnames fmap s)
  | Break | Continue | Return _ | Throw
  | Assume _ | Assert _ | Assembly _ | PlaceHolder -> stmt
  | Unchecked (lst,loc) ->
    let lst' = List.map (convert_call_s cnames fmap) lst in
    Unchecked (lst',loc)

let do_all_f cnames fmap func =
  let body = get_body func in
  let body = convert_call_s cnames fmap body in
  let body = if is_constructor func then body else body in
  update_body body func

let do_all_c cnames fmap c =
  let funcs = get_funcs c in
  let funcs' = List.map (do_all_f cnames fmap) funcs in
  update_funcs funcs' c

let do_all cnames fmap p = List.map (do_all_c cnames fmap) p

let run : pgm -> pgm
= fun p ->
  let fmap = FuncMap.mk_fmap p in
  let cnames = get_cnames p in
  do_all cnames fmap p
