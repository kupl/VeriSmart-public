open Lang
open Vlang
open Vocab
open CallGraph
open Options

let rec convert_call_s : stmt -> stmt
= fun stmt ->
  match stmt with
  | Assign _ | Decl _ -> stmt
  | Seq (s1,s2) -> Seq (convert_call_s s1, convert_call_s s2)
  | Call (lvop, Lv (MemberAccess (e,"call",_,_)), args, Some eth, gasop, loc, id)
    when is_address (get_type_exp e) ->

    let balance_info = dummy_vinfo_with_typ_org (EType (UInt 256)) "balance" in
    let this_info = dummy_vinfo_with_typ_org (Contract !main_contract) "this" in
    let this = Cast (EType Address, Lv (Var ("this", this_info))) in
    let this_balance = MemberAccess (this,"balance", balance_info, EType (UInt 256)) in
    let rcv_balance = MemberAccess (e, "balance", balance_info, EType (UInt 256)) in

    let invest_map = Var ("@Invest", dummy_vinfo_with_typ_org (Mapping (Address, EType (UInt 256))) "@Invest") in
    let rcv_invest = IndexAccess (Lv invest_map, Some e, EType (UInt 256)) in

    let cond1 = mk_ge (Lv this_balance) eth in
    let cond2 = mk_ge (mk_add (Lv rcv_balance) eth) (Lv rcv_balance) in
    let true_b = Seq (Assign (this_balance, mk_sub (Lv this_balance) eth, loc), Assign (rcv_balance, mk_add (Lv rcv_balance) eth, loc)) in
    let true_b = Seq (true_b, Assign (rcv_invest, mk_sub (Lv rcv_invest) eth, loc)) in
    let true_b = Seq (stmt, true_b) in
    let false_b = Skip in
    let if_stmt = If (mk_and cond1 cond2, true_b, false_b) in
    if_stmt

  | Call (lvop,Lv (MemberAccess (e,"send",_,_)),args, _, _, loc, _)
    when is_address (get_type_exp e) ->
    let _ = assert (no_eth_gas_modifiers stmt) in
    let _ = assert (List.length args = 1) in
    let eth = List.hd args in
    let balance_info = dummy_vinfo_with_typ_org (EType (UInt 256)) "balance" in
    let this_info = dummy_vinfo_with_typ_org (Contract !main_contract) "this" in
    let this = Cast (EType Address, Lv (Var ("this", this_info))) in
    let this_balance = MemberAccess (this,"balance", balance_info, EType (UInt 256)) in
    let rcv_balance = MemberAccess (e, "balance", balance_info, EType (UInt 256)) in

    let invest_map = Var ("@Invest", dummy_vinfo_with_typ_org (Mapping (Address, EType (UInt 256))) "@Invest") in
    let rcv_invest = IndexAccess (Lv invest_map, Some e, EType (UInt 256)) in

    let cond1 = mk_ge (Lv this_balance) eth in
    let cond2 = mk_ge (mk_add (Lv rcv_balance) eth) (Lv rcv_balance) in
    let true_b = Seq (Assign (this_balance, mk_sub (Lv this_balance) eth, loc), Assign (rcv_balance, mk_add (Lv rcv_balance) eth, loc)) in
    let true_b = Seq (true_b, Assign (rcv_invest, mk_sub (Lv rcv_invest) eth, loc)) in
    let true_b = Seq (stmt, true_b) in
    let false_b = Skip in
    let if_stmt = If (mk_and cond1 cond2, true_b, false_b) in
    if_stmt

  | Call (lvop,Lv (MemberAccess (e,"transfer",_,_)),args, _, _, loc, _)
    when is_address (get_type_exp e) ->
    let _ = assert (no_eth_gas_modifiers stmt) in
    let _ = assert (List.length args = 1) in
    let eth = List.hd args in
    let balance_info = dummy_vinfo_with_typ_org (EType (UInt 256)) "balance" in
    let this_info = dummy_vinfo_with_typ_org (Contract !main_contract) "this" in
    let this = Cast (EType Address, Lv (Var ("this", this_info))) in
    let this_balance = MemberAccess (this,"balance", balance_info, EType (UInt 256)) in
    let rcv_balance = MemberAccess (e, "balance", balance_info, EType (UInt 256)) in

    let invest_map = Var ("@Invest", dummy_vinfo_with_typ_org (Mapping (Address, EType (UInt 256))) "@Invest") in
    let rcv_invest = IndexAccess (Lv invest_map, Some e, EType (UInt 256)) in

    let cond1 = mk_ge (Lv this_balance) eth in
    let cond2 = mk_ge (mk_add (Lv rcv_balance) eth) (Lv rcv_balance) in
    let true_b = Seq (Assign (this_balance, mk_sub (Lv this_balance) eth, loc), Assign (rcv_balance, mk_add (Lv rcv_balance) eth, loc)) in
    let true_b = Seq (true_b, Assign (rcv_invest, mk_sub (Lv rcv_invest) eth, loc)) in
    let true_b = Seq (stmt, true_b) in
    let false_b = Throw in
    let if_stmt = If (mk_and cond1 cond2, true_b, false_b) in
    if_stmt

  | Call _ -> stmt
  | Skip -> stmt
  | If (e,s1,s2) -> If (e, convert_call_s s1, convert_call_s s2)
  | While (e,s) -> While (e, convert_call_s s)
  | Break | Continue | Return _
  | Throw | Assume _ | Assert _ | Assembly _ -> stmt
  | PlaceHolder -> stmt

let convert_call_f f =
  let body' = convert_call_s (get_body f) in
  update_body body' f

let convert_call_c c =
  let funcs' = List.map convert_call_f (get_funcs c) in
  update_funcs funcs' c

let convert_call p = List.map convert_call_c p

let run : pgm -> pgm
= fun p ->
  let p = if !Options.mode = "exploit" then convert_call p else p in
  p
