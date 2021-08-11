open Query
open Lang
open Vlang
open Report
open Global
open Semantics

(* safety condition: @TU[rcv] \/ @Invested[rcv] >= eth to be sent *)

let collect_queries : vformula -> Path.t -> stmt -> query list
= fun vf path stmt ->
  match stmt with
  | Call (lvop,Lv (MemberAccess (e,fname,_,_)),args,_,_,loc,_)
    when is_address (get_type_exp e) && List.mem fname ["transfer";"send"] ->
    let _ = assert (no_eth_gas_modifiers stmt) in
    let _ = assert (List.length args = 1) in
    let stolen_eth = List.hd args in
    let rcv = convert_aexp e in
    let rcv_trust = VBinRel (VEq, Read (VVar trust_map, rcv, EType Bool), VCond VTrue) in
    (* let invalid_rcv = VBinRel (VEq, rcv, VInt BatBig_int.zero) in *)
    let rcv_invested =
      if !Options.mode = "exploit" then VBinRel (VGeq, Read (VVar invest_map, rcv, EType (UInt 256)), convert_aexp stolen_eth)
      else assert false in
    let zero_ether = VBinRel (VEq, convert_aexp stolen_eth, VInt BatBig_int.zero) in
    let sc = VOr (VOr (rcv_trust, rcv_invested), zero_ether) in
    let vc = Imply (vf, sc) in
    let rcv_src = to_string_exp ~report:true e in
    let stolen_eth_src = to_string_exp ~report:true stolen_eth in
    [{vc=vc; vc2=sc; kind=ETH_LEAK; loc=loc; org_q=Org_Stmt stmt; path=path; src_f=Path.get_fkey path;
      sc_src=""; attacker_src=rcv_src; eth_src=stolen_eth_src}]

  | Call (lvop, Lv (MemberAccess (e,"call",_,_)), args, Some eth, gasop, loc, id)
    when is_address (get_type_exp e) ->
    let stolen_eth = eth in
    let rcv = convert_aexp e in
    let rcv_trust = VBinRel (VEq, Read (VVar trust_map, rcv, EType Bool), VCond VTrue) in
    let rcv_invested =
      if !Options.mode = "exploit" then VBinRel (VGeq, Read (VVar invest_map, rcv, EType (UInt 256)), convert_aexp stolen_eth)
      else assert false in
    let zero_ether = VBinRel (VEq, convert_aexp stolen_eth, VInt BatBig_int.zero) in
    let sc = VOr (VOr (rcv_trust, rcv_invested), zero_ether) in
    let vc = Imply (vf, sc) in
    let rcv_src = to_string_exp ~report:true e in
    let stolen_eth_src = to_string_exp ~report:true stolen_eth in
    [{vc=vc; vc2=sc; kind=ETH_LEAK; loc=loc; org_q=Org_Stmt stmt; path=path; src_f=Path.get_fkey path;
      sc_src=""; attacker_src=rcv_src; eth_src=stolen_eth_src}]

  | Call (lvop,Lv (Var (fname,_)),args,_,_,loc,_)
    when List.mem fname ["selfdestruct";"suicide"] ->
    let _ = assert (List.length args = 1) in
    let _ = assert (is_address (get_type_exp (List.hd args))) in
    let _ = assert (no_eth_gas_modifiers stmt) in
    let rcv_exp = List.hd args in
    let rcv = convert_aexp rcv_exp in
    let rcv_trust = VBinRel (VEq, Read (VVar trust_map, rcv, EType Bool), VCond VTrue) in
    let rcv_invested = VBinRel (VGeq, Read (VVar invest_map, rcv, EType (UInt 256)), Read (VVar eth_map, VVar this_addr, EType (UInt 256))) in
    let zero_ether = VBinRel (VEq, Read (VVar eth_map, VVar this_addr, EType (UInt 256)), VInt BatBig_int.zero) in
    let sc = VOr (VOr (rcv_trust, rcv_invested), zero_ether) in
    let vc = Imply (vf, sc) in
    let rcv_src = to_string_exp ~report:true rcv_exp in
    [{vc=vc; vc2=sc; kind=ETH_LEAK; loc=loc; org_q=Org_Stmt stmt; path=path; src_f=Path.get_fkey path;
      sc_src=""; attacker_src=rcv_src; eth_src="address(this).balance"}]
  | _ -> []
