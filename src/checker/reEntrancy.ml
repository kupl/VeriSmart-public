open Query
open Vlang
open Lang
open Semantics
open Global

let collect_queries ?(extern_ctx=false) : Global.t -> vformula -> Path.t -> cfg -> Node.t -> query list
= fun global vf path g node ->
  let stmt = find_stmt node g in
  (* let mid = Path.get_mid (snd path) in *)
  let fkey = Path.get_fkey path in
  let f = FuncMap.find fkey global.fmap in
  let defset = FuncDefUse.find_def_set fkey global.f_defuse in
  let fields = Global.get_all_fields global in
  let field_names = List.map fst fields in
  let g_defs = BatSet.filter (fun d -> List.mem d (List.map fst global.gvars) || d = "@Invest_sum" || List.mem d field_names) defset in
  (* let b0 = (is_public_func f || is_external_func f) && BatList.last mid = node in *) (* check at the end of basic paths only, for efficiency (vs. all assignments) *)
  let b1 = extern_ctx in
  let b2 = not (BatSet.is_empty g_defs) || (not (is_modifier f) && not (is_view_pure_f f)) in
  let b3 = !PatternAnalysis.may_violate_cei || !Options.re_safety_enforce in
  let b4 = MakeCfg.is_internal_call_node global.fmap global.cnames (BatList.last (snd path)) g in
  let re_state_check_cond = (* b0 && *) b1 && b2 && b3 && not b4 in

  match stmt with
  | Throw -> []
  | Return (_,loc) when loc.line < 0 -> []
  | _ when re_state_check_cond && PatternAnalysis.is_state_manipulating_assign global stmt ->
    let sc = VBinRel (VEq, Read (VVar trust_map, VVar msg_sender), VCond VTrue) in
    let vc = Imply (vf, sc) in
    let f = FuncMap.find fkey global.fmap in
    let line = (get_finfo f).floc.line in
    if (fun (a,b,c) -> a) fkey = !Options.main_contract then
      [{vc=vc; vc2=sc; kind=RE; qloc = line; org_q= Org_Func fkey; path=path; src_f=fkey; sc_src=""; attacker_src=""; eth_src = ""}]
    else []

  | Call (lvop, Lv (MemberAccess (e,"call",_,_)), args, Some eth, gasop, loc, id)
    when is_address (get_type_exp e) ->
    (* let _ = assert (!Options.mode = "verify") in *)
    let stolen_eth = eth in
    let rcv = convert_aexp e in
    let rcv_trust = VBinRel (VEq, Read (VVar trust_map, rcv), VCond VTrue) in
    let rcv_invested = VBinRel (VGeq, VVar invest_sum, convert_aexp stolen_eth) in
    let zero_ether = VBinRel (VEq, convert_aexp stolen_eth, VInt BatBig_int.zero) in
    let sc = VOr (VOr (rcv_trust, rcv_invested), zero_ether) in
    let vc = Imply (vf, sc) in
    let rcv_src = to_string_exp ~report:true e in
    let stolen_eth_src = to_string_exp ~report:true stolen_eth in
    [{vc=vc; vc2=sc; kind=RE_EL; qloc=loc.line; org_q=Org_Stmt stmt; path=path; src_f=fkey;
      sc_src=""; attacker_src=rcv_src; eth_src=stolen_eth_src}]

  | Call (lvop,Lv (MemberAccess (e,fname,_,_)),args,_,_,loc,_)
    when is_address (get_type_exp e) && List.mem fname ["transfer";"send"] && b1 ->
    let _ = assert (no_eth_gas_modifiers stmt) in
    let _ = assert (List.length args = 1) in
    let stolen_eth = List.hd args in
    let stolen_eth' =
      match stolen_eth with
      | BinOp (Mul, Lv v1, Lv (Var (v,_)), _) when BatString.starts_with v "sellPrice" -> Lv v1
      | _ -> stolen_eth in
    let rcv = convert_aexp e in
    let rcv_trust = VBinRel (VEq, Read (VVar trust_map, rcv), VCond VTrue) in
    (* let invalid_rcv = VBinRel (VEq, rcv, VInt BatBig_int.zero) in *)
    let rcv_invested =
      if !Options.mode = "exploit" then VBinRel (VGeq, Read (VVar invest_map, rcv), convert_aexp stolen_eth)
      else if !Options.mode = "verify" then VBinRel (VGeq, VVar invest_sum, convert_aexp stolen_eth')
      else assert false in
    let zero_ether = VBinRel (VEq, convert_aexp stolen_eth, VInt BatBig_int.zero) in
    let sc = VOr (VOr (rcv_trust, rcv_invested), zero_ether) in
    let vc = Imply (vf, sc) in
    let rcv_src = to_string_exp ~report:true e in
    let stolen_eth_src = to_string_exp ~report:true stolen_eth in
    [{vc=vc; vc2=sc; kind=RE_EL; qloc=loc.line; org_q=Org_Stmt stmt; path=path; src_f=Path.get_fkey path;
      sc_src=""; attacker_src=rcv_src; eth_src=stolen_eth_src}]

  | _ -> []
