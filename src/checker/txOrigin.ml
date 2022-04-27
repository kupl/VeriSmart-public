open Query
open Vlang
open Lang
open Semantics
open Global

let collect_queries : Global.t -> vformula -> Path.t -> cfg -> Node.t -> query list
= fun global vf path g node ->
  let func = FuncMap.find (Path.get_fkey path) global.fmap in
  let params = List.map (fun (v,vinfo) -> (v,vinfo.vtyp)) (get_params func) in
  let params = List.filter (fun (v,typ) -> is_address typ) params in
  let stmt = find_stmt node g in
  match stmt with
  | Assume (BinOp (bop,e1,e2,einfo), _)
    when einfo.eloc.line > 0 && is_address (get_type_exp e1) && is_address (get_type_exp e2) ->
    let _ = assert (bop = Eq || bop = NEq) in
    let line = einfo.eloc.line in
    let sc1 = VBinRel (VEq, convert_aexp e1, VVar msg_sender) in
    let sc2 = VBinRel (VEq, convert_aexp e2, VVar msg_sender) in
    let sc3 = VBinRel (VEq, convert_aexp e1, VCast (EType Address, VInt BatBig_int.zero)) in
    let sc4 = VBinRel (VEq, convert_aexp e2, VCast (EType Address, VInt BatBig_int.zero)) in
    let sc5 =
      List.fold_left (fun acc param ->
        let f' = VOr (VBinRel (VEq, convert_aexp e1, VVar param), VBinRel (VEq, convert_aexp e2, VVar param)) in
        if equal_vf acc VTrue then f'
        else VOr (acc, f')
      ) VTrue params in
    let sc = VOr (VOr (VOr (sc1, sc2), VOr (sc3,sc4)), sc5) in
    let vc = Imply (vf,sc) in
    [{vc=vc; vc2=sc; kind=TX_ORG; qloc=line; org_q=Org_Stmt stmt; path=path; src_f=Path.get_fkey path;
      sc_src=""; attacker_src=""; eth_src=""}]
  | _ -> []
