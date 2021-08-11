open Query
open Lang
open Vlang
open Report
open Global
open Semantics

let collect_queries : vformula -> Path.t -> stmt -> query list
= fun vf path stmt ->
  match stmt with
  | Call (lvop,Lv (Var (fname,_)),args,_,_,loc,_)
    when List.mem fname ["selfdestruct";"suicide"] ->
    let _ = assert (no_eth_gas_modifiers stmt) in
    let sc = VBinRel (VEq, Read (VVar trust_map, VVar ("msg.sender", EType Address), EType Bool), VCond VTrue) in
    let vc = Imply (vf,sc) in
    [{vc=vc; vc2=sc; kind=KILL; loc=loc; org_q=Org_Stmt stmt; path=path; src_f=Path.get_fkey path;
      sc_src=""; attacker_src=""; eth_src=""}]
  | _ -> []
