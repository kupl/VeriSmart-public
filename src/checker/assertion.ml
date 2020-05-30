open Query
open Vlang
open Lang
open Options
open Semantics
open Z3Interface

let collect_queries : Global.t -> vformula -> Path.t -> stmt -> query list
= fun global vf path stmt ->
  match stmt with
  | Assert (e,loc) ->
    let sc = convert_bexp e in
    let vc = Imply (vf, sc) in
    let sc_src = to_string_exp ~report:true e in
    let kind = ASSERT in
    [{vc=vc; vc2=sc; kind=kind; loc=loc; org_q=Org_Exp e; path=path; src_f=Path.get_fkey path; sc_src=sc_src}]
  | _ -> []
