open Lang
open Vocab
open Vlang
open Semantics

type t = comps
and comps = {
  mapvars : var BatSet.t;
  composites : ExpSet.t;
  ivars : var BatSet.t;
  avars : var BatSet.t;
  ints : BigIntSet.t
}

let rec ex_e : exp -> ExpSet.t
= fun exp ->
  match exp with
  | Int _ | Real _ | Str _ -> ExpSet.empty
  | Lv lv ->
    if List.mem (to_string_lv lv) keyword_vars then ExpSet.empty
    else ex_lv lv
  | Cast (_,e) -> ex_e e
  | BinOp (_,e1,e2,_) -> ExpSet.union (ex_e e1) (ex_e e2)
  | UnOp (_,e,_) -> ex_e e
  | True | False -> ExpSet.empty
  | ETypeName _ -> ExpSet.empty
  | _ -> failwith "ex_e : temp expressions encountered"

and ex_lv : lv -> ExpSet.t
= fun lv ->
  match lv with
  | Var (x,xinfo) -> ExpSet.singleton (VVar (x,xinfo.vtype))
  | MemberAccess (e,x,xinfo,_) -> ExpSet.add (VVar (x,xinfo.vtype)) (ex_e e)
  | IndexAccess (e1,Some e2,_) ->
    let y1 = Read (convert_aexp e1, convert_aexp e2, get_type_lv lv) in
    let y2 = ExpSet.union (ex_e e1) (ex_e e2) in
    ExpSet.add y1 y2
  | IndexAccess (e,None,_) -> ex_e e
  | Tuple (eops,_) ->
    List.fold_left (fun acc eop ->
      match eop with
      | None -> acc
      | Some e -> ExpSet.union (ex_e e) acc
    ) ExpSet.empty eops
 
let rec ex_s : Node.t -> cfg -> ExpSet.t * BigIntSet.t
= fun node g ->
  let stmt = find_stmt node g in
  match stmt with
  | Assign (lv,e,_) ->
    let (y1,n1) = (ex_lv lv, int_lv lv) in
    let (y2,n2) = (ex_e e, int_exp e) in
    (ExpSet.union y1 y2, BigIntSet.union n1 n2)
  | Decl lv -> (ex_lv lv, int_lv lv)
  | Call (None,e,elst,_,_) ->
    let (y1,n1) = (ex_e e, int_exp e) in
    let (y2,n2) =
      List.fold_left (fun (acc1,acc2) e' ->
        let (y',n') = (ex_e e', int_exp e') in
        (ExpSet.union y' acc1, BigIntSet.union n' acc2)
      ) (ExpSet.empty, BigIntSet.empty) elst
    in
    (ExpSet.union y1 y2, BigIntSet.union n1 n2)
  | Call (Some lv,e,elst,_,_) ->
    let (y0,n0) = (ex_lv lv, int_lv lv) in
    let (y1,n1) = (ex_e e, int_exp e) in
    let (y2,n2) =
      List.fold_left (fun (acc1,acc2) e' ->
        let (y',n') = (ex_e e', int_exp e') in
        (ExpSet.union y' acc1, BigIntSet.union n' acc2)
      ) (ExpSet.empty, BigIntSet.empty) elst
    in
    (ExpSet.union y0 (ExpSet.union y1 y2), BigIntSet.union n0 (BigIntSet.union n1 n2))
  | Skip -> (ExpSet.empty, BigIntSet.empty)
  | Assume (e,_) -> (ex_e e, int_exp e)
  | Assert (e,_) -> (ex_e e, int_exp e)
  | Return (None,_) -> (ExpSet.empty, BigIntSet.empty)
  | Return (Some e,_) -> (ex_e e, int_exp e)
  | Throw -> (ExpSet.empty, BigIntSet.empty)
  | Assembly _ -> (ExpSet.empty, BigIntSet.empty)
  | Seq _ | If _ | While _
  | Break | Continue -> raise (Failure "ex_s")

let ex_f : func -> ExpSet.t * BigIntSet.t
= fun f ->
  let cfg = get_cfg f in
  let nodes = MakeCfg.nodesof cfg in
  List.fold_left (fun (acc1,acc2) node ->
    let (y,n) = ex_s node cfg in
    (ExpSet.union y acc1, BigIntSet.union n acc2)
  ) (ExpSet.empty, BigIntSet.empty) nodes

let mk_comps : ExpSet.t -> BigIntSet.t -> comps
= fun expset intset ->
  let ivars =
    ExpSet.fold (fun ve acc ->
      match ve with
      | VVar (x,t) when is_uintkind t || is_sintkind t ->
        BatSet.add (x,t) acc
      | _ -> acc
    ) expset BatSet.empty
  in
  let avars =
    ExpSet.fold (fun ve acc ->
      match ve with
      | VVar (x,t) when is_address t ->
        BatSet.add (x,t) acc
      | _ -> acc
    ) expset BatSet.empty
  in
  let mapvars =
    ExpSet.fold (fun ve acc ->
      match ve with
      | VVar (x,t) when is_usual_mapping t ->
        BatSet.add (x,t) acc
      | _ -> acc
    ) expset BatSet.empty
  in
  let reads =
    ExpSet.filter (fun ve ->
      match ve with
      | Read (VVar (x,t), VVar _, _) when not (is_usual_mapping t) -> true
      | _ -> false
    ) expset
  in
  {mapvars=mapvars; composites=reads; ivars=ivars; avars=avars; ints=intset}

let collect_comps_f : func -> comps
= fun f ->
  let (expset, intset) = ex_f f in
  mk_comps expset intset

let collect_comps_bp : Node.t list -> cfg -> comps
= fun nodes cfg ->
  let (expset,intset) =
    List.fold_left (fun (acc1,acc2) node ->
      let (y,n) = ex_s node cfg in
      (ExpSet.union y acc1, BigIntSet.union n acc2)
    ) (ExpSet.empty, BigIntSet.empty) nodes
  in
  mk_comps expset intset

let to_string : comps -> string
= fun comp ->
  "map vars   : " ^ string_of_list ~first:"{" ~last:"}" ~sep:", " (fst|>id) (BatSet.to_list comp.mapvars) ^ "\n" ^
  "composites : " ^ string_of_list ~first:"{" ~last:"}" ~sep:", " to_string_vexp (ExpSet.to_list comp.composites) ^ "\n" ^
  "int vars   : " ^ string_of_list ~first:"{" ~last:"}" ~sep:", " (fst|>id) (BatSet.to_list comp.ivars) ^ "\n" ^
  "addr vars  : " ^ string_of_list ~first:"{" ~last:"}" ~sep:", " (fst|>id) (BatSet.to_list comp.avars) ^ "\n" ^
  "integers   : " ^ string_of_list ~first:"{" ~last:"}" ~sep:", " BatBig_int.to_string (BigIntSet.to_list comp.ints)
