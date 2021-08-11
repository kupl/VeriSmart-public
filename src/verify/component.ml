open Lang
open Vocab
open Vlang
open Semantics

type t = comps

and comps = {
  mapvars : var BatSet.t;
  reads   : ExpSet.t;
  ivars   : var BatSet.t;
  avars   : var BatSet.t;
  ints    : BigIntSet.t
}

let empty_comps = {
  mapvars = BatSet.empty;
  reads = ExpSet.empty;
  ivars = BatSet.empty;
  avars = BatSet.empty;
  ints = BigIntSet.empty;
} 

let to_string : comps -> string
= fun comp ->
  "map vars     : " ^ string_of_list ~first:"{" ~last:"}" ~sep:", " (fst|>id) (BatSet.to_list comp.mapvars) ^ "\n" ^
  "reads        : " ^ string_of_list ~first:"{" ~last:"}" ~sep:", " to_string_vexp (ExpSet.to_list comp.reads) ^ "\n" ^
  "int vars     : " ^ string_of_list ~first:"{" ~last:"}" ~sep:", " (fst|>id) (BatSet.to_list comp.ivars) ^ "\n" ^
  "addr vars    : " ^ string_of_list ~first:"{" ~last:"}" ~sep:", " (fst|>id) (BatSet.to_list comp.avars) ^ "\n" ^
  "integers     : " ^ string_of_list ~first:"{" ~last:"}" ~sep:", " BatBig_int.to_string (BigIntSet.to_list comp.ints)


let rec collect_e : Global.t -> exp -> comps -> comps
= fun global exp comps ->
  match exp with
  | Int n -> {comps with ints = BigIntSet.add n comps.ints}
  | Real _ | Str _ -> comps
  | Lv lv ->
    if List.mem (to_string_lv lv) keyword_vars then comps
    else collect_lv global lv comps
  | Cast (EType Address, Int _) -> comps
  | Cast (_,e) -> collect_e global e comps
  | BinOp (_,e1,e2,_) -> collect_e global e2 (collect_e global e1 comps)
  | UnOp (_,e,_) -> collect_e global e comps
  | True | False | ETypeName _ -> comps
  | _ -> failwith "collect_e : temp expressions encountered"

and collect_lv : Global.t -> lv -> comps -> comps
= fun global lv comps ->
  match lv with
  | Var (x,xinfo) ->
    let t = xinfo.vtype in
    { comps with mapvars = if is_usual_mapping t && not (BatString.starts_with x "@")
                             then BatSet.add (x,t) comps.mapvars
                           else comps.mapvars;
                 ivars = if (is_uintkind t || is_sintkind t) && not (BatString.starts_with x "@")
                           then BatSet.add (x,t) comps.ivars
                         else comps.ivars;
                 avars = if is_address t then BatSet.add (x,t) comps.avars else comps.avars;
    }
  | MemberAccess (e,x,xinfo,_) -> collect_e global e comps
  | IndexAccess (e1,Some e2,_) ->
    let read = Read (convert_aexp e1, convert_aexp e2, get_type_lv lv) in
    let vars = BatSet.union (var_exp e1) (var_exp e2) in
    (* e.g., exclude @Invest[...] *)
    let b = not (BatSet.exists (fun y -> BatString.starts_with (fst y) "@") vars) in
    let comps = {comps with reads = if b then ExpSet.add read comps.reads else comps.reads} in
    collect_e global e2 (collect_e global e1 comps)
  | IndexAccess (e,None,_) -> collect_e global e comps
  | Tuple (eops,_) ->
    List.fold_left (fun acc eop ->
      match eop with
      | None -> acc
      | Some e -> collect_e global e acc
    ) comps eops

let rec collect_s : Global.t -> Node.t -> cfg -> comps -> comps
= fun global node g comps ->
  let stmt = find_stmt node g in
  match stmt with
  | Assign (lv,e,_) -> collect_e global e (collect_lv global lv comps)
  | Decl lv -> collect_lv global lv comps
  | Call (lvop,e,elst,ethop,gasop,_,_) ->
    let comps = match lvop with None -> comps | Some lv -> collect_lv global lv comps in
    let comps = collect_e global e comps in
    List.fold_left (fun acc e' -> collect_e global e' acc) comps elst
  | Skip -> comps
  | Assume (e,_) -> collect_e global e comps
  | Assert (e,_,_) -> collect_e global e comps
  | Return (eop,_) -> (match eop with None -> comps | Some e -> collect_e global e comps)
  | Throw | Assembly _ -> comps
  | Seq _ | If _ | While _
  | Break | Continue | PlaceHolder -> failwith ("collect_s: " ^ to_string_stmt stmt)

let collect_f : Global.t -> func -> comps
= fun global f ->
  let cfg = get_cfg f in
  let nodes = MakeCfg.nodesof cfg in
  List.fold_left (fun acc node ->
    collect_s global node cfg acc
  ) empty_comps nodes

let collect_bp : Global.t -> Node.t list -> cfg -> comps
= fun global nodes cfg ->
  List.fold_left (fun acc node ->
    collect_s global node cfg acc
  ) empty_comps nodes
