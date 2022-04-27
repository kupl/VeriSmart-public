open Global
open Lang
open Vocab
open Vlang
open Semantics

type t = comps

and comps = {
  mapvars : var BatSet.t;
  mapmems : (var * var) BatSet.t;
  reads   : ExpSet.t;
  ivars   : var BatSet.t;
  avars   : var BatSet.t;
  a_arrs  : var BatSet.t;
  a_maps  : var BatSet.t;
  bvars   : var BatSet.t;
  ints    : BigIntSet.t
}

let empty_comps = {
  mapvars = BatSet.empty;
  mapmems = BatSet.empty;
  reads = ExpSet.empty;
  ivars = BatSet.empty;
  avars = BatSet.empty;
  a_arrs = BatSet.empty;
  a_maps = BatSet.empty;
  bvars = BatSet.empty;
  ints = BigIntSet.empty;
}

let subset : t -> t -> bool
= fun comps1 comps2 ->
  BatSet.subset comps1.mapvars comps2.mapvars
  && BatSet.subset comps1.mapmems comps2.mapmems
  && ExpSet.subset comps1.reads comps2.reads
  && BatSet.subset comps1.ivars comps2.ivars
  && BatSet.subset comps1.avars comps2.avars
  && BatSet.subset comps1.a_arrs comps2.a_arrs
  && BatSet.subset comps1.a_maps comps2.a_maps
  && BatSet.subset comps1.bvars comps2.bvars
  && BigIntSet.subset comps1.ints comps2.ints

let union : t -> t -> t
= fun comps1 comps2 ->
  {mapvars = BatSet.union comps1.mapvars comps2.mapvars;
   mapmems = BatSet.union comps1.mapmems comps2.mapmems;
   reads = ExpSet.union comps1.reads comps2.reads;
   ivars = BatSet.union comps1.ivars comps2.ivars;
   avars = BatSet.union comps1.avars comps2.avars;
   a_arrs = BatSet.union comps1.a_arrs comps2.a_arrs;
   a_maps = BatSet.union comps1.a_maps comps2.a_maps;
   bvars = BatSet.union comps1.bvars comps2.bvars;
   ints = BigIntSet.union comps1.ints comps2.ints
  }

let to_string : comps -> string
= fun comp ->
  "map vars     : " ^ string_of_list ~first:"{" ~last:"}" ~sep:", " (fst|>id) (BatSet.to_list comp.mapvars) ^ "\n" ^
  "smap mems    : " ^ string_of_list ~first:"{" ~last:"}" ~sep:", " (fun (x,y) -> fst x ^ "[i]." ^ fst y) (BatSet.to_list comp.mapmems) ^ "\n" ^
  "reads        : " ^ string_of_list ~first:"{" ~last:"}" ~sep:", " to_string_vexp (ExpSet.to_list comp.reads) ^ "\n" ^
  "int vars     : " ^ string_of_list ~first:"{" ~last:"}" ~sep:", " (fst|>id) (BatSet.to_list comp.ivars) ^ "\n" ^
  "addr vars    : " ^ string_of_list ~first:"{" ~last:"}" ~sep:", " (fst|>id) (BatSet.to_list comp.avars) ^ "\n" ^
  "addr arrays  : " ^ string_of_list ~first:"{" ~last:"}" ~sep:", " (fst|>id) (BatSet.to_list comp.a_arrs) ^ "\n" ^
  "addr maps    : " ^ string_of_list ~first:"{" ~last:"}" ~sep:", " (fst|>id) (BatSet.to_list comp.a_maps) ^ "\n" ^
  "boolean vars : " ^ string_of_list ~first:"{" ~last:"}" ~sep:", " (fst|>id) (BatSet.to_list comp.bvars) ^ "\n" ^
  "integers     : " ^ string_of_list ~first:"{" ~last:"}" ~sep:", " BatBig_int.to_string (BigIntSet.to_list comp.ints)

let is_addr_one_dim_array_typ : typ -> bool
= fun typ ->
  match typ with
  | Array (EType Address, _) -> true
  | _ -> false

let is_addr_mapping_typ : typ -> bool
= fun typ ->
  match typ with
  | Mapping (Address, EType Address) -> true
  | _ -> false

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
  | Var (x,xinfo)
    when BatString.starts_with x "@" || BatString.starts_with x "Tmp"
         || BatString.starts_with x "Param" || BatString.exists x "__inline"
    -> comps
  | Var (x,xinfo) ->
    let t = xinfo.vtyp in
    { comps with mapvars = if is_usual_mapping t then BatSet.add (x,t) comps.mapvars
                           else comps.mapvars;
                 ivars = if (is_uintkind t || is_sintkind t) then BatSet.add (x,t) comps.ivars
                         else comps.ivars;
                 avars = if is_address t && not (is_constant_address global (x,t)) then BatSet.add (x,t) comps.avars else comps.avars;
                 a_arrs = if is_addr_one_dim_array_typ t then BatSet.add (x,t) comps.a_arrs else comps.a_arrs;
                 a_maps = if is_addr_mapping_typ t then BatSet.add (x,t) comps.a_maps else comps.a_maps;
                 bvars = if is_bool t && List.mem (x,t) global.gvars then BatSet.add (x,t) comps.bvars else comps.bvars;
    }

  | MemberAccess (e,x,xinfo,_)
    when is_struct (get_type_exp e) && is_uint256 xinfo.vtyp
         && not (BatSet.exists (fun y -> BatString.starts_with (fst y) "@") (var_exp e))
         && not (BatString.starts_with x "@")
    ->
    let pred = (fun g -> snd g = Mapping (Address, get_type_exp e)) in
    let lst = List.filter pred global.gvars in
    List.fold_left (fun acc g ->
      {acc with mapmems = BatSet.add (g, (x,Mapping2 (get_type_exp e, xinfo.vtyp))) acc.mapmems}
    ) (collect_e global e comps) lst

  | MemberAccess (e,x,xinfo,_) -> collect_e global e comps
  | IndexAccess (e1,Some e2,_) ->
    let read = Read (convert_aexp e1, convert_aexp e2) in
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
  | Break | Continue | PlaceHolder | Unchecked _ -> failwith ("collect_s: " ^ to_string_stmt stmt)

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
