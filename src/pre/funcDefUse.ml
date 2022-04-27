open Lang
open Vocab
open FuncMap
open MakeCfg

type t = (fkey, value) BatMap.t
and du_map = t
and value = def_set * use_set * use_set_assume 
and def_set = id BatSet.t
and use_set = id BatSet.t
and use_set_assume = id BatSet.t

let mem = BatMap.mem
let empty = BatMap.empty
let bindings = BatMap.bindings
let find x m =
  try BatMap.find x m 
  with Not_found -> (BatSet.empty,BatSet.empty,BatSet.empty) (* for built-in functions *)

let find_def_set x m = triple_fst (find x m)
let find_use_set x m = triple_snd (find x m)
let find_use_set_assume x m = triple_third (find x m)

let add_def x defs m =
  BatMap.add x (BatSet.union defs (find_def_set x m), find_use_set x m, find_use_set_assume x m) m

let add_use x uses m =
  BatMap.add x
    (find_def_set x m, BatSet.union uses (find_use_set x m), find_use_set_assume x m) m

let add_use_assume x uses m =
  BatMap.add x
    (find_def_set x m, find_use_set x m, BatSet.union uses (find_use_set_assume x m)) m

let to_string : t -> string
= fun map ->
  let to_string_x (cid,fid,typs) = cid ^ "," ^ fid ^ "," ^ string_of_list ~first:"(" ~last:")" ~sep:"," to_string_typ typs in
  let to_string_y y = string_of_set ~first:"{" ~last:"}" ~sep:", " id y in
  "{" ^ "\n" ^
  BatMap.foldi (fun x (d,u,a) acc -> 
    acc ^ to_string_x x ^ " ->\n" ^
    "  " ^ "DEF: " ^ to_string_y d ^ "\n" ^
    "  " ^ "USE: " ^ to_string_y u ^ "\n" ^
    "  " ^ "USE_ASSUME: " ^ to_string_y a ^ "\n" 
  ) map ""
  ^ "}"

let eq m1 m2 = BatString.equal (to_string m1) (to_string m2)

let rec get_def_set_lv : lv -> id BatSet.t
= fun lv ->
  match lv with
  | Var (id,vinfo) -> BatSet.singleton id
  | MemberAccess (e,"length",info,_) -> BatSet.singleton "@L"
  | MemberAccess (e,"balance",info,_) ->
    let _ = assert (info.vtyp = EType (UInt 256)) in
    let _ = assert (is_address (get_type_exp e)) in
    BatSet.singleton "@B"
  | MemberAccess (e,x,xinfo,_) -> BatSet.singleton x
  (* | MemberAccess (Lv lv,x,xinfo,_) -> get_def_set_lv lv *)
  | IndexAccess (Lv lv,_,_) -> get_def_set_lv lv
  | IndexAccess (Cast (_, Lv lv),_,_) -> get_def_set_lv lv
  | Tuple (eops,_) ->
    List.fold_left (fun acc eop ->
      match eop with
      | Some (Lv lv) -> BatSet.union (get_def_set_lv lv) acc
      | None -> acc
      | _ -> failwith "get_defs_lv"
    ) BatSet.empty eops
  | _ -> failwith "get_defs_lv"

let get_def_set_lvop lvop =
  match lvop with
  | None -> BatSet.empty
  | Some lv -> get_def_set_lv lv

let get_use_set_exp exp = BatSet.map fst (var_exp exp)

let get_use_set_exps exps =
  List.fold_left (fun acc e ->
    let uses = get_use_set_exp e in
    BatSet.union uses acc
  ) BatSet.empty exps

type alias_map = (id, id BatSet.t) BatMap.t

let find_alias x m = try BatMap.find x m with Not_found -> BatSet.empty

let handle_built_in_funcs (lvop,f,args) =
  match lvop with
  | None ->
    (match f with
     | "revert" -> (BatSet.empty, BatSet.empty)
     | "selfdestruct" -> (BatSet.empty, get_use_set_exps args)
     | "suicide" -> (BatSet.empty, get_use_set_exps args)
     | "delete" ->
        let _ = assert (List.length args = 1) in
        let exp = List.hd args in
        let defs = match exp with Lv lv -> get_def_set_lv lv | _ -> assert false in
        (defs, BatSet.diff (get_use_set_exp exp) defs)
     | _ -> failwith ("handle_built_in_funcs: " ^ f))
  | Some lv -> (* lv is in 'Var' pattern *)
    (match f with
     | "keccak256" | "sha3" | "sha256" | "ripemd160"
     | "ecrecover" | "addmod" | "blockhash" ->
        (get_def_set_lv lv, get_use_set_exps args)
     | _ -> failwith ("handle_built_in_funcs: " ^ f))

let handle_undefs fmap (lvop,exp,args) loc =
  match exp with
  | Lv (Var (f,_)) when List.mem f built_in_funcs ->
    handle_built_in_funcs (lvop,f,args)
  | _ -> (get_def_set_lvop lvop, get_use_set_exps args)

let update_du_n : id list -> FuncMap.t -> cfg -> fkey -> Node.t ->
                  t * alias_map -> t * alias_map
= fun cnames fmap g fkey n (du_map, alias_map) ->
  let (cname,_,_) = g.signature in
  let stmt = find_stmt n g in
  match stmt with
  | Assign (lv,Lv e,_) when is_struct (get_type_lv lv) ->
    let defs, aliases = get_def_set_lv lv, get_def_set_lv e in
    let uses =
      let lv_use = BatSet.diff (BatSet.map fst (var_lv lv)) (get_def_set_lv lv) in
      BatSet.union lv_use (BatSet.map fst (var_exp (Lv e))) in
    let du_map = add_def fkey defs du_map in
    let du_map = add_use fkey uses du_map in
    let alias_map = BatSet.fold (fun d acc -> BatMap.add d (BatSet.union aliases (find_alias d acc)) acc) defs alias_map in
    (du_map, alias_map)
  | Assign (lv,_,_) when is_struct (get_type_lv lv) -> assert false
  | Assign (lv,e,_) ->
    let defs = get_def_set_lv lv in
    let defs = BatSet.fold (fun d acc -> BatSet.union (find_alias d alias_map) acc) defs defs in
    let uses =
      let lv_use = BatSet.diff (BatSet.map fst (var_lv lv)) (get_def_set_lv lv) in
      BatSet.union lv_use (BatSet.map fst (var_exp e)) in
    let du_map = add_def fkey defs du_map in
    let du_map = add_use fkey uses du_map in
    (du_map, alias_map)
  | Decl lv -> (add_def fkey (get_def_set_lv lv) du_map, alias_map)
  | Call (lvop,e,args,_,_,loc,_) when is_undef_call fmap stmt ->
    let (defs,uses) = handle_undefs fmap (lvop,e,args) loc in
    let du_map = add_def fkey defs du_map in
    let du_map = add_use fkey uses du_map in
    (du_map, alias_map)

  | Call _ when is_external_call stmt ->
    (* the anlysis here aims to identify def-use by direct usage in code *)
    (du_map, alias_map)

  | Call (lvop,e,args,_,_,loc,_) -> (* normal calls *)
    (* Find def set *)
    let init_defs = match lvop with Some lv -> get_def_set_lv lv | None -> BatSet.empty in
    let callees = FuncMap.find_matching_funcs cname e (List.map get_type_exp args) cnames fmap in
    let defs =
      BatSet.fold (fun callee acc ->
        BatSet.union (find_def_set (get_fkey callee) du_map) acc
      ) callees init_defs in
    (* Find use set *)
    let init_uses1 =
      (match lvop with
       | Some lv ->
         let all = BatSet.map fst (var_lv lv) in
         BatSet.diff all (get_def_set_lv lv)
       | None -> BatSet.empty) in
    let init_uses2 =
      List.fold_left (fun acc e ->
        let use_ids = BatSet.map fst (var_exp e) in
        BatSet.union use_ids acc
      ) BatSet.empty args in
    let init_uses = BatSet.union init_uses1 init_uses2 in
    let uses =
      BatSet.fold (fun callee acc ->
        BatSet.union (find_use_set (get_fkey callee) du_map) acc
      ) callees init_uses in
    (* Find use_assume set *)
    let uses_assume =
      BatSet.fold (fun callee acc ->
        BatSet.union (find_use_set_assume (get_fkey callee) du_map) acc
      ) callees BatSet.empty in
    (du_map |> add_def fkey defs |> add_use fkey uses |> add_use_assume fkey uses_assume,
     alias_map)
  | Assembly (lst,_) ->
    let defs = BatSet.map fst (BatSet.of_list lst) in (* conservative result *)
    let uses = defs in
    (du_map |> add_def fkey defs |> add_use fkey uses, alias_map)
  | Skip -> (du_map, alias_map)
  | Return (None,_) -> (du_map, alias_map)
  | Return (Some e,_) ->
    let uses = BatSet.map fst (var_exp e) in
    (add_use fkey uses du_map, alias_map)
  | Throw -> (du_map, alias_map)
  | Assume (e,_) ->
    let uses = BatSet.map fst (var_exp e) in
    (du_map |> add_use fkey uses |> add_use_assume fkey uses,
     alias_map)
  | Assert (e,_,_) ->
    let uses = BatSet.map fst (var_exp e) in
    (add_use fkey uses du_map, alias_map)
  | PlaceHolder -> (du_map, alias_map) (* this case is encountered for the modifier case *)
  | If _ | Seq _ | While _ | Break | Continue | Unchecked _ -> failwith "update_du_n"

let onestep : id list -> FuncMap.t -> fkey -> t * alias_map -> t * alias_map
= fun cnames fmap fkey (du_map, alias_map) ->
  let f = FuncMap.find fkey fmap in
  let g = get_cfg f in
  let nodes = nodes_of g in
  List.fold_left (fun (acc_du_map, acc_alias_map) n ->
    update_du_n cnames fmap g fkey n (acc_du_map, acc_alias_map)
  ) (du_map, alias_map) nodes

let onestep_f : id list -> FuncMap.t -> fkey BatSet.t -> (t * alias_map) -> (t * alias_map)
= fun cnames fmap fkeys (du_map, alias_map) ->
  BatSet.fold (fun fkey (acc_du_map, acc_alias_map) ->
    onestep cnames fmap fkey (acc_du_map, acc_alias_map)
  ) fkeys (du_map,alias_map)

let rec fix_fsum : id list -> FuncMap.t -> fkey BatSet.t -> (t * alias_map) -> t
= fun cnames fmap fkeys (du_map,alias_map) ->
  let du_map', alias_map' = onestep_f cnames fmap fkeys (du_map,alias_map) in
  if eq du_map' du_map then du_map'
  else fix_fsum cnames fmap fkeys (du_map',alias_map')

let compute : id list-> FuncMap.t -> t
= fun cnames fmap ->
  let lst = BatMap.bindings fmap in
  let fkeys = List.map fst lst |> BatSet.of_list in
  let res = fix_fsum cnames fmap fkeys (empty, BatMap.empty) in
  (* let _ = print_endline (to_string res) in
  let _ = assert false in *)
  res
