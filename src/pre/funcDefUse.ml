open Lang
open Vocab
open FuncMap 

type t = (fkey, value) BatMap.t
and value = def_set * use_set * use_set_assume 
and def_set = id BatSet.t
and use_set = id BatSet.t
and use_set_assume = id BatSet.t

let add = BatMap.add
let mem = BatMap.mem
let empty = BatMap.empty
let bindings = BatMap.bindings
let find x m = 
  try BatMap.find x m 
  with Not_found -> (BatSet.empty,BatSet.empty,BatSet.empty) (* for built-in functions *)

let find_def_set x m = triple_fst (find x m)
let find_use_set x m = triple_snd (find x m)
let find_use_set_assume x m = triple_third (find x m) 

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
  | Var (id,_) -> BatSet.singleton id 
  | MemberAccess (e,x,xinfo,_) -> BatSet.singleton (x) 
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

let get_def_set_n : id list -> FuncMap.t -> t -> Node.t -> cfg -> id BatSet.t
= fun cnames fmap fsum n g ->
  let (cname,_,_) = g.signature in
  let stmt = find_stmt n g in
  match stmt with
  | Assign (lv,_,_) -> get_def_set_lv lv
  | Decl lv -> get_def_set_lv lv
  | Call (lvop,e,args,loc,_) (* built-in functions *)
    when FuncMap.is_undef e (List.map get_type_exp args) fmap ->
    (match lvop with
     | Some lv -> get_def_set_lv lv
     | None -> BatSet.empty)
  | Call (lvop,e,args,loc,_) -> (* normal calls *)
    let init =
      (match lvop with
       | Some lv -> get_def_set_lv lv
       | None -> BatSet.empty)
    in
    let callees = FuncMap.find_matching_funcs cname e (List.map get_type_exp args) cnames fmap in
    BatSet.fold (fun callee acc ->
      BatSet.union (find_def_set (get_fkey callee) fsum) acc 
    ) callees init
  | Assembly (lst,_) -> BatSet.map fst (BatSet.of_list lst) (* conservative result *)
  | Skip | Return _ | Throw | Assume _ | Assert _ -> BatSet.empty
  | If _ | Seq _ | While _ | Break | Continue -> failwith "get_defs"

let get_use_set_n : id list -> FuncMap.t -> t -> Node.t -> cfg -> id BatSet.t 
= fun cnames fmap fsum n g ->
  let (cname,_,_) = g.signature in
  let stmt = find_stmt n g in
  let res =
  match stmt with
  | Assign (lv,e,_) ->
    let lv_use = BatSet.diff (BatSet.map fst (var_lv lv)) (get_def_set_lv lv) in
    BatSet.union lv_use (BatSet.map fst (var_exp e))
  | Decl lv -> BatSet.empty
  | Call (lvop,e,args,loc,_) (* built-in functions *)
    when FuncMap.is_undef e (List.map get_type_exp args) fmap ->
    List.fold_left (fun acc e ->
      let use_ids = BatSet.map fst (var_exp e) in
      BatSet.union use_ids acc
    ) BatSet.empty args
  | Call (lvop,e,args,loc,_) -> (* normal calls *)
    let init1 =
      (match lvop with
       | Some lv ->
         let all = BatSet.map fst (var_lv lv) in
         BatSet.diff all (get_def_set_lv lv)
       | None -> BatSet.empty)
    in
    let init2 =
      List.fold_left (fun acc e ->
        let use_ids = BatSet.map fst (var_exp e) in
        BatSet.union use_ids acc
      ) BatSet.empty args
    in
    let init = BatSet.union init1 init2 in 
    let callees = FuncMap.find_matching_funcs cname e (List.map get_type_exp args) cnames fmap in
    BatSet.fold (fun callee acc ->
      BatSet.union (find_use_set (get_fkey callee) fsum) acc
    ) callees init
  | Skip -> BatSet.empty
  | Return (eop,_) ->
    (match eop with
     | None -> BatSet.empty
     | Some e -> BatSet.map fst (var_exp e))
  | Throw -> BatSet.empty
  | Assume (e,_) -> BatSet.map fst (var_exp e)
  | Assert (e,_) -> BatSet.map fst (var_exp e)
  | Assembly (lst,_) -> BatSet.map fst (BatSet.of_list lst) (* conservative result *)
  | If _ | Seq _ | While _ | Break | Continue -> failwith "get_uses"
  in
  BatSet.filter (fun x -> not (List.mem x keyword_vars)) res

let get_use_set_n_assume : id list -> FuncMap.t -> t -> Node.t -> cfg -> id BatSet.t
= fun cnames fmap fsum n g ->
  let (cname,_,_) = g.signature in
  let stmt = find_stmt n g in
  let res =
  match stmt with
  | Call (lvop,e,args,loc,_) (* built-in functions *)
    when FuncMap.is_undef e (List.map get_type_exp args) fmap ->
    BatSet.empty
  | Call (lvop,e,args,loc,_) -> (* normal calls *)
    let callees = FuncMap.find_matching_funcs cname e (List.map get_type_exp args) cnames fmap in
    BatSet.fold (fun callee acc ->
      BatSet.union (find_use_set_assume (get_fkey callee) fsum) acc
    ) callees BatSet.empty
  | Assume (e,_) -> BatSet.map fst (var_exp e)
  | Assembly (lst,_) -> BatSet.map fst (BatSet.of_list lst) (* conservative result *)
  | _ -> BatSet.empty
  in
  BatSet.filter (fun x -> not (List.mem x keyword_vars)) res

let get_du_set_f : id list -> FuncMap.t -> t -> fkey ->
                 (def_set * use_set * use_set_assume) 
= fun cnames fmap fsum fkey ->
  let f = FuncMap.find fkey fmap in
  let g = get_cfg f in
  let nodes = nodes_of g in
  List.fold_left (fun (acc_d,acc_u,acc_a) n ->
    (BatSet.union (get_def_set_n cnames fmap fsum n g) acc_d,
     BatSet.union (get_use_set_n cnames fmap fsum n g) acc_u,
     BatSet.union (get_use_set_n_assume cnames fmap fsum n g) acc_a)
  ) (BatSet.empty,BatSet.empty,BatSet.empty) nodes

let onestep_fsum : id list -> FuncMap.t -> fkey BatSet.t -> t -> t 
= fun cnames fmap ks fsum ->
  BatSet.fold (fun k acc ->
    add k (get_du_set_f cnames fmap fsum k) acc 
  ) ks fsum

let rec fix_fsum : id list -> FuncMap.t -> fkey BatSet.t -> t -> t
= fun cnames fmap ks fsum ->
  let fsum' = onestep_fsum cnames fmap ks fsum in
    if eq fsum' fsum then fsum'
    else fix_fsum cnames fmap ks fsum'

let compute : id list-> FuncMap.t -> t
= fun cnames fmap ->
  let ks = FuncMap.dom fmap in 
  fix_fsum cnames fmap ks empty
