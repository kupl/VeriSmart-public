open Lang
open Vocab

let rec is_implicitly_convertible : typ -> typ -> bool 
= fun my_typ comp_typ ->
  if my_typ = comp_typ then true
  else
    (match my_typ, comp_typ with
     | ConstInt, EType (UInt n) -> true
     | EType (UInt n1), EType (UInt n2) -> n1<=n2 
     | ConstInt, EType (SInt n) -> true
     | EType (SInt n1), EType (SInt n2) -> n1<=n2
     | EType (SInt _), EType (UInt _) -> false (* negative numbers cannot be unsigned numbers *) 
     | ConstInt, EType Address -> true
     | ConstInt, EType String -> false
     | ConstInt, Array _ -> false
     | Contract _, EType Address ->
       (* true for 0.4x, false for 0.5x *)
       if BatString.starts_with !Options.solc_ver "0.4" then true
       else if BatString.starts_with !Options.solc_ver "0.5" then false
       else failwith "is_implicitly_convertible"
     | Contract _, EType (Bytes _) -> false
     | Contract _, EType DBytes -> false
     | ConstString, EType (Bytes _) -> true
     | ConstString, EType DBytes -> true
     | ConstString, EType String -> true
     | ConstString, Array (EType String, _) -> false
     | ConstString, Array (EType DBytes, _) -> false
     | ConstString, EType (UInt _) -> false
     | ConstString, Contract _ -> false
     | EType String, EType DBytes -> false
     | EType String, EType (Bytes _) -> false
     | EType String, Struct _ -> false
     | Struct _, EType String -> false
     | EType DBytes, EType String -> false
     | EType (Bytes n1), EType (Bytes n2) -> n1<=n2
     | EType (Bytes _), EType String -> false
     | EType (Bytes _), EType DBytes -> false
     | EType (Bytes _), Contract _ -> false
     | EType DBytes, EType (Bytes _) -> false
     | EType DBytes, EType Address -> false
     | EType Address, Contract _ -> false
     | EType Address, Enum _ -> false 
     | EType (UInt n), EType Address ->
       if BatString.starts_with !Options.solc_ver "0.4" then
         if n<=160 then true else false
       else false
     | EType Address, EType (UInt n) -> false 
     | EType (SInt n), EType Address -> false 
     | EType Address, EType (SInt n) -> false
     | EType Address, Array _ -> false
     | Array _, EType Address -> false
     | EType (UInt  _), EType String -> false
     | EType String, EType (UInt _) -> false
     | EType DBytes, EType (UInt _) -> false
     | Array (t1, Some n1), Array (t2, Some n2) when n1=n2 -> is_implicitly_convertible t1 t2
     | Array (t1, None), Array (t2, None) -> is_implicitly_convertible t1 t2
     | Array _, Array _ -> false
     | Struct id1, Struct id2 -> BatString.equal id1 id2
     | Contract _, EType (UInt _) -> false 
     | EType (Bytes _), Struct _ -> false
     | Struct _, EType (UInt _) -> false
     | Struct _, EType (SInt _) -> false
     | EType (UInt _), Struct _ -> false
     | EType (UInt _), Contract _ -> false
     | Enum id1, Enum id2 -> BatString.equal id1 id2
     | Enum _, EType Address -> false
     | Struct _, EType Address -> false
     | Contract c1, Contract c2 -> true
     | EType (UInt n1), EType (SInt n2) -> n1 < n2
     | ConstInt, EType (Bytes _) -> true
     | EType (UInt _), EType DBytes -> false
     | EType (UInt _), EType (Bytes _) -> false
     | EType (Bytes _), EType (UInt _) -> false
     | EType (Bytes _), EType Address -> false
     | EType Address, EType (Bytes _)-> false
     | EType Address, EType DBytes -> false 
     | EType _, Array _ -> false
     | Array _, EType _ -> false
     | EType Bool, EType Address -> false
     | EType Address, EType Bool -> false
     | EType Bool, EType String -> false 
     | EType String, EType Bool -> false
     | EType Bool, EType (UInt _) -> false
     | EType (UInt _), EType Bool -> false
     | EType Bool, EType (Bytes _) -> false
     | EType (Bytes _), EType Bool -> false
     | EType Bool, EType DBytes -> false
     | EType DBytes, EType Bool -> false
     | EType String, EType Address -> false
     | EType Address, EType String -> false
     | Struct _, EType (Bytes _) -> false
     | EType DBytes, Enum _ -> false
     | Struct _, Array _ -> false
     | _ -> failwith ("is_implicitly_convertible : " ^ to_string_typ my_typ ^ " vs. " ^ to_string_typ comp_typ))

exception FunctionNotFound of string * string

type t = ((cname*fname*typ list), func) BatMap.t
and cname = id
and fname = id

let empty = BatMap.empty
let add = BatMap.add
let mem = BatMap.mem
let fold = BatMap.foldi
let merge m1 m2 = BatMap.foldi add m1 m2
let dom m = BatSet.of_enum (BatMap.keys m)
let make_key cid fid arg_typs = (cid,fid,arg_typs) 

let find_weak (cid,fid,arg_typs) map =
  BatMap.foldi (fun (cid',fid',typs') v acc ->
    if BatString.equal fid fid' &&
       List.length arg_typs = List.length typs' && (* should be checked first before checking convertibility *)
       List.for_all2 is_implicitly_convertible arg_typs typs'
      then BatSet.add v acc
    else acc
  ) map BatSet.empty

let find (cid,fid,arg_typs) map =
  let funcs =
    BatMap.foldi (fun (cid',fid',typs') v acc ->
      if BatString.equal cid cid' &&
         BatString.equal fid fid' &&
         List.length arg_typs = List.length typs' && (* should be checked first before checking convertibility *)
         List.for_all2 is_implicitly_convertible arg_typs typs'
      then BatSet.add v acc
      else acc
    ) map BatSet.empty
  in
  if BatSet.cardinal funcs = 1 then BatSet.choose funcs else
  if BatSet.cardinal funcs = 0 then raise (FunctionNotFound (cid,fid))
  else
    raise (Failure "FunctionMap-find")
  
let to_string : t -> string
= fun map ->
  let to_string_x (cid,fid,typs) = cid ^ "," ^ fid ^ "," ^ string_of_list ~first:"(" ~last:")" ~sep:"," to_string_typ typs in
  let to_string_y y = string_of_int ((get_finfo y).fid) in
  "{" ^ "\n" ^
  BatMap.foldi (fun x y acc -> 
    acc ^ to_string_x x ^ " -> " ^ to_string_y y ^ "\n"
  ) map ""
  ^ "}"

let mk_fmap_c : contract -> t -> t
= fun (cname,_,_,_,funcs,_) fmap ->
  List.fold_left (fun acc f ->
    let (fid,typs) = get_fsig f in
    add (cname,fid,typs) f acc
  ) fmap funcs

let mk_fmap_p : pgm -> t 
= fun contracts ->
  List.fold_left (fun acc contract ->
    mk_fmap_c contract acc 
  ) empty contracts

let mk_fmap : pgm -> t
= fun pgm -> mk_fmap_p pgm

let is_undef e arg_typs fmap = 
  match e with
  | Lv (Var (fname,_)) 
  | Lv (MemberAccess (_,fname,_,_)) ->
    let fs = find_weak (make_key "DUMMY" fname arg_typs) fmap in
    BatSet.is_empty fs 
  | _ -> failwith ("is_undef : " ^ to_string_exp e)
                  
let rec find_matching_funcs : id -> exp -> typ list -> id list -> t -> func BatSet.t
= fun cname e arg_typs cnames fmap ->
  match e with
  | Lv (Var (fname,_)) ->
    BatSet.singleton (find (make_key cname fname arg_typs) fmap)
  | Lv (MemberAccess (Lv (Var (prefix,_)),fname,_,_)) ->
    if List.mem prefix cnames then (* static call *)
      BatSet.singleton (find (make_key prefix fname arg_typs) fmap)
    else (* method call *)
      find_weak (make_key "DUMMY" fname arg_typs) fmap
  | Lv (MemberAccess (_,fname,_,_)) ->
    find_weak (make_key "DUMMY" fname arg_typs) fmap
  | _ -> failwith ("find_matching_funcs : " ^ to_string_exp e)
