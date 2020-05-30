open Lang
open Vocab

type t = (id, structure list) BatMap.t
and smap = t

let add = BatMap.add
let empty = BatMap.empty

let mk_smap_c : smap -> contract -> smap
= fun smap c -> add (get_cname c) (get_structs c) smap

let mk_smap : pgm -> t
= fun contracts -> List.fold_left mk_smap_c empty contracts

let find : id -> exp -> smap -> structure
= fun ctx_cname e smap ->
  match e with
  | Lv (Var (sname,_)) ->
    let structs = BatMap.find ctx_cname smap in
    List.find (fun (sname',_) -> sname = sname') structs
  | Lv (MemberAccess (Lv (Var (prefix,_)),sname,_,_)) ->
    let structs = BatMap.find prefix smap in
    List.find (fun (sname',_) -> sname = sname') structs
  | _ -> failwith "structMap_find"

let to_string : t -> string
= fun map ->
  let to_string_x cname = cname in
  let to_string_y (sname,decls) = sname in
  "{" ^ "\n" ^
  BatMap.foldi (fun x ylst acc ->
    acc ^ to_string_x x ^ " -> " ^ string_of_list ~first:"[" ~last:"]" ~sep:"," to_string_y ylst ^ "\n"
  ) map ""
  ^ "}"
