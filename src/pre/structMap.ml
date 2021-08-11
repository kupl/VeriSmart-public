open Lang
open Vocab

type t = (struct_id, members) BatMap.t
and smap = t
and struct_id = string (* "Defined Contract Name"."Struct Name" *)
and members = var_decl list

let add = BatMap.add
let empty = BatMap.empty

let mk_smap_c : smap -> contract -> smap
= fun smap c ->
  let structs = get_structs c in
  List.fold_left (fun acc s -> add (fst s) (snd s) acc) smap structs

let mk_smap : pgm -> t
= fun contracts -> List.fold_left mk_smap_c empty contracts

let find : struct_id -> smap -> members
= fun sname smap ->
  try BatMap.find sname smap
  with Not_found -> failwith "structMap_find"

let to_string : t -> string
= fun smap ->
  "{" ^ "\n" ^
  BatMap.foldi (fun x ylst acc ->
    acc ^ x ^ " -> " ^ string_of_list ~first:"[" ~last:"]" ~sep:"," to_string_var_decl ylst ^ "\n"
  ) smap ""
  ^ "}"
