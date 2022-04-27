open Lang
open Vlang
open Simplification

type t = (key, vformula) BatMap.t
and key =
  | Plain of Node.t
  | Ctx of Node.t * Node.t (* external call-site as context *)

let to_string_key : key -> string
= fun k ->
  match k with
  | Plain n -> Node.to_string n
  | Ctx (n1,n2) -> "(" ^ Node.to_string n1 ^ "," ^ Node.to_string n2 ^ ")"

let add = BatMap.add
let mem = BatMap.mem
let find x m = try BatMap.find x m with Not_found -> assert false
let foldi = BatMap.foldi
let map = BatMap.mapi
let empty = BatMap.empty
let is_empty= BatMap.is_empty
let exists = BatMap.exists
let bindings = BatMap.bindings

let equal m1 m2 = BatMap.equal equal_vf m1 m2

let merge : t -> t -> t
= fun m1 m2 ->
  let merge' k opt_v1 opt_v2 =
    match opt_v1, opt_v2 with
    | None, None -> None 
    | None, Some v
    | Some v, None -> Some v
    | Some v1, Some v2 -> Some (simplify_both (VAnd (v1,v2))) in
  BatMap.merge merge' m1 m2

let simplify : t -> t
= fun m -> map (fun _ vf -> simplify_both vf) m

let to_string : t -> string
= fun m ->
  "[" ^ "\n" ^
  BatMap.foldi (fun k d acc ->
    acc ^
     to_string_key k ^ " -> " ^ to_string_vformula d ^ "\n"
  ) m ""
  ^ "]"
