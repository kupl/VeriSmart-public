open Lang
open Vlang
open Simplification

(* function specifications for internal transactions *)
type t = (key, (pre * post)) BatMap.t
and key = Node.t
and pre = vformula
and post = vformula

let to_string_key = Node.to_string

let add = BatMap.add
let mem = BatMap.mem
let find x m = try BatMap.find x m with Not_found -> assert false
let find_pre x m = try fst (BatMap.find x m) with Not_found -> assert false
let find_post x m = try snd (BatMap.find x m) with Not_found -> assert false

let foldi = BatMap.foldi
let map = BatMap.mapi
let mem = BatMap.mem
let empty = BatMap.empty
let is_empty= BatMap.is_empty
let exists = BatMap.exists
let bindings = BatMap.bindings

let equal m1 m2 = BatMap.equal (fun (pre1,post1) (pre2,post2) -> equal_vf pre1 pre2 && equal_vf post1 post2) m1 m2

let merge : t -> t -> t
= fun m1 m2 ->
  let merge' k opt_v1 opt_v2 =
    match opt_v1, opt_v2 with
    | None, None -> None 
    | None, Some v
    | Some v, None -> Some v
    | Some (pre1,post1), Some (pre2,post2) ->
      let pre = simplify_both (VAnd (pre1,pre2)) in
      let post = simplify_both (VAnd (post1,post2)) in
      Some (pre, post)
  in
  BatMap.merge merge' m1 m2

let simplify : t -> t
= fun m -> map (fun _ (pre,post) -> (simplify_both pre, simplify_both post)) m

let to_string : t -> string
= fun m ->
  "[" ^ "\n" ^
  BatMap.foldi (fun k (pre,post) acc ->
    acc ^
     to_string_key k ^ " -> " ^ "(" ^ to_string_vformula pre ^ ", " ^ to_string_vformula post ^ ")" ^ "\n"
  ) m ""
  ^ "]"
