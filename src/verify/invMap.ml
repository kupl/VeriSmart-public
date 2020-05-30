open Lang
open Vlang
open Itv
open ItvDom
open Simplification

type t = (Node.t, vformula) BatMap.t
and invmap

let add = BatMap.add
let mem = BatMap.mem
let find x m = try BatMap.find x m with Not_found -> VTrue
let fold = BatMap.foldi
let map = BatMap.mapi
let empty = BatMap.empty
let is_empty= BatMap.is_empty
let exists = BatMap.exists

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
    Node.to_string k ^ " -> " ^ to_string_vformula d ^ "\n"
  ) m ""
  ^ "]"

(* propagte transaction invariant to loop headers *)
(*
let prop_tinv : triple -> triple
= fun (tinv,lmap,fspecs) ->
  let lmap' = LoopInvMap.map (fun _ d -> simplify (VAnd (tinv, d))) lmap in
  (tinv, lmap', fspecs)
*)
