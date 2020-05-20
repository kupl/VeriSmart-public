open Lang
open Vocab

(* aims to track from what global variables may be affected *)
type t = var BatSet.t

let bot = BatSet.empty 
let is_bot = BatSet.is_empty

let le v1 v2 = BatSet.subset v1 v2
let meet v1 v2 = BatSet.intersect v1 v2
let join v1 v2 = BatSet.union v1 v2
let widen v1 v2 = join v1 v2 (* domain is finite *)

let singleton = BatSet.singleton 

let to_string set = string_of_set (fst|>id) set
