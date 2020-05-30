open Lang
open Vocab

type t =
  | Top (* may be tainted from block information *)
  | Bot (* not taited by block information *)

let bot = Bot
let top = Top

let is_bot v = (v = Bot)
let is_top v = (v = Top)

let le v1 v2 =
  match v1,v2 with
  | Bot,Bot -> true
  | Bot,Top -> true
  | Top,Bot -> false
  | Top,Top -> true

let meet v1 v2 =
  match v1,v2 with
  | Top,Top -> Top
  | _ -> Bot

let join v1 v2 =
  match v1,v2 with
  | Bot,Bot -> Bot
  | _ -> Top

let widen v1 v2 = join v1 v2

let to_string v =
  match v with
  | Bot -> "NotTainted"
  | Top -> "MayTainted"
