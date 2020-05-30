open Vocab

type t' = 
  | V of BatBig_int.t
  | PInf 
  | NInf

type t = Itv of t' * t' | Bot  

let top = Itv (NInf, PInf)
let bot = Bot

let zero = BatBig_int.zero
let is_pos n = BatBig_int.sign_big_int n = 1
let is_zero n = BatBig_int.sign_big_int n = 0

let upper_int itv =
  match itv with
  | Itv (_,V n) -> n
  | _ -> raise (Failure "upper_int")

let lower_int itv =
  match itv with
  | Itv (V n,_) -> n
  | _ -> raise (Failure "lower_int")

let to_string' : t' -> string
= fun v -> 
  match v with
  | V n -> BatBig_int.to_string n
  | PInf -> "+oo"
  | NInf -> "-oo"

let to_string : t -> string
= fun itv ->
  match itv with
  | Itv (l,u) -> "[" ^ (to_string' l) ^ ", " ^ (to_string' u) ^"]"
  | Bot -> "bot"

let le' : t' -> t' -> bool
= fun v1 v2 ->
  match v1,v2 with
  | NInf,_ -> true
  | _,PInf -> true
  | V n1,V n2 -> BatBig_int.le_big_int n1 n2
  | _,_ -> false

let eq' : t' -> t' -> bool
= fun v1 v2 ->
  match v1,v2 with
  | NInf,NInf 
  | PInf,PInf -> true
  | V n1,V n2 -> BatBig_int.equal n1 n2
  | _,_ -> false

let lt' : t' -> t' -> bool
= fun v1 v2 -> le' v1 v2 && not (eq' v1 v2)

let gt' : t' -> t' -> bool
= fun v1 v2 -> not (le' v1 v2) (* check *) 

let ge' : t' -> t' -> bool
= fun v1 v2 -> not (lt' v1 v2) 

let min' : t' -> t' -> t' 
= fun v1 v2 -> if le' v1 v2 then v1 else v2

let max' : t' -> t' -> t'
= fun v1 v2 -> if le' v1 v2 then v2 else v1 

let plus' : t' -> t' -> t' 
= fun v1 v2 ->
  match v1,v2 with
  | V n1,V n2 -> V (BatBig_int.add n1 n2)
  | PInf,NInf -> raise (Failure "itv.ml : plus'")
  | NInf,PInf -> raise (Failure "itv.ml : plus'")
  | PInf,_ -> PInf
  | NInf,_ -> NInf
  | _,PInf -> PInf
  | _,NInf -> NInf

let minus' : t' -> t' -> t'
= fun v1 v2 ->
  match v1,v2 with
  | V n1,V n2 -> V (BatBig_int.sub n1 n2)
  | PInf,PInf -> raise (Failure "itv.ml : minus'")
  | NInf,NInf -> raise (Failure "itv.ml : minus'")
  | PInf,_ -> PInf
  | NInf,_ -> NInf
  | _,PInf -> NInf
  | _,NInf -> PInf 

let times' : t' -> t' -> t'
= fun v1 v2 ->
  match v1,v2 with 
  | V n1,V n2 -> V (BatBig_int.mul n1 n2)
  | PInf,PInf
  | NInf,NInf -> PInf
  | PInf,NInf
  | NInf,PInf -> NInf
  | PInf,V n
  | V n,PInf ->
    if BatBig_int.gt_big_int n zero then PInf else 
    if BatBig_int.lt_big_int n zero then NInf
    else (V zero)
  | NInf,V n
  | V n,NInf ->
    if BatBig_int.gt_big_int n zero then NInf else 
    if BatBig_int.lt_big_int n zero then PInf
    else (V zero)

let divide' : t' -> t' -> t'
= fun v1 v2 ->
  match v1,v2 with
  | V n1, V n2 ->
    if BatBig_int.equal n2 zero then raise (Failure "itv.ml : divide'1")
    else V (BatBig_int.div n1 n2)
  | PInf,PInf
  | NInf,NInf -> PInf
  | NInf,PInf
  | PInf,NInf -> NInf
  | NInf,V n ->
    if BatBig_int.lt_big_int n zero then PInf else (* n<0 *)
    if BatBig_int.gt_big_int n zero then NInf      (* n>0 *)
    else raise (Failure "itv.ml : divide'2") 
  | PInf,V n ->
    if BatBig_int.lt_big_int n zero then NInf else (* n<0 *)
    if BatBig_int.gt_big_int n zero then PInf      (* n>0 *)
    else raise (Failure "itv.ml : divide'3")
  | V _,PInf
  | V _,NInf -> V zero

let modulo' : t' -> t' -> t'
= fun v1 v2 ->
  match v1,v2 with
  | V n1, V n2 ->
    if BatBig_int.equal n2 zero then raise (Failure "itv.ml : divide'2")
    else V (BatBig_int.modulo n1 n2) 
  | PInf,PInf 
  | PInf,NInf -> PInf
  | NInf,PInf
  | NInf,NInf -> NInf
  | NInf,V n ->
    if BatBig_int.lt_big_int n zero then V (BatBig_int.succ n) else              (* n<0 => n+1 *)
    if BatBig_int.gt_big_int n zero then V (BatBig_int.succ (BatBig_int.neg n))  (* n>0 => -n+1 *)
    else raise (Failure "itv.ml : modulo'2")
  | PInf,V n ->
    if BatBig_int.lt_big_int n zero then V (BatBig_int.neg (BatBig_int.succ n)) else  (* n<0 => -(n+1) *)
    if BatBig_int.gt_big_int n zero then V (BatBig_int.pred n)                        (* n>0 => (n-1) *)
    else raise (Failure "itv.ml : modulo'3")
  | V n,PInf
  | V n,NInf -> V n

let power' : t' -> t' -> t'
= fun v1 v2 ->
  match v1,v2 with
  | V n1, V n2 -> V (BatBig_int.pow n1 n2)
  | _ -> raise (Failure "power'")

let lower_widen' : t' -> t' -> t'
= fun v1 v2 ->
  if lt' v2 v1 then NInf 
  else v1
  
let upper_widen' : t' -> t' -> t'
= fun v1 v2 ->
  if gt' v2 v1 then PInf
  else v1

let is_const : t -> bool
= fun itv ->
  match itv with
  | Itv (V n1,V n2) when BatBig_int.equal n1 n2 -> true
  | _ -> false

let const_of : t -> BatBig_int.t
= fun itv ->
  match itv with
  | Itv (V n1,V n2) when is_const itv -> n1
  | _ -> raise (Failure "extract_const")

let is_top : t -> bool
= fun itv -> itv = top

let is_bot : t -> bool
= fun itv ->
  match itv with
  | Bot -> true
  | Itv (l,u) -> l = PInf || u = NInf || not (le' l u)

let le : t -> t -> bool
= fun itv1 itv2 ->
  if is_bot itv1 then true else
  if is_bot itv2 then false 
  else
    match itv1,itv2 with
    | Itv (l1,u1),Itv (l2,u2) -> le' l2 l1 && le' u1 u2
    | _ -> raise (Failure "itv.ml : le")

let eq : t -> t -> bool
= fun itv1 itv2 ->
  if is_bot itv1 && is_bot itv2 then true else
  if is_bot itv1 || is_bot itv2 then false
  else
    match itv1,itv2 with
    | Itv (l1,u1),Itv (l2,u2) -> eq' l1 l2 && eq' u1 u2
    | _ -> raise (Failure "itv.ml : eq")

let plus : t -> t -> t
= fun itv1 itv2 ->
  if is_bot itv1 || is_bot itv2 then Bot
  else
    match itv1,itv2 with
    | Itv (l1,u1),Itv (l2,u2) -> Itv (plus' l1 l2, plus' u1 u2) 
    | _ -> raise (Failure "itv.ml : plus") 

let minus : t -> t -> t
= fun itv1 itv2 ->
  if is_bot itv1 || is_bot itv2 then Bot
  else
    match itv1,itv2 with
    | Itv (l1,u1),Itv (l2,u2) -> Itv (minus' l1 u2, minus' u1 l2)
    | _ -> raise (Failure "itv.ml : minus")

let times : t -> t -> t
= fun itv1 itv2 ->
  if is_bot itv1 || is_bot itv2 then Bot
  else
    match itv1,itv2 with
    | Itv (l1,u1),Itv (l2,u2) -> 
      let x1 = times' l1 l2 in
      let x2 = times' l1 u2 in
      let x3 = times' u1 l2 in
      let x4 = times' u1 u2 in 
      let l = min' (min' x1 x2) (min' x3 x4) in
      let u = max' (max' x1 x2) (max' x3 x4) in
      Itv (l,u)
    | _ -> raise (Failure "itv.ml : times")

let divide : t -> t -> t
= fun itv1 itv2 -> (* itv1/itv2 *)
  if is_bot itv1 || is_bot itv2 then bot else
  if eq (Itv (V zero,V zero)) itv2 then top else
  if le (Itv (V zero,V zero)) itv2 then top else
    match itv1,itv2 with
    | Itv (l1,u1),Itv (l2,u2) ->
      let x1 = divide' l1 l2 in
      let x2 = divide' l1 u2 in
      let x3 = divide' u1 l2 in
      let x4 = divide' u1 u2 in
      let l = min' (min' x1 x2) (min' x3 x4) in
      let u = max' (max' x1 x2) (max' x3 x4) in
      Itv (l,u)
    | _ -> raise (Failure "itv.ml : divide")

let modulo : t -> t -> t
= fun itv1 itv2 -> (* itv1 mod itv2 *)
  if is_bot itv1 || is_bot itv2 then bot else
  if eq (Itv (V zero,V zero)) itv2 then top else
  if le (Itv (V zero,V zero)) itv2 then top else
    match itv1,itv2 with
    | Itv (l1,u1),Itv (l2,u2) ->
      let x1 = modulo' l1 l2 in
      let x2 = modulo' l1 u2 in
      let x3 = modulo' u1 l2 in
      let x4 = modulo' u1 u2 in
      let l = min' (min' x1 x2) (min' x3 x4) in
      let u = max' (max' x1 x2) (max' x3 x4) in
      Itv (l,u)
    | _ -> raise (Failure "itv.ml : modulo")

let power : t -> t -> t 
= fun itv1 itv2 ->
  if is_bot itv1 || is_bot itv2 then Bot
  else
    match itv1,itv2 with
    | Itv (V l1,V u1),Itv (V l2,V u2)
      when is_pos l1 && is_pos u1 && (is_pos l2 || is_zero l2) && (is_pos u2 || is_zero l2) ->
      Itv (power' (V l1) (V l2), power' (V u1) (V u2))
    | Itv _,Itv _ -> top
    | _ -> raise (Failure "itv.ml : times")

let join : t -> t -> t
= fun itv1 itv2 ->
  if le itv1 itv2 then itv2 else
  if le itv2 itv1 then itv1
  else
    match itv1,itv2 with
    | Itv (l1,u1),Itv (l2,u2) -> Itv (min' l1 l2, max' u1 u2)  
    | _ -> raise (Failure "itv.ml : join")

let meet : t -> t -> t
= fun itv1 itv2 ->
  if le itv1 itv2 then itv1 else (* bot related op is included in le *) 
  if le itv2 itv1 then itv2
  else
    match itv1,itv2 with
    | Itv (l1,u1),Itv (l2,u2) -> Itv (max' l1 l2, min' u1 u2)  
    | _ -> raise (Failure "itv.ml : meet") 

let widen : t -> t -> t
= fun itv1 itv2 ->
  if is_bot itv1 then itv2 else
  if is_bot itv2 then itv1
  else
    match itv1,itv2 with
    | Itv (l1,u1),Itv (l2,u2) -> 
      Itv (lower_widen' l1 l2, upper_widen' u1 u2) 
    | _ -> raise (Failure "itv.ml : widen") 
