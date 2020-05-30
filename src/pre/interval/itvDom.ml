open Itv
open GTaint
open Lang
open Vocab

module Loc = struct
  type t = id * typ

  let compare (id1,t1) (id2,t2) = BatString.compare id1 id2
  let of_var id t = (id,t)
  let typ_of (id,t) = t
  let to_string (id,t) = id
end

module Val = struct
  type t = Itv.t * GTaint.t * BTaint.t

  let itv_of (a,_,_) = a
  let gtaint_of (_,b,_) = b
  let btaint_of (_,_,c) = c

  let of_itv itv = (itv, GTaint.bot, BTaint.bot)

  let update_itv a' (a,b,c) = (a',b,c) 
  let update_gtaint b' (a,b,c) = (a,b',c)
  let update_btaint c' (a,b,c) = (a,b,c')

  let bot = (Itv.bot, GTaint.bot, BTaint.bot) 

  let le    (a1,b1,c1) (a2,b2,c2) = Itv.le a1 a2 && GTaint.le b1 b2 && BTaint.le c1 c2 
  let meet  (a1,b1,c1) (a2,b2,c2) = (Itv.meet a1 a2, GTaint.meet b1 b2, BTaint.meet c1 c2)
  let join  (a1,b1,c1) (a2,b2,c2) = (Itv.join a1 a2, GTaint.join b1 b2, BTaint.join c1 c2)
  let widen (a1,b1,c1) (a2,b2,c2) = (Itv.widen a1 a2, GTaint.widen b1 b2, BTaint.widen c1 c2)

  let to_string v =
    "(" ^ Itv.to_string (itv_of v) ^ ", " ^ GTaint.to_string (gtaint_of v) ^ ", " ^ BTaint.to_string (btaint_of v) ^ ")"
end 

module Mem = struct 
  type t = (Loc.t, Val.t) BatMap.t

  let bot = BatMap.empty

  let find x s = try BatMap.find x s with Not_found -> Val.bot
  let find2 x s = try BatMap.find x s with Not_found -> (Itv.top, GTaint.bot, BTaint.bot) (* for linearization purpose, taint values will not be used *) 

  let filter = BatMap.filter
  let map = BatMap.mapi

  let update = BatMap.add
  let weak_update x v m =
    let v' = Val.join (find x m) v in
    update x v' m

  let meet : t -> t -> t
  = fun mem1 mem2 -> 
    let meet' key opt_d1 opt_d2 = 
      match opt_d1,opt_d2 with
      | None,_ 
      | _,None -> None
      | Some v1,Some v2 -> Some (Val.meet v1 v2)
    in BatMap.merge meet' mem1 mem2

  let join : t -> t -> t
  = fun mem1 mem2 -> 
    let join' key opt_d1 opt_d2 = 
      match opt_d1,opt_d2 with
      | None,None -> None
      | None,Some v
      | Some v,None -> Some v
      | Some v1,Some v2 -> Some (Val.join v1 v2)
    in BatMap.merge join' mem1 mem2

  let widen : t -> t -> t
  = fun mem1 mem2 ->
    let widen' key opt_d1 opt_d2 =
      match opt_d1,opt_d2 with
      | None,None -> None
      | None,Some v
      | Some v,None -> Some v
      | Some v1,Some v2 -> Some (Val.widen v1 v2) 
    in BatMap.merge widen' mem1 mem2

  let le : t -> t -> bool 
  = fun mem1 mem2 ->
    if mem1 == mem2 then true else
      let enum1 = BatMap.enum mem1 in
      let enum2 = BatMap.enum mem2 in
      let rec loop : (Loc.t * Val.t) option -> (Loc.t * Val.t) option -> bool
      = fun e1 e2 ->
        match e1,e2 with
        | Some (k1,v1),Some (k2,v2) ->
          let c = Loc.compare k1 k2 in
          if c=0 then
            if Val.le v1 v2 then loop (BatEnum.get enum1) (BatEnum.get enum2) else false
          else if c<0 then
            if Val.le v1 Val.bot then loop (BatEnum.get enum1) e2 else false
          else
            loop e1 (BatEnum.get enum2)
        | Some (_,v),None ->
          if Val.le v Val.bot then loop (BatEnum.get enum1) e2 
          else false 
        | None,Some _ -> true
        | None,None -> true
      in
      loop (BatEnum.get enum1) (BatEnum.get enum2)

  let fold = BatMap.foldi

  let to_string : t -> string
  = fun mem ->
    "{" ^ "\n" ^
    BatMap.foldi (fun x y acc -> 
      acc ^ Loc.to_string x ^ " -> " ^ Val.to_string y ^ "\n"
    ) mem ""
    ^ "}"
end
