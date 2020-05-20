open Itv
open ItvDom
open ItvSem2
open Vlang

let rec fix : int -> vformula -> Mem.t -> Mem.t
= fun cnt vf mem ->
  let mem' = eval_vf vf mem in
  let mem' = Mem.meet mem mem' in
    if Mem.le mem mem' then mem'
    else fix (cnt+1) vf mem'

let run : vformula -> Mem.t
= fun vf ->
  let locs = free_vf vf in
  let init = BatSet.fold (fun loc acc -> Mem.update loc (Itv.top,GTaint.bot,BTaint.bot) acc) locs Mem.bot in
  let mem = fix 0 vf init in
  let mem = Mem.filter (fun _ v -> not (is_top (Val.itv_of v))) mem in
  mem
