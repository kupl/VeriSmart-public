open Itv
open ItvDom
open Lang
open Vocab
open Path
open Options

(* assign top values to input parameters of public/external functions *)
let update_params : func -> Mem.t -> Mem.t
= fun f mem ->
  match get_vis f with
  | Public | External ->
    (* For interval domains, always assign top values for parameters of public functions *)
    let params = get_params f in
    List.fold_left (fun acc (x,xinfo) ->
      let loc = Loc.of_var x xinfo.vtype in
      let v = Mem.find loc mem in
      let itop = Itv.top in
      Mem.update loc (Val.update_itv itop v) acc
    ) mem params
  | _ -> mem

let onestep' : Global.t -> id -> Path.t -> Mem.t -> Mem.t
= fun global main_name path mem ->
  let fk = Path.get_fkey path in
  let bp = Path.get_bp path in
  let func = FuncMap.find fk global.fmap in
  let mem = update_params func mem in
  List.fold_left (fun acc node ->
    ItvSem.eval_stmt global main_name func node acc
  ) mem bp

let onestep : Global.t -> id -> PathSet.t -> Mem.t -> Mem.t
= fun global main_name paths mem ->
  PathSet.fold (fun path acc ->
    onestep' global main_name path acc
  ) paths mem

let rec fix : Global.t -> id -> int -> PathSet.t -> Mem.t -> Mem.t
= fun global main_name cnt paths mem ->
  let mem' = onestep global main_name paths mem in
  let mem' = Mem.widen mem mem' in
    if Mem.le mem' mem then mem'
    else fix global main_name (cnt+1) paths mem'

let weed_out : Global.t -> Mem.t -> Mem.t
= fun global mem ->
  if !Options.intra then Mem.filter (fun k _ -> not (List.mem k global.gvars)) mem
  else mem

let run : pgm -> Global.t -> PathSet.t -> Mem.t 
= fun pgm global paths ->
  let main_name = get_cname (get_main_contract pgm) in
  let init = List.fold_left (fun acc g -> Mem.update g (Itv.bot, GTaint.singleton g, BTaint.bot) acc) Mem.bot global.gvars in 
  let mem = fix global main_name 0 paths init in
  let mem = weed_out global mem in
  mem
