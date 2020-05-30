open Lang
open FuncMap
open FuncDefUse

type t = {
  cnames   : string list;
  gvars    : var list;
  smap     : StructMap.t;
  enums    : enum list;
  fmap     : FuncMap.t;
  f_defuse : FuncDefUse.t;
  lhs      : Node.t BatSet.t
}
and global = t

let get_cfg : fkey -> global -> cfg
= fun k global -> Lang.get_cfg (FuncMap.find k global.fmap)

let get_all_lhs_f : func -> Node.t BatSet.t
= fun f -> (Lang.get_cfg f).lh_set

let get_all_lhs_c : contract -> Node.t BatSet.t
= fun c ->
  List.fold_left (fun acc f ->
    BatSet.union (get_all_lhs_f f) acc
  ) BatSet.empty (get_funcs c)

let get_all_lhs : pgm -> Node.t BatSet.t
= fun p ->
  List.fold_left (fun acc c ->
    BatSet.union (get_all_lhs_c c) acc
  ) BatSet.empty p 

let make_global_info : pgm -> global
= fun p ->
  let cnames = get_cnames p in
  let gvars = get_gvars p in
  let smap = StructMap.mk_smap p in
  let enums = get_enums (get_main_contract p) in
  let fmap = FuncMap.mk_fmap p in
  let defuse = FuncDefUse.compute cnames fmap in
  let lhs = get_all_lhs p in
  {cnames = cnames;
   gvars = gvars;
   smap = smap;
   enums = enums;
   fmap = fmap; 
   f_defuse = defuse;
   lhs = lhs}
