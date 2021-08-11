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
  lhs      : Node.t BatSet.t;
}
and global = t

let make_global_info : pgm -> global
= fun p ->
  let cnames = get_cnames p in
  let gvars = get_gvars p in
  let smap = StructMap.mk_smap p in
  let enums = get_enums (get_main_contract p) in
  let fmap = FuncMap.mk_fmap p in
  let defuse = FuncDefUse.compute cnames fmap in
  {cnames = cnames;
   gvars = gvars;
   smap = smap;
   enums = enums;
   fmap = fmap; 
   f_defuse = defuse;
   lhs = BatSet.empty;
  }
