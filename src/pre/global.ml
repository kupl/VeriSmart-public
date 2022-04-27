open Lang
open FuncMap
open FuncDefUse
open CallGraph
open MakeCfg

type t = {
  pgm         : pgm;
  slines      : string list;
  cnames      : string list;
  gvars       : var list;
  hc_addrs    : BigIntSet.t;
  mem         : ItvDom.Mem.t;
  smap        : StructMap.t;
  enums       : enum list;
  fmap        : FuncMap.t;
  f_defuse    : FuncDefUse.t;
  lhs         : Node.t BatSet.t; (* all loop headers *)
  lhs2        : Node.t BatSet.t; (* loop headers within non-pure/non-view functions *)
  lhs3        : Node.t BatSet.t; (* loop headers within functions that are non-pure/non-view and do not contain public intcalls *)
  callnodes   : (Node.t * fkey) BatSet.t;

  lhs_main    : Node.t BatSet.t;
  lhs2_main   : Node.t BatSet.t;
  lhs3_main   : Node.t BatSet.t;
  callnodes_main : (Node.t * fkey) BatSet.t;

  extcalls    : Node.t BatSet.t;
  call_edges  : CallGraph.edge BatSet.t;
  base_names  : string list;
  base_names_wo_interface : string list;
}

and global = t

(*************************)
(*************************)
(*** Some useful utils ***)
(*************************)
(*************************)

let contain_line : line -> func -> bool
= fun line func ->
  let finfo = get_finfo func in
  finfo.floc.line <= line && line <= finfo.floc.finish_line

let find_func : line -> func list -> func
= fun line funcs -> List.find (contain_line line) funcs

let find_func_containing_line : line -> global -> func
= fun line global ->
  let all_funcs = List.fold_left (fun acc c -> acc @ (get_funcs c)) [] global.pgm in
  find_func line all_funcs

let get_all_fields : global -> var list
= fun global ->
  let field_lst = BatMap.bindings global.smap |> List.map snd in
  let fields = List.fold_left (fun acc members -> acc @ (List.map (fun (v,vinfo) -> (v,vinfo.vtyp)) members)) [] field_lst in
  fields

let get_callee_of_intcall : global -> func -> stmt -> func
= fun global func stmt ->
  let caller_cname = (get_finfo func).scope_s in
  match stmt with
  | Call (lvop,e,args,ethop,gasop,loc,_) ->
    let callees = FuncMap.find_matching_funcs caller_cname e (List.map get_type_exp args) global.cnames global.fmap in
    let _ = assert (BatSet.cardinal callees = 1) in
    BatSet.choose callees
  | _ -> assert false

let is_intcall_from_other_contracts : stmt -> bool
= fun stmt ->
  match stmt with
  | Call (_,Lv (MemberAccess (Lv (Var (x,_)),_,_,_)),_,_,_,_,_) ->
    not (x = !Options.main_contract)
  | Call _ -> false
  | _ -> assert false

let is_live_intcall : func -> stmt -> bool
= fun callee stmt ->
  is_internal_func callee || is_private_func callee || is_view_pure_f callee
  || is_intcall_from_other_contracts stmt

let rec contain_dead_intcall' : global -> func -> stmt -> bool
= fun global f stmt ->
  match stmt with
  | Assign _ | Decl _ -> false
  | Seq (s1,s2) -> contain_dead_intcall' global f s1 || contain_dead_intcall' global f s2
  | Call (lvop,e,args,ethop,gasop,loc,_) when is_undef_call global.fmap stmt -> false

  | Call _ when is_internal_call global.fmap global.cnames stmt ->
    let callee = get_callee_of_intcall global f stmt in
    not (is_live_intcall callee stmt)

  | Call _ -> false
  | Skip -> false
  | If (e,s1,s2,i) -> contain_dead_intcall' global f s1 || contain_dead_intcall' global f s2
  | While (e,s) -> contain_dead_intcall' global f s
  | Break | Continue | Return _ | Throw
  | Assume _ | Assert _ | Assembly _ -> false
  | PlaceHolder -> false (* could be included in modifier that contain function calls *)
  | Unchecked (slst,_) -> List.exists (contain_dead_intcall' global f) slst

let contain_dead_intcall : global -> func -> bool
= fun global f ->
  let reachable = CallGraph.transitive_callees (BatSet.singleton (get_fkey f)) global.call_edges in
  let reachable = BatSet.map (fun k -> FuncMap.find k global.fmap) reachable in
  BatSet.exists (fun f' -> contain_dead_intcall' global f' (get_body f')) reachable

let contain_dead_intcall_cfg' : global -> func -> bool
= fun global f ->
  let cfg = get_cfg f in
  let nodes = nodesof cfg in
  let nodes = List.filter (fun n -> is_internal_call_node global.fmap global.cnames n cfg) nodes in
  List.exists (fun n ->
    let callee = get_callee_of_intcall global f (find_stmt n cfg) in
    not (is_live_intcall callee (find_stmt n cfg))
  ) nodes

let contain_dead_intcall_cfg : global -> func -> bool
= fun global f ->
  let reachable = CallGraph.transitive_callees (BatSet.singleton (Lang.get_fkey f)) global.call_edges in
  let reachable = BatSet.map (fun k -> FuncMap.find k global.fmap) reachable in
  BatSet.exists (fun f' -> contain_dead_intcall_cfg' global f') reachable

let rec contain_extern' : stmt -> bool
= fun stmt ->
  match stmt with
  | Assign _ | Decl _ -> false
  | Seq (s1,s2) -> contain_extern' s1 || contain_extern' s2
   (* | Call (lvop, Lv (MemberAccess (e,"call",_,_)), args, Some eth, gasop, loc, id)
    when is_address (get_type_exp e) -> true *)
  | Call _ when is_external_call stmt -> true
  | Call _ -> false
  | Skip -> false
  | If (e,s1,s2,i) -> contain_extern' s1 || contain_extern' s2
  | While (e,s) -> contain_extern' s
  | Break | Continue | Return _ | Throw
  | Assume _ | Assert _ | Assembly _ -> false
  | PlaceHolder -> assert false
  | Unchecked (slst,_) -> List.exists contain_extern' slst

let contain_extern : global -> func -> bool
= fun global f ->
  let reachable = CallGraph.transitive_callees (BatSet.singleton (get_fkey f)) global.call_edges in
  BatSet.exists (fun k -> contain_extern' (get_body (FuncMap.find k global.fmap))) reachable


let is_constant_address : global -> var -> bool
= fun global var ->
  let _ = assert (is_address (get_type_var var)) in
  let itv = ItvDom.Val.itv_of (ItvDom.Mem.find var global.mem) in
  if Itv.is_top itv || Itv.is_bot itv then false
  else
    (match itv with
     | Itv (V l, V u) when BatBig_int.equal l u -> true
     | _ -> false)

(************************************)
(*** Collect hard-coded addresses ***)
(************************************)

let rec hc_lv : lv -> BigIntSet.t
= fun lv ->
  match lv with
  | Var _ -> BigIntSet.empty
  | MemberAccess (e,_,_,_) -> hc_exp e
  | IndexAccess (e,None,_) -> hc_exp e
  | IndexAccess (e1,Some e2,_) -> BigIntSet.union (hc_exp e1) (hc_exp e2)
  | Tuple (eops,_) ->
    List.fold_left (fun acc eop ->
      match eop with
      | None -> acc
      | Some e -> BigIntSet.union (hc_exp e) acc
    ) BigIntSet.empty eops

and hc_exp : exp -> BigIntSet.t
= fun exp ->
  match exp with
  | Int n -> BigIntSet.empty
  | Real _ | Str _ -> BigIntSet.empty
  | Lv lv -> hc_lv lv
  | Cast (EType Address, Int n) when not (BatBig_int.equal n BatBig_int.zero) -> BigIntSet.singleton n
  | Cast (_,e) -> hc_exp e
  | BinOp (_,e1,e2,_) -> BigIntSet.union (hc_exp e1) (hc_exp e2)
  | UnOp (_,e,_) -> hc_exp e
  | True | False -> BigIntSet.empty
  | ETypeName _ -> BigIntSet.empty
  | _ -> failwith "hc_exp: temp expressions encountered"

let rec hca_s : stmt -> BigIntSet.t
= fun stmt ->
  let is_address_array typ = match typ with Array (EType Address,_) -> true | _ -> false in
  match stmt with
  | Assign (lv,Int n,_) when is_address (get_type_lv lv) && not (BatBig_int.equal n BatBig_int.zero) ->
    BigIntSet.singleton n
  | Assign (lv,Lv (Tuple (eops,_)),_) when is_address_array (get_type_lv lv) ->
    List.fold_left (fun acc eop ->
      match eop with
      | Some (Int n) -> BigIntSet.add n acc
      | Some _ -> acc
      | None -> acc
    ) BigIntSet.empty eops
  | Assign (lv,e,_) -> hc_exp e
  | Decl _ -> BigIntSet.empty
  | Assume (e,_) -> hc_exp e
  | Assert (e,_,_) -> hc_exp e
  | Call (lvop,_,args,_,_,loc,_) ->
    let hc1 = match lvop with None -> BigIntSet.empty | Some lv -> hc_lv lv in
    let hc2 = List.fold_left (fun acc arg -> BigIntSet.union (hc_exp arg) acc) BigIntSet.empty args in
    BigIntSet.union hc1 hc2
  | Seq (s1,s2) -> BigIntSet.union (hca_s s1) (hca_s s2)
  | Skip -> BigIntSet.empty
  | If (e,s1,s2,_) ->
    BigIntSet.union (hc_exp e) (BigIntSet.union (hca_s s1) (hca_s s2))
  | While (e,s) -> BigIntSet.union (hc_exp e) (hca_s s)
  | Break | Continue -> BigIntSet.empty
  | Return (eop,_) ->
    (match eop with
     | None -> BigIntSet.empty
     | Some e -> hc_exp e)
  | Throw | Assembly _ | PlaceHolder -> BigIntSet.empty
  | Unchecked (lst,_) ->
    List.fold_left (fun acc s -> BigIntSet.union (hca_s s) acc) BigIntSet.empty lst

let hca_f : func -> BigIntSet.t
= fun f -> hca_s (get_body f)

let hca_c : contract -> BigIntSet.t
= fun c ->
  List.fold_left (fun acc f ->
    BigIntSet.union (hca_f f) acc
  ) BigIntSet.empty (get_funcs c)

let collect_hc_addrs : pgm -> BigIntSet.t
= fun contracts ->
  List.fold_left (fun acc c ->
    BigIntSet.union (hca_c c) acc
  ) BigIntSet.empty contracts

let get_basenames pgm =
  let main_c = get_main_contract pgm in
  let bases = (get_cinfo main_c).inherit_order in (* left: main (child), right: parent *)
  let bases = List.map (find_contract_nid pgm) bases  in
  let bases_wo_interface = List.filter is_contract_kind bases in
  let bases, bases_wo_interface = List.map get_cname bases, List.map get_cname bases_wo_interface in
  (* let _ = print_endline (string_of_list Vocab.id bases) in
  let _ = assert false in *)
  (bases, bases_wo_interface)

let get_base_contracts pgm =
  let main_c = get_main_contract pgm in
  let bases = (get_cinfo main_c).inherit_order in (* left: main (child), right: parent *)
  let bases = List.map (find_contract_nid pgm) bases  in
  let bases_wo_interface = List.filter is_contract_kind bases in
  (bases, bases_wo_interface)

let get_full_basenames pgm c =
  let bases = (get_cinfo c).inherit_order in (* left: main (child), right: parent *)
  let bases = List.map (find_contract_nid pgm) bases in
  let bases = List.map get_cname bases in
  bases

let get_full_base_contracts pgm c =
  let bases = (get_cinfo c).inherit_order in (* left: main (child), right: parent *)
  let bases = List.map (find_contract_nid pgm) bases  in
  bases

let make_global_info : pgm -> string list -> global
= fun p slines ->
  let cnames = get_cnames p in
  let gvars = get_gvars p in
  let hc_addrs = collect_hc_addrs p in
  let smap = StructMap.mk_smap p in
  let enums = get_enums (get_main_contract p) in
  let fmap = FuncMap.mk_fmap p in
  let defuse = FuncDefUse.compute cnames fmap in
  let call_edges = CallGraph.collect_call_edges ~inlined_cfg:false cnames fmap p in
  let bases,bases_wo_interface = get_basenames p in
  {pgm = p;
   slines = slines;
   cnames = cnames;
   hc_addrs = hc_addrs;
   gvars = gvars;
   mem = ItvDom.Mem.bot;
   smap = smap;
   enums = enums;
   fmap = fmap;
   f_defuse = defuse;

   lhs = BatSet.empty;
   lhs2 = BatSet.empty;
   lhs3 = BatSet.empty;
   lhs_main = BatSet.empty;
   lhs2_main = BatSet.empty;
   lhs3_main = BatSet.empty;
   callnodes = BatSet.empty;
   callnodes_main = BatSet.empty;
   extcalls = BatSet.empty;

   call_edges = call_edges;
   base_names = bases;
   base_names_wo_interface = bases_wo_interface
  }
