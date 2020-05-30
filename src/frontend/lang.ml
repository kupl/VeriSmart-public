open Vocab
open Options

module Node = struct
  type t = ENTRY | EXIT | Node of int
  let equal n1 n2 =
    match n1, n2 with
    | ENTRY, ENTRY -> true
    | EXIT, EXIT -> true
    | Node i1, Node i2 -> i1 = i2
    | _, _ -> false

  let less n1 n2 =
    match n1, n2 with
    | ENTRY, ENTRY -> n1
    | ENTRY, EXIT -> n1
    | EXIT, ENTRY -> n2
    | Node i1, Node i2 -> 
      if i1 <= i2 then n1 else n2
    | Node _, ENTRY -> n2
    | ENTRY, Node _ -> n1
    | _, _ -> EXIT

  let hash = Hashtbl.hash

  let compare = Stdlib.compare

  let entry = ENTRY
  let exit = EXIT

  let nid = ref 0

  let make () = nid := !nid + 1; Node !nid

  let to_string : t -> string
  = fun n ->
    match n with
    | ENTRY -> "ENTRY"
    | EXIT -> "EXIT"
    | Node i -> string_of_int i
end

type node = Node.t

module G = Graph.Persistent.Digraph.Concrete (Node)
module Scc = Graph.Components.Make(G)

let trans_node = Node.Node 0

(********************)
(********************)
(***** language *****)
(********************)
(********************)

type pgm = contract list
and contract = id * state_var_decl list * structure list * enum list * func list * cinfo

and state_var_decl = id * exp option * vinfo

and structure = id * var_decl list
and var_decl = id * vinfo

and enum = id * enum_mem list
and enum_mem = id

and func = id * param list * ret_param list * stmt * finfo
and param = id * vinfo
and ret_param = id * vinfo

and fsig = id * typ list
and fkey = id * id * typ list
and func_decl = id * var list * var list 
and visibility = Public | Internal | External | Private

and var = id * typ

and stmt =
  | Assign of lv * exp * loc
  | Decl of lv
  | Seq of stmt * stmt
  | Call of lv option * exp * exp list * loc * int (* int for call-site id *) 
  | Skip
  | If of exp * stmt * stmt
  | While of exp * stmt
  | Break
  | Continue
  | Return of exp option * loc
  | Throw
  | Assume of exp * loc
  | Assert of exp * loc (* used to check safety conditions *)
  | Assembly of (id * int) list * loc 

and exp =
  | Int of BatBig_int.t
  | Real of float 
  | Str of string
  | Lv of lv
  | Cast of typ * exp
  | BinOp of bop * exp * exp * einfo
  | UnOp of uop * exp * typ
  | True | False
  | ETypeName of elem_typ (* may be second arguments of abi.decode functions *)
  (* exists only in the interim process *)
  | IncTemp of exp * bool * loc (* true if prefix, false if postfix *)
  | DecTemp of exp * bool * loc
  | CallTemp of exp * exp list * einfo
  | CondTemp of exp * exp * exp * typ * loc
  | AssignTemp of lv * exp * loc

and bop =
  | Add | Sub | Mul | Div | Mod | Exponent
  | GEq | Gt | LEq | Lt | LAnd | LOr | Eq | NEq
  | ShiftL | ShiftR | BXor | BAnd | BOr

and uop =
  | Pos | Neg | LNot | BNot

and lv =
  | Var of (id * vinfo)
  | MemberAccess of exp * id * vinfo * typ (* exp.id / vinfo is for id *)
  | IndexAccess of exp * exp option * typ (* exp[exp?] *)
  | Tuple of exp option list * typ (* [a, b, c, d, ] *)

and id = string
and loc = int 

and cinfo = {
  numid : int;
  inherit_order : int list;
  lib_typ_lst : (id * typ) list; (* a list of pairs of (lib name, aliased type). Orders do not matter. *)
  ckind : string
}

and vinfo = {
  vloc : loc;
  is_gvar : bool;
  vtype : typ;
  vvis : visibility;
  vid : int;
  refid : int; (* referenced declartion. valid only for non-function variables *)
  storage : string; 
  flag : bool; (* true if the information is propagated *)
  org : string (* original name (source code) before renamed or replaced *)
}

and einfo = {
  eloc : loc; 
  etyp : typ;
  eid : int
}

and finfo = {
  is_constructor : bool;
  is_payable : bool;
  fvis : visibility;
  fid : int;
  scope : int; (* belonging contract numid *)
  scope_s : id; (* belonging contract name *)
  cfg : cfg
}

and cfg = {
  graph         : G.t;
  pre_set       : node BatSet.t; (* nodes just before loop headers *)
  lh_set        : node BatSet.t; (* loop header set *)
  lx_set        : node BatSet.t; (* loop exit set *)
  continue_set  : node BatSet.t;
  break_set     : node BatSet.t;
  basic_paths   : node list BatSet.t;
  stmt_map      : (node, stmt) BatMap.t;
  signature     : fkey
}

and typ =
  | ConstInt
  | ConstString
  | ConstReal
  | EType of elem_typ
  | Mapping of elem_typ * typ
  | Mapping2 of typ * typ
  | Array of typ * int option (* type, (size)? *)
  | Contract of id
  | Struct of id
  | Enum of id
  | TupleType of typ list
  | Void (* dummy type *)

and elem_typ =
  | Address
  | Bool
  | String
  | UInt of int
  | SInt of int
  | Bytes of int (* fixed-size byte arrays *)
  | DBytes (* dynamically-sized byte arrays *) 
  (* | Fixed | UFixed *)

let empty_cfg = {
  graph         = G.empty;
  pre_set       = BatSet.empty;
  lh_set        = BatSet.empty;
  lx_set        = BatSet.empty;
  continue_set  = BatSet.empty;
  break_set     = BatSet.empty;
  basic_paths   = BatSet.empty;
  stmt_map      = BatMap.empty;
  signature     = ("Dummy","Dummy",[])
}

let find_stmt : node -> cfg -> stmt
= fun n g -> 
  try if n = Node.ENTRY || n = Node.EXIT then Skip
      else BatMap.find n g.stmt_map
  with _ -> failwith ("No stmt found in the given node " ^ Node.to_string n)

let nodes_of : cfg -> node list
= fun g -> G.fold_vertex (fun x acc -> x::acc) g.graph []

let has_loop : cfg -> bool
= fun g -> not (BatSet.is_empty g.lh_set) (* inspect whether loop headers exist *)

let find_contract_id : pgm -> id -> contract
= fun contracts id ->
  List.find (fun (cid,_,_,_,_,_) -> BatString.equal cid id) contracts

let find_contract_nid : pgm -> int -> contract
= fun contracts nid ->
  List.find (fun (_,_,_,_,_,cinfo) -> nid = cinfo.numid) contracts

let get_main_contract : pgm -> contract
= fun pgm ->
  if BatString.equal !main_contract "" then BatList.last pgm
  else
    try find_contract_id pgm !main_contract
    with _ -> failwith ("main contract name mathcing failed : " ^ "\'"^ !main_contract ^ "\'")

let get_cname : contract -> id
= fun (cid,_,_,_,_,_) -> cid

let get_decls : contract -> state_var_decl list
= fun (_,decls,_,_,_,_) -> decls

let get_structs : contract -> structure list
= fun (_,_,structs,_,_,_) -> structs

let get_enums : contract -> enum list
= fun (_,_,_,enums,_,_) -> enums

let get_all_structs : pgm -> structure list
= fun pgm ->
  List.fold_left (fun acc c -> (get_structs c) @ acc) [] pgm 

let get_cnames : pgm -> id list
= fun pgm -> List.map get_cname pgm

let get_gvars : pgm -> var list
= fun p ->
  let main = get_main_contract p in
  let decls = get_decls main in
  List.map (fun (x,_,vinfo) -> (x,vinfo.vtype)) decls

let get_cinfo : contract -> cinfo
= fun (_,_,_,_,_,cinfo) -> cinfo

let get_libnames : pgm -> id list
= fun pgm ->
  let libs = List.filter (fun c -> BatString.equal (get_cinfo c).ckind "library") pgm in
  List.map get_cname libs

let get_numid : contract -> int
= fun (_,_,_,_,_,cinfo) -> cinfo.numid

let get_fname : func -> id (* detach this function *)
= fun (fname,_,_,_,_) -> fname

let get_funcs : contract -> func list
= fun (_,_,_,_,funcs,_) -> funcs

let get_fnames : contract -> id list
= fun (_,_,_,_,funcs,_) -> List.map get_fname funcs 

let get_cnstr : contract -> func
= fun (_,_,_,_,funcs,_) ->
  let lst = List.filter (fun (_,_,_,_,finfo) -> finfo.is_constructor) funcs in
  let _ = assert (List.length lst = 1) in
  List.hd lst

let gen_func ~fname ~params ~ret_params ~stmt ~finfo 
= (fname,params,ret_params,stmt,finfo) 

let update_cinfo : cinfo -> contract -> contract
= fun cinfo (cid,decls,structs,enums,funcs,_) -> (cid,decls,structs,enums,funcs,cinfo)

let update_enums : enum list -> contract -> contract
= fun enums (cid,decls,structs,_,funcs,cinfo) -> (cid,decls,structs,enums,funcs,cinfo)

let update_structs : structure list -> contract -> contract
= fun structs (cid,decls,_,enums,funcs,cinfo) -> (cid,decls,structs,enums,funcs,cinfo)

let update_funcs : func list -> contract -> contract
= fun funcs (cid,decls,structs,enums,_,cinfo) -> (cid,decls,structs,enums,funcs,cinfo)

let get_inherit_order : contract -> int list
= fun (_,_,_,_,_,cinfo) -> cinfo.inherit_order

let is_library : contract -> bool
= fun c -> BatString.equal (get_cinfo c).ckind "library"

let get_finfo : func -> finfo
= fun (_,_,_,_,finfo) -> finfo

let get_vis : func -> visibility 
= fun f -> (get_finfo f).fvis

let is_public = function 
  | Public -> true | _ -> false

let is_external = function
  | External -> true | _ -> false

let is_internal = function 
  | Internal -> true | _ -> false

let is_private = function
  | Private -> true | _ -> false

let is_public_func : func -> bool
= fun f -> is_public (get_vis f)

let is_external_func : func -> bool
= fun f -> is_external (get_vis f)

let is_internal_func : func -> bool
= fun f -> is_internal (get_vis f)

let is_private_func : func -> bool
= fun f -> is_private (get_vis f)

let update_finfo : finfo -> func -> func
= fun finfo (id,params,ret_params,stmt,_) -> (id,params,ret_params,stmt,finfo)

let is_constructor : func -> bool
= fun f -> (get_finfo f).is_constructor

let get_body : func -> stmt
= fun (_,_,_,stmt,_) -> stmt

let update_body : stmt -> func -> func
= fun stmt' (id,params,rets,stmt,finfo) -> (id, params, rets, stmt', finfo) 

let modify_contract : contract -> pgm -> pgm
= fun c p ->
  let cname = get_cname c in 
  List.map (fun c' -> 
    if BatString.equal cname (get_cname c') then c 
    else c'
  ) p

let get_cfg : func -> cfg
= fun func -> (get_finfo func).cfg

let update_cfg : func -> cfg -> func
= fun f g ->
  let finfo = get_finfo f in
  update_finfo {finfo with cfg = g} f

let is_outer_pred_of_lh : node -> cfg -> bool
= fun n g -> BatSet.mem n g.pre_set 

let is_loophead : node -> cfg -> bool
= fun n g -> BatSet.mem n g.lh_set

let is_loopexit : node -> cfg -> bool
= fun n g -> BatSet.mem n g.lx_set

let is_continue_node : node -> cfg -> bool
= fun n g -> BatSet.mem n g.continue_set

let is_break_node : node -> cfg -> bool
= fun n g -> BatSet.mem n g.break_set

let is_callnode : node -> cfg -> bool
= fun n g ->
  match find_stmt n g with
  | Call _ -> true
  | _ -> false

let is_skip_node : node -> cfg -> bool
= fun n g ->
  match find_stmt n g with
  | Skip -> true
  | _ -> false

let is_exception_node : node -> cfg -> bool
= fun n g ->
  match find_stmt n g with
  | Throw -> true
  | Call (lvop, Lv (Var ("revert",_)), args, _, _) -> true
  | _ -> false

let is_entry : node -> bool
= fun n ->
  match n with
  | Node.ENTRY -> true
  | _ -> false

let is_exit : node -> bool
= fun n ->
  match n with
  | Node.EXIT -> true
  | _ -> false

let is_uintkind : typ -> bool
= fun t ->
  match t with
  | EType UInt _ -> true
  | _ -> false

let is_uint256 t =
  match t with
  | EType (UInt 256) -> true
  | _ -> false

let is_sintkind : typ -> bool
= fun t ->
  match t with
  | EType SInt _ -> true
  | _ -> false

let is_mapping : typ -> bool
= fun t ->
  match t with
  | Mapping _ -> true
  | _ -> false

let is_usual_mapping : typ -> bool
= fun t ->
  match t with
  | Mapping (Address, EType (UInt 256)) -> true
  | _ -> false

let is_usual_allowance : typ -> bool
= fun t ->
  match t with
  | Mapping (Address, Mapping (Address, EType (UInt 256))) -> true
  | _ -> false

let is_bool : typ -> bool
= fun t ->
  match t with
  | EType Bool -> true
  | _ -> false

let is_address : typ -> bool
= fun t ->
  match t with
  | EType Address -> true
  | _ -> false

let is_array : typ -> bool
= fun t ->
  match t with
  | Array _ -> true
  | _ -> false

let is_static_array : typ -> bool
= fun t ->
  match t with
  | Array (_,Some _) -> true
  | _ -> false

let get_array_size : typ -> int option
= fun t ->
  match t with
  | Array (_,Some n) -> Some n
  | Array (_,None) -> None
  | _ -> raise (Failure "get_array_size")

let is_dynamic_array : typ -> bool
= fun t ->
  match t with
  | Array (_,None) -> true
  | _ -> false

let is_struct : typ -> bool
= fun t ->
  match t with
  | Struct _ -> true
  | _ -> false

let is_contract : typ -> bool
= fun t ->
  match t with
  | Contract _ -> true
  | _ -> false

let is_enum : typ -> bool
= fun t ->
  match t with
  | Enum _ -> true
  | _ -> false

let is_elemtyp : typ -> bool
= fun t ->
  match t with
  | EType _ -> true
  | _ -> false

let is_dbytes : typ -> bool
= fun t ->
  match t with
  | EType DBytes -> true
  | _ -> false

let is_bytes : typ -> bool
= fun t ->
  match t with
  | EType (Bytes _) -> true
  | _ -> false

let is_bytekind : typ -> bool
= fun t -> is_dbytes t || is_bytes t

let is_const_int : typ -> bool
= fun t ->
  match t with
  | ConstInt -> true
  | _ -> false

let is_uintkind_or_constint : typ -> bool
= fun t -> is_uintkind t || is_const_int t

let is_const_string : typ -> bool
= fun t ->
  match t with
  | ConstString -> true
  | _ -> false

let is_string : typ -> bool
= fun t ->
  match t with
  | EType String -> true
  | _ -> false

let is_tuple : typ -> bool
= fun t ->
  match t with
  | TupleType _ -> true
  | _ -> false

let domain_typ : typ -> typ
= fun typ -> 
  match typ with
  | Array _ -> EType (UInt 256) 
  | Mapping (et,_) -> EType et
  | Mapping2 (t,_) -> t
  | EType DBytes -> EType (UInt 256)
  | EType (Bytes _) -> EType (UInt 256)
  | _ -> failwith "domain_typ"

let range_typ : typ -> typ
= fun typ ->
  match typ with
  | Array (t,_) -> t
  | Mapping (_,t) -> t
  | Mapping2 (_,t) -> t
  | EType DBytes -> EType (Bytes 1) 
  | _ -> failwith "range_typ"

let unroll_tuple : typ -> typ list
= fun t ->
  match t with
  | TupleType lst -> lst
  | _ -> failwith "unroll_tuple"

let get_bytes_size : typ -> int
= fun t ->
  match t with
  | EType (Bytes n) -> n
  | _ -> failwith "get_bytes_size"

let exp_to_lv : exp -> lv
= fun exp ->
  match exp with
  | Lv lv -> lv
  | _ -> raise (Failure "exp_to_lv") 

let get_name_userdef : typ -> id
= fun t ->
  match t with
  | Struct s -> s
  | Enum s -> s
  | Contract s -> s
  | _ -> raise (Failure "get_name_userdef")

let get_type_var : var -> typ
= fun var -> snd var

let get_type_var2 : id * vinfo -> typ
= fun (v,vinfo) -> vinfo.vtype

let get_type_lv : lv -> typ
= fun lv ->
  match lv with
  | Var (_,vinfo) -> vinfo.vtype
  | MemberAccess (_,_,_,typ) -> typ 
  | IndexAccess (_,_,typ) -> typ 
  | Tuple (_, typ) -> typ

let get_type_exp : exp -> typ
= fun exp ->
  match exp with
  | Int _ -> ConstInt
  | Real _ -> ConstReal
  | Str _ -> ConstString
  | Lv lv -> get_type_lv lv 
  | Cast (typ,_) -> typ
  | BinOp (_,_,_,einfo) -> einfo.etyp
  | UnOp (_,_,typ) -> typ
  | True | False -> EType Bool
  | ETypeName etyp -> EType etyp
  | _ -> raise (Failure "get_type_exp")

let get_type_array_elem : typ -> typ
= fun typ ->
  match typ with
  | Array (t,_) -> t
  | _ -> raise (Failure "get_type_array_elem") 

let get_int : exp -> int
= fun exp ->
  match exp with
  | Int bigint -> BatBig_int.to_int bigint
  | _ -> failwith "get_int"

let get_bigint : exp -> BatBig_int.t
= fun exp ->
  match exp with
  | Int bigint -> bigint
  | _ -> failwith "get_bigint"

let big_lt = BatBig_int.lt_big_int
let big_neg = BatBig_int.neg
let big_ge = BatBig_int.ge_big_int
let big_pow n1 n2 = BatBig_int.pow (BatBig_int.of_int n1) (BatBig_int.of_int n2)

(* 0 <= X < 2^n *)
let rec bit_unsigned_of_int : BatBig_int.t -> int -> int 
= fun n bit ->
  let _ = assert (bit <= 256) in
  if big_lt n (big_pow 2 bit) then bit (* meaning EType (UInt bit) *)
  else bit_unsigned_of_int n (bit+8)

(* -2^(n-1) <= X < 2^(n-1) *)
let rec bit_signed_of_int : BatBig_int.t -> int -> int
= fun n bit ->
  let _ = assert (bit <= 256) in
  if big_ge n (big_neg (big_pow 2 (bit-1))) && big_lt n (big_pow 2 (bit-1)) then bit (* meaning EType (SInt bit) *)
  else bit_signed_of_int n (bit+8)

let dummy_vinfo = {vloc = -1; is_gvar = false; vtype = Void; vvis = Private; vid = -1; refid = -1; storage = ""; flag = false; org = ""} 
let dummy_vinfo_with_typ typ =
  {vloc = -1; is_gvar = false; vtype = typ; vvis = Private; vid = -1; refid = -1; storage = ""; flag = false; org = ""} 
let dummy_vinfo_with_typ_org typ org =
  {vloc = -1; is_gvar = false; vtype = typ; vvis = Private; vid = -1; refid = -1; storage = ""; flag = false; org = org}

let is_supported_mapping : typ -> bool
= fun typ ->
  match typ with
  | Mapping (Address, EType Address)
  | Mapping (Address, EType (UInt _))
  | Mapping (Address, EType Bool)
  | Mapping (UInt _, EType Address)
  | Mapping (UInt _, EType (UInt _))
  | Mapping (Address, Mapping (Address, EType (UInt _))) -> true
  | Mapping _ -> false
  | _ -> assert false

let get_init_stmt : lv -> int -> stmt
= fun lv loc ->
  match get_type_lv lv with
  | EType Address -> Assign (lv, Int BatBig_int.zero, loc)
  | EType Bool -> Assign (lv, False, loc)
  | EType String -> Assign (lv, Str "", loc)
  | EType (UInt _) -> Assign (lv, Int BatBig_int.zero, loc)
  | EType (SInt _) -> Assign (lv, Int BatBig_int.zero, loc)
  | EType (Bytes _) -> Assign (lv, Int BatBig_int.zero, loc)
  | EType DBytes -> Skip
  | Array _ -> Call (None, Lv (Var ("array_decl", dummy_vinfo)), [Lv lv], loc, -1)

  | Mapping (Address, EType Address)
  | Mapping (Address, EType (UInt _))
  | Mapping (Address, EType Bool)
  | Mapping (UInt _, EType Address)
  | Mapping (UInt _, EType (UInt _)) -> Call (None, Lv (Var ("mapping_init", dummy_vinfo)), [Lv lv], loc, -1)

  | Mapping (Address, Mapping (Address, EType (UInt _))) -> Call (None, Lv (Var ("mapping_init2", dummy_vinfo)), [Lv lv], loc, -1)
  | Contract id -> Assign (lv, Cast (Contract id, Int BatBig_int.zero), loc)
  | Mapping2 _ -> failwith "get_init_stmt - an expression of void type should not exist."
  | Void -> failwith "get_init_stmt - an expression of void type should not exist."
  | _ -> Call (None, Lv (Var ("dummy_init", dummy_vinfo)), [Lv lv], loc, -1)

let gvar_init = Call (None, Lv (Var ("GVar_Init", dummy_vinfo)), [], -1, -1)

let is_gvar_init stmt =
  match stmt with
  | Call (None, Lv (Var ("GVar_Init",_)), [], -1, -1) -> true
  | _ -> false

let is_skip stmt =
  match stmt with
  | Skip -> true
  | _ -> false

let get_body (_,_,_,stmt,_) = stmt
let get_params (_,params,_,_,_) = params
let get_param_types (_,params,_,_,_) = List.map (fun p -> (snd p).vtype) params 
let get_ret_params (_,_,ret_params,_,_) = ret_params
let get_ret_param_types (_,_,ret_params,_,_) = List.map (fun p -> (snd p).vtype) ret_params 
let get_fname (id,_,_,_,_) = id

let get_fsig : func -> id * typ list
= fun f -> (get_fname f, get_param_types f)

let equal_sig : func -> func -> bool
= fun f1 f2 ->
  let sig1 = get_fsig f1 in
  let sig2 = get_fsig f2 in
  try sig1 = sig2 with Invalid_argument s -> false

let get_fkey : func -> id * id * typ list
= fun f -> ((get_finfo f).scope_s, get_fname f, get_param_types f)

let get_func_decl : func -> func_decl 
= fun (fname,params,ret_params,_,_) ->
  (fname, List.map (fun (x,xinfo) -> (x,xinfo.vtype)) params, List.map (fun (x,xinfo) -> (x,xinfo.vtype)) ret_params)

let get_all_fkeys_c : contract -> fkey BatSet.t
= fun c ->
  let funcs = get_funcs c in
  BatSet.of_list (List.map get_fkey funcs)

let get_all_fkeys : pgm -> fkey BatSet.t
= fun p ->
  List.fold_left (fun acc c ->
    BatSet.union (get_all_fkeys_c c) acc
  ) BatSet.empty p

(******************************)
(******************************)
(***** Tostring Functions *****)
(******************************)
(******************************)

let rec to_string_exp ?(report=false) exp =
  match exp with
  | Int n -> BatBig_int.to_string n
  | Real n -> string_of_float n
  | Str s -> "\"" ^ (BatString.nreplace s "\n" "") ^ "\""
  | Lv lv -> to_string_lv ~report lv
  | Cast (typ,e) -> to_string_typ typ ^ "(" ^ to_string_exp ~report e ^ ")"
  | BinOp (bop,e1,e2,_) -> "(" ^ to_string_exp ~report e1 ^ " " ^ to_string_bop bop ^ " " ^ to_string_exp ~report e2 ^ ")"
  | UnOp (uop,e,_) -> "(" ^ to_string_uop uop ^ to_string_exp ~report e ^ ")" 
  | True -> "true"
  | False -> "false"
  | ETypeName etyp -> to_string_etyp etyp
  | IncTemp (e,prefix,_) -> if prefix then "++" ^ to_string_exp e else to_string_exp e ^ "++" 
  | DecTemp (e,prefix,_) -> if prefix then "--" ^ to_string_exp e else to_string_exp e ^ "--" 
  | CondTemp (e1,e2,e3,_,_) -> "(" ^ to_string_exp e1 ^ " ? " ^ to_string_exp e2 ^ " : " ^ to_string_exp e3 ^ ")"
  | AssignTemp (lv,e,_) -> "(" ^ to_string_lv lv ^ " = " ^ to_string_exp e ^ ")"
  | CallTemp (e,params,_) ->
    to_string_exp e ^ string_of_list ~first:"(" ~last:")" ~sep:", " to_string_exp params 

and to_string_exp_opt exp =
  match exp with
  | Some e -> to_string_exp e
  | None -> " "

and to_string_bop bop =
  match bop with
  | Add -> "+" | Sub -> "-" 
  | Mul -> "*" | Div -> "/" 
  | Mod -> "%" | Exponent -> "**"
  | GEq -> ">=" | Gt -> ">"  
  | LEq -> "<=" | Lt -> "<"
  | LAnd -> "&&" | LOr -> "||"
  | Eq -> "==" | NEq -> "!="
  | ShiftL -> "<<" | ShiftR -> ">>" 
  | BXor -> "^" | BAnd -> "&" 
  | BOr -> "|"

and to_string_uop uop =
  match uop with
  | Pos -> "+"
  | Neg -> "-"
  | LNot -> "!"
  | BNot -> "~"

and to_string_lv ?(report=false) lv =
  match lv with
  | Var (x,xinfo) ->
    if not report then x else xinfo.org
  | MemberAccess (e,x,xinfo,_) -> to_string_exp ~report e ^ "." ^ (if not report then x else xinfo.org)
  | IndexAccess (e,None,_) -> to_string_exp ~report e ^ "[]"
  | IndexAccess (e1,Some e2,_) -> to_string_exp ~report e1 ^ "[" ^ to_string_exp ~report e2 ^ "]"
  | Tuple (elst, t) -> 
    if is_array t then string_of_list ~first:"[" ~last:"]" ~sep:", " to_string_exp_opt elst
    else string_of_list ~first:"(" ~last:")" ~sep:", " to_string_exp_opt elst

and to_string_typ typ =
  match typ with
  | ConstInt -> "int_const"
  | ConstReal -> "rational_const"
  | ConstString -> "literal_string"
  | EType etyp -> to_string_etyp etyp
  | Mapping (etyp,typ) -> "mapping" ^ "(" ^ to_string_etyp etyp ^ "=>" ^ to_string_typ typ ^ ")"
  | Mapping2 (t1,t2) -> "mapping2" ^ "(" ^ to_string_typ t1 ^ "=>" ^ to_string_typ t2 ^ ")"
  | Array (typ,None) -> to_string_typ typ ^ "[]"
  | Array (typ,Some n) -> to_string_typ typ ^ "[" ^ string_of_int n ^ "]"
  | Void -> "void"
  (* | UserDef s -> "UserDefinedType" ^ "-" ^ s *)
  | Contract id -> "Contract:" ^ id
  | Struct id -> "Struct:" ^ id
  | Enum id -> "Enum:" ^ id
  | TupleType typs -> "Tuple" ^ string_of_list ~first:"(" ~last:")" ~sep:", " to_string_typ typs

and to_string_etyp elem_typ =
  match elem_typ with
  | Address -> "address"
  | Bool -> "bool"
  | String -> "string"
  | UInt n -> "uint" ^ string_of_int n
  | SInt n -> "sint" ^ string_of_int n
  | Bytes n -> "bytes" ^ string_of_int n
  | DBytes -> "dbytes" (* dynamically-sized byte array *)
  (* | Fixed -> "fixed"
  | UFixed -> "ufixed" *)

let rec to_string_stmt ?(report=false) stmt =
  match stmt with
  | Assign (lv,e,_) -> to_string_lv ~report lv ^ " = " ^ to_string_exp ~report e ^ ";"
  | Decl (Var (id,vinfo)) -> to_string_typ vinfo.vtype ^ " " ^ id ^ ";"
  | Decl _ -> raise (Failure "invalid declaration")
  | Seq (s1,s2) -> to_string_stmt ~report s1 ^ "" ^ "\n" ^ "    " ^ to_string_stmt ~report s2 
  | Call (None, e, exps, _, _) ->
    to_string_exp ~report e ^ string_of_list ~first:"(" ~last:")" ~sep:", " (to_string_exp ~report) exps ^ ";"
  | Call (Some lv, e, exps, _, _) ->
    if report && BatString.starts_with (to_string_lv lv) "Tmp" then
      to_string_lv ~report lv
    else 
      to_string_lv ~report lv ^ " = " ^ to_string_exp ~report e ^ 
      string_of_list ~first:"(" ~last:")" ~sep:", " (to_string_exp ~report) exps ^ ";"
  | Skip -> "skip;"
  | If (e,s1,s2) ->
    "if" ^ "(" ^ to_string_exp ~report e ^ ")" ^ "{" ^ to_string_stmt ~report s1 ^ "}" ^ " " ^
    "else" ^ "{" ^ to_string_stmt ~report s2 ^ "}" 
  | While (e,s) -> "while" ^ "(" ^ to_string_exp ~report e ^ ")" ^ "{" ^ to_string_stmt ~report s ^ "}"
  | Break -> "break;"
  | Continue -> "continue;"
  | Return (None,_) -> "return;"
  | Return (Some e,_) -> "return " ^ to_string_exp ~report e ^ ";"
  | Throw -> "throw;"
  | Assume (e,_) -> "assume" ^ "(" ^ to_string_exp ~report e ^ ")" ^ ";"
  | Assert (e,_) -> "assert" ^ "(" ^ to_string_exp ~report e ^ ")" ^ ";"
  | Assembly (lst,_) ->
    "assembly" ^ string_of_list ~first:"{" ~last:"}" ~sep:", " (fst|>id) lst ^ ";"

let rec to_string_func (id,params,ret_params,stmt,finfo) =
  "function" ^ " " ^ id ^ " " ^ (string_of_list ~first:"(" ~last:")" ~sep:", " to_string_param params) ^
  " " ^ "returns" ^ " " ^ (string_of_list ~first:"(" ~last:")" ~sep:", " to_string_param ret_params) ^
  " " ^ to_string_vis finfo.fvis ^ " " ^ "{" ^ "\n" ^
  "    " ^ to_string_stmt stmt ^ "\n" ^ "  " ^ "}" ^ "\n"
 
and to_string_param (id,vinfo) = to_string_typ vinfo.vtype ^ " " ^ id

and to_string_vis vis =
 match vis with
 | Public -> "public"
 | Internal -> "internal"
 | External -> "external"
 | Private -> "private"

let to_string_state_var_decl decl =
  match decl with
  | (id,None,vinfo) -> to_string_typ vinfo.vtype ^ " " ^ id ^ ";"
  | (id,Some e,vinfo) -> to_string_typ vinfo.vtype ^ " " ^ id ^ " = " ^ to_string_exp e ^ ";" 

let to_string_var_decl = to_string_param

let to_string_structure (id,decls) =
  "struct" ^ " " ^ id ^ "{" ^ "\n" ^
  (string_of_list ~first:"    " ~last:";" ~sep:";\n    " to_string_var_decl decls) ^
  "\n" ^ "  " ^ "}" ^ "\n"

let to_string_enum (id,mems) =
  "enum" ^ " " ^ id ^ (string_of_list ~first:" {" ~last:"}" ~sep:", " Vocab.id mems)

let to_string_contract (id, decls, structs, enums, func_defs, _) =
  "contract" ^ " " ^ id ^ "{" ^ "\n" ^
  (if decls = [] then ""  
   else string_of_list ~first:"  " ~last:"\n\n" ~sep:"\n  " to_string_state_var_decl decls) ^
  (if structs = [] then ""
   else string_of_list ~first:"  " ~last:"\n\n" ~sep:"\n  " to_string_structure structs) ^
  (if enums = [] then ""
   else string_of_list ~first:"  " ~last:"\n\n" ~sep:"\n  " to_string_enum enums) ^
  string_of_list ~first:"  " ~last:"\n" ~sep:"\n  " to_string_func func_defs ^ "}"

let to_string_pgm contracts =
  string_of_list ~first:"" ~last:"" ~sep:"\n\n" to_string_contract contracts

let to_string_fsig (fname,typs) =
  fname ^ ", " ^ (string_of_list ~first:"{" ~last:"}" ~sep:", " to_string_typ typs)

let to_string_fkey (cname,fname,typs) =
  "\"" ^
  "(" ^ cname ^ ", " ^ fname ^ ", " ^ (string_of_list ~first:"[" ~last:"]" ~sep:", " to_string_typ typs) ^ ")" ^
  "\""

let to_string_cfg ?(name="G") : cfg -> string
= fun cfg ->
  "digraph " ^ name ^ "{" ^ "\n" ^
  "{" ^ "\n" ^
  "node [shape=box]" ^ "\n" ^
  G.fold_vertex (fun v acc ->
    let str_v = Node.to_string v in
    let stmt = to_string_stmt (find_stmt v cfg) in
    let colored = 
      if is_loophead v cfg then " style=filled color=grey shape=oval" else
      if is_loopexit v cfg then " style=filled color=grey shape=diamond" else
      if is_callnode v cfg then " style=filled color=yellow" 
      else ""
    in
    acc ^ str_v ^ " [label=\"" ^ str_v ^ ": " ^ stmt ^ "\"" ^ colored ^ "]" ^ "\n"
  ) cfg.graph ""
  ^
  "}" ^ "\n" ^
  G.fold_edges (fun v1 v2 acc ->
    acc ^ Node.to_string v1 ^ " -> " ^ Node.to_string v2 ^ "\n"
  ) cfg.graph ""
  ^
  "}" ^ "\n\n"

let to_string_cfg_f : func -> string
= fun func -> to_string_cfg ~name:(get_fname func) (get_cfg func)

let to_string_cfg_c : contract -> string
= fun contract ->
  List.fold_left (fun acc f ->
    acc ^ to_string_cfg_f f
  ) "" (get_funcs contract)

let to_string_cfg_p : pgm -> string
= fun p ->
  List.fold_left (fun acc c ->
    acc ^ to_string_cfg_c c
  ) "" p

let to_string_path : node list -> string
= fun path -> string_of_list ~first:"[" ~last:"]" ~sep:"->" Node.to_string path

let to_string_paths : node list BatSet.t -> string
= fun paths -> string_of_set ~first:"{" ~last:"}" ~sep:",\n" to_string_path paths

let print_path : node list -> unit
= fun path -> print_endline (to_string_path path)

let print_paths : node list BatSet.t -> unit
= fun paths -> print_endline (to_string_paths paths) 

(******************************)
(******************************)
(***** Built-in Functions *****)
(******************************)
(******************************)

let is_require exp =
  match exp with
  | Lv (Var ("require",_)) -> true
  | _ -> false

let is_assert exp =
  match exp with
  | Lv (Var ("assert",_)) -> true
  | _ -> false

let is_revert exp =
  match exp with
  | Lv (Var ("revert",_)) -> true
  | _ -> false

(***********************)
(***********************)
(***** Other Utils *****)
(***********************)
(***********************)

let rec replace_exp : exp -> exp -> exp -> exp 
= fun exp target replacement ->
  match exp with
  | Int _ | Real _ | Str _ -> exp
  | Lv lv when exp = target -> replacement
  | Lv lv -> exp
  | Cast (typ,e) -> Cast (typ, replace_exp e target replacement) 
  | BinOp (bop,e1,e2,einfo) -> BinOp (bop, replace_exp e1 target replacement, replace_exp e2 target replacement, einfo)
  | UnOp (uop,e,typ) -> UnOp (uop, replace_exp e target replacement, typ) 
  | True | False -> exp
  | ETypeName _ -> exp 
  | AssignTemp _ 
  | CondTemp _
  | IncTemp _ 
  | DecTemp _
  | CallTemp _ -> raise (Failure "replace_exp")

let equal_typ : typ -> typ -> bool
= fun t1 t2 -> t1 = t2

exception NoParameters

let params_to_lv params =
  if (List.length params = 1) then
    let (x,vinfo) = List.hd params in
    Var (x,vinfo) else 
  if (List.length params > 1) then
    let eops = List.map (fun (x,vinfo) -> Some (Lv (Var (x,vinfo)))) params in
    let tuple_typ = TupleType (List.map (fun (_,vinfo) -> vinfo.vtype) params) in
    Tuple (eops,tuple_typ)
  else
    raise NoParameters

let args_to_exp : exp list -> exp
= fun args ->
  if (List.length args = 1) then
    List.hd args else
  if (List.length args > 1) then
    let eops = List.map (fun e -> Some e) args in
    let tuple_typ = TupleType (List.map get_type_exp args) in
    Lv (Tuple (eops,tuple_typ))
  else
    raise NoParameters

let is_static_call : id list -> stmt -> bool
= fun cnames stmt ->
  match stmt with
  | Call (_,Lv (Var (f,_)),_,_,_) -> true
  | Call (_,Lv (MemberAccess (Lv (Var (x,_)),_,_,_)),_,_,_) when List.mem x cnames -> true
  | Call _ -> false
  | _ -> failwith "is_static_call"

let keyword_vars =
  ["block.coinbase"; "block.difficulty"; "block.gaslimit"; 
   "block.number"; "block.timestamp"; "now";
   "msg.data"; "msg.data.length"; "msg.sender"; "msg.value"; "msg.gas"; "msg.sig";
   "this";
   "tx.gasprice"; "tx.origin"]

let blk_keyword_vars =
  ["block.coinbase"; "block.difficulty"; "block.gaslimit"; 
   "block.number"; "block.timestamp"; "now"]

let is_balance_keyword lv =
  match lv with
  | MemberAccess (e,id,_,_)
    when (is_address (get_type_exp e) || is_contract (get_type_exp e))
         && BatString.equal id "balance"
    -> true
  | _ -> false

let init_funcs = ["array_init"; "array_decl"; "dbytes_init"; "string_init"; "contract_init"; "struct_init"; "struct_init2"; "mapping_init"; "mapping_init2"; "dummy_init"]

let built_in_funcs =
  ["abi.encode"; "abi.decode"; "abi.encodePacked"; "abi.encodeWithSignature"; "abi.encodeWithSelector";
   "revert"; "keccak256"; "sha3"; "sha256"; "ripemd160"; "delete"; 
   "selfdestruct"; "suicide"; "ecrecover"; "addmod";
   "blockhash"; "block.blockhash"]

let max_256bit =
  let pow = BatBig_int.pow (BatBig_int.of_string "2") (BatBig_int.of_string "256") in
  let one = BatBig_int.of_string "1" in
  BatBig_int.sub pow one

let rec var_lv : lv -> var BatSet.t
= fun lv ->
  match lv with
  | Var (x,xinfo) -> BatSet.singleton (x,xinfo.vtype)
  | MemberAccess (e,x,xinfo,_) -> BatSet.add (x,xinfo.vtype) (var_exp e)
  | IndexAccess (e1,Some e2,_) -> BatSet.union (var_exp e1) (var_exp e2)
  | IndexAccess (e,None,_) -> var_exp e
  | Tuple (eops,_) ->
    List.fold_left (fun acc eop ->
      match eop with
      | None -> acc
      | Some e -> BatSet.union (var_exp e) acc
    ) BatSet.empty eops

and var_exp : exp -> var BatSet.t
= fun exp ->
  match exp with
  | Int _ | Real _ | Str _ -> BatSet.empty
  | Lv lv ->
    if List.mem (to_string_lv lv) keyword_vars then
      BatSet.singleton (to_string_lv lv, get_type_lv lv)
    else var_lv lv
  | Cast (_,e) -> var_exp e
  | BinOp (_,e1,e2,_) -> BatSet.union (var_exp e1) (var_exp e2)
  | UnOp (_,e,_) -> var_exp e
  | True | False -> BatSet.empty
  | ETypeName _ -> BatSet.empty
  | _ -> failwith "var_exp: temp expressions encountered"

module OrderedType = struct
  type t = BatBig_int.t
  let compare = BatBig_int.compare
end

module BigIntSet = BatSet.Make (OrderedType)

let rec int_lv : lv -> BigIntSet.t
= fun lv ->
  match lv with
  | Var _ -> BigIntSet.empty
  | MemberAccess (e,_,_,_) -> int_exp e
  | IndexAccess (e1,Some e2,_) -> BigIntSet.union (int_exp e1) (int_exp e2)
  | IndexAccess (e,None,_) -> int_exp e
  | Tuple (eops,_) ->
    List.fold_left (fun acc eop ->
      match eop with
      | None -> acc
      | Some e -> BigIntSet.union (int_exp e) acc
    ) BigIntSet.empty eops

and int_exp : exp -> BigIntSet.t
= fun exp ->
  match exp with
  | Int n -> BigIntSet.singleton n
  | Real _ | Str _ -> BigIntSet.empty
  | Lv lv -> int_lv lv
  | Cast (_,e) -> int_exp e
  | BinOp (_,e1,e2,_) -> BigIntSet.union (int_exp e1) (int_exp e2)
  | UnOp (_,e,_) -> int_exp e
  | True | False -> BigIntSet.empty
  | ETypeName _ -> BigIntSet.empty
  | _ -> failwith "int_exp: temp expressions encountered"


let preceding_typ : typ -> typ -> typ
= fun t1 t2 ->
  if t1=t2 then t1
  else
   (match t1,t2 with
    | EType String, ConstString -> t1
    | EType (UInt n1), EType (UInt n2) -> EType (UInt (max n1 n2))
    | EType (SInt n1), EType (SInt n2) -> EType (SInt (max n1 n2))
    | EType (SInt n1), EType (UInt n2) when n1>n2 -> t1
    | EType (SInt n1), EType (UInt n2) when n1<=n2 -> raise (Failure "preceding_typ : intX1 and uintX2 are not convertible if X1<=X2")
    | EType (UInt n1), EType (SInt n2) when n1<n2 -> t2
    | EType (UInt n1), EType (SInt n2) when n1>=n2 -> t1
    | ConstInt, EType Address -> t2
    | EType Address, ConstInt -> t1
    | Contract s, ConstInt -> t1 
    | EType Address, Contract s -> t1
    | Contract s, EType Address -> t2
    | EType Bytes _, ConstInt -> t1
    | Array (t1,None), Array (t2, Some n) when t1=t2 -> Array (t1,None)
    | Contract id1, Contract id2 -> t2
    | ConstString, EType Bytes _ -> t2
    | ConstString, EType DBytes -> t2
    | EType Bytes _, ConstString -> t1
    | EType DBytes, ConstString -> t1
    | t1,t2 -> raise (Failure ("preceding_typ : " ^ (to_string_typ t1) ^ " vs. " ^ (to_string_typ t2))))

(* currently, casting is performed in the vc generation step. *)
let rec folding : exp -> exp
= fun exp ->
  match exp with
  | Int n -> Int n
  | BinOp (Add,Int n1,Int n2,einfo) -> Int (BatBig_int.add n1 n2)
  | BinOp (Sub,Int n1,Int n2,einfo) -> Int (BatBig_int.sub n1 n2)
  | BinOp (Mul,Int n1,Int n2,einfo) -> Int (BatBig_int.mul n1 n2)
  | BinOp (Div,Int n1,Int n2,einfo) -> Int (BatBig_int.div n1 n2)
  | BinOp (Mod,Int n1,Int n2,einfo) -> Int (BatBig_int.modulo n1 n2)
  | BinOp (Exponent,Int n1,Int n2,einfo) -> Int (BatBig_int.pow n1 n2)
  | BinOp (bop,e1,e2,einfo) -> BinOp (bop, folding e1, folding e2, einfo) 
  | _ -> failwith "folding"

let rec constant_folding : exp -> exp
= fun exp ->
  let exp' = folding exp in
  if BatString.equal (to_string_exp exp) (to_string_exp exp') then exp'
  else constant_folding exp'

let common_typ : exp -> exp -> typ 
= fun e1 e2 ->
  let t1,t2 = get_type_exp e1, get_type_exp e2 in
  if t1=t2 then t1 
  else
   (match t1,t2 with
    | ConstInt, EType (UInt n) ->
      let n' = bit_unsigned_of_int (get_bigint (constant_folding e1)) 8 in
      EType (UInt (max n n'))
    | EType (UInt n), ConstInt ->
      let n' = bit_unsigned_of_int (get_bigint (constant_folding e2)) 8 in
      EType (UInt (max n n'))
    | ConstInt, EType (SInt n) ->
      let n' = bit_signed_of_int (get_bigint (constant_folding e1)) 8 in
      EType (SInt (max n n'))
    | EType (SInt n), ConstInt ->
      let n' = bit_signed_of_int (get_bigint (constant_folding e2)) 8 in
      EType (SInt (max n n'))
    | _ -> preceding_typ t1 t2)


let mk_einfo : typ -> einfo
= fun t -> {eloc=(-1); etyp=t; eid=(-1)}

let mk_finfo : contract -> finfo
= fun c ->
  {is_constructor = false;
   is_payable = false;
   fvis = Public;
   fid = (-1);
   scope = (get_cinfo c).numid;
   scope_s = get_cname c;
   cfg = empty_cfg}

let mk_access : exp -> exp -> exp
= fun e1 e2 ->
  let _ = assert (is_usual_mapping (get_type_exp e1) || is_usual_allowance (get_type_exp e1)) in
  let _ = assert (is_address (get_type_exp e2)) in
  Lv (IndexAccess (e1, Some e2, range_typ (get_type_exp e1)))

let mk_eq : exp -> exp -> exp
= fun e1 e2 -> BinOp (Eq, e1, e2, mk_einfo (EType Bool))

let mk_neq : exp -> exp -> exp
= fun e1 e2 -> BinOp (NEq, e1, e2, mk_einfo (EType Bool)) 

let mk_ge : exp -> exp -> exp
= fun e1 e2 -> BinOp (GEq, e1, e2, mk_einfo (EType Bool))

let mk_and : exp -> exp -> exp
= fun e1 e2 ->
  let _ = assert (is_bool (get_type_exp e1)) in
  let _ = assert (is_bool (get_type_exp e2)) in
  BinOp (LAnd, e1, e2, mk_einfo (EType Bool))

let mk_or : exp -> exp -> exp
= fun e1 e2 ->
  let _ = assert (is_bool (get_type_exp e1)) in
  let _ = assert (is_bool (get_type_exp e2)) in
  BinOp (LOr, e1, e2, mk_einfo (EType Bool))

let mk_plus : exp -> exp -> exp
= fun e1 e2 -> BinOp (Add, e1, e2, mk_einfo (common_typ e1 e2))
