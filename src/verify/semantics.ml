open Lang
open Vlang
open Vocab
open Report
open Global
open ItvDom
open Query

(**************************)
(**************************)
(**** Helper functions ****)
(**************************)
(**************************)

let rid = ref 0 (* rename id *)
let fresh_rid () = rid:=!rid+1; !rid

let rename : vexp -> vexp
= fun vexp ->  
  match vexp with
  | VVar (vid,typ) -> 
    let vid' = vid ^ "(" ^ "#" ^ string_of_int (fresh_rid ()) ^ ")"
    in VVar (vid',typ)
  | _ -> raise (Failure "rename")

let is_renamed : vid -> bool
= fun x -> BatString.exists x "#"

let weaken_vf2 : vformula -> vid list -> vformula
= fun vf targets ->
  List.fold_left weaken_vf vf targets

let rec get_target : lv -> vexp
= fun lv ->
  match lv with
  | Var (id,vinfo) -> VVar (id, vinfo.vtype)
  | MemberAccess (e,x,xinfo,_) ->
    VVar (x, Mapping2 (get_type_exp e, xinfo.vtype))
  | IndexAccess (Lv lv,_,_) -> get_target lv
  | _ -> raise (Failure ("semantics (get_target) : " ^ to_string_lv lv))

let rec recur : vexp -> vexp
= fun ve ->
  match ve with
  | Write (VVar _,_,_) -> ve
  | Write (Read (ve1,ve2,_),idx,e) -> recur (Write (ve1,ve2,ve))
  | _ -> raise (Failure "recur")

let rec include_byte_exp : exp -> bool
= fun e ->
  match e with
  | Int _ -> false
  | Str _ -> false
  | Real _ -> false
  | Lv lv -> is_bytekind (get_type_lv lv)
  | Cast (t,e) -> is_bytekind t || include_byte_exp e
  | BinOp (_,e1,e2,einfo) -> is_bytekind einfo.etyp || include_byte_exp e1 || include_byte_exp e2
  | UnOp (_,e,t) -> is_bytekind t || include_byte_exp e
  | True | False -> false
  | _ -> failwith "include_byte_exp : tmp expressions should not exist"

(***********************)
(***********************)
(**** SP Generation ****)
(***********************)
(***********************)

let rec convert_aexp : exp -> vexp
= fun exp ->
  match exp with
  | Int n -> VInt n
  | Str s -> VVar ("@"^s, ConstString)
  | Real _ -> failwith "convert_aexp : rational literal"
  | Lv lv ->
    let s = to_string_lv lv in
    if List.mem s Lang.keyword_vars then VVar (s, get_type_lv lv)
    else convert_lv lv
  | Cast (EType Address, Lv (Var ("this",_))) -> VVar this_addr
  | Cast (typ,e) -> (* specifics are handled in z3Interface. *)
    VCast (typ, convert_aexp e)
  | True -> VCond VTrue
  | False -> VCond VFalse
  | UnOp (uop,e,typ) -> 
    (match uop with
     | Neg -> VUnOp (VNeg, convert_aexp e, typ)
     | BNot -> VUnOp (VBNot, convert_aexp e, typ)
     | LNot -> VCond (VNot (convert_bexp e)) 
     | _ -> failwith ("convert_aexp: UnOP - " ^ to_string_exp exp))
  | BinOp (bop,e1,e2,einfo) ->
    let typ = get_type_exp exp in
    let ve1 = convert_aexp e1 in
    let ve2 = convert_aexp e2 in
    (match bop with
     | Add -> VBinOp (VAdd,ve1,ve2,typ)
     | Sub -> VBinOp (VSub,ve1,ve2,typ)
     | Mul -> VBinOp (VMul,ve1,ve2,typ)
     | Div -> VBinOp (VDiv,ve1,ve2,typ)
     | Mod -> VBinOp (VMod,ve1,ve2,typ) 
     | Exponent -> VBinOp (VPower,ve1,ve2,typ)
     | ShiftL ->
       if is_bytekind typ then VVar (gen_newsym typ)
       else VBinOp (VShiftL,ve1,ve2,typ) 
     | ShiftR ->
       if is_bytekind typ then VVar (gen_newsym typ)
       else VBinOp (VShiftR,ve1,ve2,typ)
     | BAnd ->
       if is_bytekind typ then VVar (gen_newsym typ)
       else VBinOp (VBAnd,ve1,ve2,typ)
     | BOr ->
       if is_bytekind typ then VVar (gen_newsym typ)
       else VBinOp (VBOr,ve1,ve2,typ)
     | BXor ->
       if is_bytekind typ then VVar (gen_newsym typ)
       else VBinOp (VBXor,ve1,ve2,typ)
     | GEq -> VCond (VBinRel (VGeq, convert_aexp e1, convert_aexp e2))
     | Gt -> VCond (VBinRel (VGt, convert_aexp e1, convert_aexp e2))
     | LEq -> VCond (VBinRel (VGeq, convert_aexp e2, convert_aexp e1)) 
     | Lt -> VCond (VBinRel (VGt, convert_aexp e2, convert_aexp e1)) 
     | Eq -> VCond (VBinRel (VEq, convert_aexp e1, convert_aexp e2))
     | NEq -> VCond (VNot (VBinRel (VEq, convert_aexp e1, convert_aexp e2)))
     | LAnd -> VCond (VAnd (convert_bexp e1, convert_bexp e2))
     | LOr -> VCond (VOr (convert_bexp e1, convert_bexp e2)))
  | _ -> failwith "convert_aexp : tmp expressions should not exist"

and convert_lv : lv -> vexp
= fun lv ->
  let typ = get_type_lv lv in
  match lv with
  | Var (x,_) -> VVar (x,typ)
  | IndexAccess (e,Some _,EType (Bytes 1))
    when get_type_exp e = EType (Bytes 1) -> convert_aexp e
  | IndexAccess (e1,Some e2,t) -> Read (convert_aexp e1, convert_aexp e2, typ)
  | IndexAccess (e,None,_) -> raise (Failure "convert_lv - IndexAccess")
  | MemberAccess (e,"balance",_,_) ->
    Read (VVar eth_map, convert_aexp e, EType (UInt 256))
  | MemberAccess (e,"length",_,_) when is_array (get_type_exp e) ->
    Read (VVar (length_map, Mapping2 (get_type_exp e, typ)), convert_aexp e, typ)
  | MemberAccess (_,"selector",_,_) -> VVar (to_string_lv lv,typ) (* typ: bytes4 *)
  | MemberAccess (e,x,xinfo,etyp) when is_enum typ && BatString.exists x "__idx" ->
    let (_,idx) = BatString.split x "__idx" in
    VCast (typ, VInt (BatBig_int.of_int (int_of_string idx)))
  | MemberAccess (e,x,xinfo,etyp) ->
    Read (VVar (x, Mapping2 (get_type_exp e, xinfo.vtype)), convert_aexp e, xinfo.vtype)
  | Tuple _ -> raise (Failure ("convert_lv - Tuple : " ^ (to_string_lv lv))) (* handled in assignment level *)

and convert_bexp : exp -> vformula 
= fun exp -> 
  match exp with
  | True -> VTrue
  | False -> VFalse
  | Lv lv -> convert_bexp_lv lv
  | BinOp (bop,e1,e2,einfo) ->
    (match bop with
     | GEq ->
       if include_byte_exp exp then VTrue
       else VBinRel (VGeq, convert_aexp e1, convert_aexp e2)
     | Gt ->
       if include_byte_exp exp then VTrue
       else VBinRel (VGt, convert_aexp e1, convert_aexp e2)
     | LEq ->
       if include_byte_exp exp then VTrue
       else VBinRel (VGeq, convert_aexp e2, convert_aexp e1)
     | Lt ->
       if include_byte_exp exp then VTrue
       else VBinRel (VGt, convert_aexp e2, convert_aexp e1)
     | Eq ->
       if include_byte_exp exp then VTrue
       else VBinRel (VEq, convert_aexp e1, convert_aexp e2)
     | NEq ->
       if include_byte_exp exp then VTrue
       else VNot (VBinRel (VEq, convert_aexp e1, convert_aexp e2))
     | LAnd -> VAnd (convert_bexp e1, convert_bexp e2)
     | LOr -> VOr (convert_bexp e1, convert_bexp e2)
     | _ -> raise (Failure ("convert_bexp1 - " ^ to_string_exp exp)))
  | UnOp (uop,e,typ) ->
    (match uop with
     | LNot ->
       if include_byte_exp exp then VTrue
       else VNot (convert_bexp e)
     | _ -> raise (Failure ("convert_bexp2 - " ^ to_string_exp exp)))
  | _ -> raise (Failure ("convert_bexp3 - " ^ to_string_exp exp))

and convert_bexp_lv : lv -> vformula
= fun lv ->
  let _ = assert (is_bool (get_type_lv lv)) in
  VBinRel (VEq, convert_lv lv, VCond VTrue)

let rewrite_q : query -> vexp -> vexp -> query
= fun q target replacement -> {q with vc2 = rewrite_vf q.vc2 target replacement}

let rec assign (lv,e) (vf,qs) =
  let lv_typ = get_type_lv lv in
  match lv,e with
  | _, Lv (Tuple (eops,_)) when is_array lv_typ ->
    BatList.fold_lefti (fun (acc_vf,acc_qs) i eop ->
      match eop with
      | Some e ->
        let t = get_type_array_elem lv_typ in (* type of "lv[i]" *)
        assign (IndexAccess (Lv lv,Some (Int (BatBig_int.of_int i)),t), e) (acc_vf,acc_qs)
      | None -> (acc_vf,acc_qs)
    ) (vf,qs) eops
  | Var _, e ->
    let target = get_target lv in
    let replacement = rename target in
    let vf' = rewrite_vf vf target replacement in
    let ve' = rewrite_ve (convert_aexp e) target replacement in
    (VAnd (vf', Label (0, VBinRel (VEq,target,ve'))),
     List.map (fun q -> rewrite_q q target replacement) qs)
  | IndexAccess (arr, Some idx, t), e -> 
    let target = get_target lv in
    let replacement = rename target in
    let vf' = rewrite_vf vf target replacement in
    let ve = recur (Write (convert_aexp arr, convert_aexp idx, convert_aexp e)) in
    let ve' = rewrite_ve ve target replacement in
    (VAnd (vf', Label (0, VBinRel (VEq,target,ve'))),
     List.map (fun q -> rewrite_q q target replacement) qs)
  | MemberAccess (e1,x,xinfo,t), e2 ->
    let target = get_target lv in
    let replacement = rename target in
    let vf' = rewrite_vf vf target replacement in
    let ve = Write (target, convert_aexp e1, convert_aexp e2) in 
    let ve' = rewrite_ve ve target replacement in
    (VAnd (vf', Label (0, VBinRel (VEq,target,ve'))),
     List.map (fun q -> rewrite_q q target replacement) qs)
  | Tuple (eops1,_), Lv (Tuple (eops2,_)) -> (* (a,b) := (1,2) *)
    List.fold_left2 (fun (acc_vf,acc_qs) eop1 eop2 ->
      match eop1,eop2 with
      | Some (Lv lv'),Some e' -> assign (lv',e') (acc_vf, acc_qs)
      | None,Some e' -> (acc_vf, acc_qs)
      | _ -> raise (Failure "invalid tuple assignment1")
    ) (vf,qs) eops1 eops2
  | Tuple _,_ -> raise (Failure "invalid tuple assignment2")
  | IndexAccess (_,None,_), _ -> raise (Failure "invalid IndexAccess assignment")

let handle_init_funcs (lvop,f,args) (vf,qs) =
  match lvop with
  | None ->
    (match f with
     | "mapping_init" ->
        (* Only allowed for certaint types of mapping. refer to 'get_default_value' function. *)
        let _ = assert (List.length args = 1) in
        let map = match List.hd args with Lv (Var (x,xinfo)) -> (x,xinfo.vtype) | _ -> assert false in
        (match get_type_var map with
         | Mapping (Address, EType (UInt n)) ->
           let new_f = VAnd (NoOverFlow map, SigmaEqual (VInt BatBig_int.zero, map)) in
           (VAnd (vf, new_f), qs)
         | Mapping (Address, EType Bool) -> (vf,qs)
         | Mapping (UInt n, EType Address) -> (vf,qs)
         | Mapping (UInt n1, EType (UInt n2)) -> (vf,qs)
         | Mapping (Address, EType Address) -> (vf,qs)
         | _ -> assert false)
    | "mapping_init2" ->
       let _ = assert (List.length args = 1) in
       (vf,qs)
    | "array_decl" ->
      let _ = assert (List.length args = 1) in
      let arr = match List.hd args with Lv (Var (x,xinfo)) -> VVar (x,xinfo.vtype) | _ -> assert false in
      let arr_typ = get_type_vexp arr in
      (match get_array_size arr_typ with
       | Some n -> (* @L[arr] := n *)
         let new_f = VBinRel (VEq, Read (VVar (length_map, Mapping2 (arr_typ, EType (UInt 256))),  arr, EType (UInt 256)), VInt (BatBig_int.of_int n)) in
         (VAnd (vf, new_f), qs)
       | None -> (* @L[arr] := 0 *)
         let new_f = VBinRel (VEq, Read (VVar (length_map, Mapping2 (arr_typ, EType (UInt 256))),  arr, EType (UInt 256)), VInt BatBig_int.zero) in
         (VAnd (vf, new_f), qs))
    | "dummy_init" -> (vf, qs)
    | _ -> failwith ("handle_init_funcs : " ^ f))
  | Some lv ->
    (match f with
     | "array_init" -> (vf,qs)
     | "dbytes_init" -> (vf,qs)
     | "string_init" -> (vf,qs)
     | "contract_init" -> (vf,qs)
     | "struct_init" -> (* must be handled in preprocessing step. *)
        failwith "struct_init : semantics.ml"
     | _ -> failwith ("handle_init_funcs : " ^ f))

let handle_built_in_funcs (lvop,f,args) (vf,qs) =
  match lvop with
  | None ->
    (match f with
     | "revert" -> (VFalse, qs)
     | "selfdestruct" -> (VFalse, qs)
     | "suicide" -> (VFalse, qs)
     | "delete" -> (vf, qs)
     | _ -> failwith ("handle_built_in_funcs: " ^ f))
  | Some lv -> (* lv is in 'Var' pattern *)
    (match f with
     | "keccak256" | "sha3" | "sha256" | "ripemd160" (* outputs hash value *)
     | "ecrecover" -> (vf,qs) (* recover address *)
     | "addmod" -> (vf,qs)
     | "blockhash" -> (vf,qs) (* hash of the given block *)
     | _ -> failwith ("handle_built_in_funcs: " ^ f))

let handle_address_built_in loc rcv (lvop,f,args) (vf,qs) =
  match lvop with
  | None ->
    (match f with
     | "transfer" ->
       let _ = assert (List.length args = 1) in
       let arg = List.hd args in
       let target = VVar eth_map in
       let replacement1 = rename target in
       (* B[this] := B[this] - arg *)
       let vf1 = rewrite_vf vf target replacement1 in
       let this = VVar this_addr in
       let ve = Write (target, this, VBinOp (VSub, Read (target,this,EType (UInt 256)), convert_aexp arg, EType (UInt 256))) in
       let ve1 = rewrite_ve ve target replacement1 in
       let res1 = VAnd (vf1, Label (0, VBinRel (VEq,target,ve1))) in
       let qs1 = List.map (fun q -> rewrite_q q target replacement1) qs in
       (* B[rcv] := B[rcv] + arg *)
       let replacement2 = rename target in
       let vf2 = rewrite_vf res1 target replacement2 in
       let ve = Write (target, convert_aexp rcv, VBinOp (VAdd, Read (target,convert_aexp rcv,EType (UInt 256)), convert_aexp arg, EType (UInt 256))) in
       let ve2 = rewrite_ve ve target replacement2 in
       let res2 = VAnd (vf2, Label (0, VBinRel (VEq,target,ve2))) in
       let qs2 = List.map (fun q -> rewrite_q q target replacement2) qs1 in
       (res2, qs2)
     | "balance" -> (vf,qs)
     | "send" -> (vf,qs)
     | "call" -> (vf,qs)
     | "delegatecall" -> (vf,qs)
     | _ -> failwith ("handle_address_built_in : " ^ f))
  | Some lv ->
    (match f with
     (* returns bool, i.e., success or failure *)
     | "send" | "call" | "delegatecall" | "staticcall" -> (vf,qs)
     | _ -> failwith ("handle_address_built_in : " ^ f))

let handle_array_built_in (lvop,exp,args) fname loc (vf,qs) =
  match exp with
  | Lv (MemberAccess (arr,"push",_,_)) ->
    (* tmp := @L[arr]; arr[tmp] := v; @L[arr] := tmp + 1 *)
    (* Without the first stmt, we get unsound results. *)
    let len_map_typ = Mapping2 (get_type_exp arr, EType (UInt 256)) in
    let len_arr = IndexAccess (Lv (Var (length_map, dummy_vinfo_with_typ len_map_typ)), Some arr, EType (UInt 256)) in (* @L[arr] *)
    let tmp = Var (fst (gen_newsym (EType (UInt 256))), dummy_vinfo_with_typ (EType (UInt 256))) in
    let arr_tmp = IndexAccess (arr, Some (Lv tmp), range_typ (get_type_exp arr)) in (* arr[tmp] *)
    let (vf1,qs1) = assign (tmp, Lv len_arr) (vf,qs) in (* first stmt *)
    let snd_stmt =
      (match List.length args with
       | 0 -> (* Since solc 0.6.0, 'arr.push()' is possible *)
         Lang.get_init_stmt arr_tmp loc (* initialize (arr[tmp]) : even 'mapping' type can be initialized when 'arr' is an array of mapping. *)
       | 1 -> Assign (arr_tmp, List.hd args, loc)
       | _ -> assert false) in
    let (vf2,qs2) = (* snd stmt *)
      (match snd_stmt with
       | Call (lvop,Lv (Var (f,_)),args,loc,_) -> handle_init_funcs (lvop,f,args) (vf1,qs1)
       | Assign (lv,e,loc) -> assign (lv,e) (vf1,qs1)
       | _ -> assert false) in
    let (vf3,qs3) = assign (len_arr, BinOp (Add, Lv tmp, Int (BatBig_int.of_int 1), mk_einfo (EType (UInt 256)))) (vf2,qs2) in (* third stmt *)
    (vf3,qs3)
  | Lv (MemberAccess (e,"pop",_,_)) -> (vf,qs)
  | _ -> failwith ("handle_array_built_in : " ^ fname)

let handle_abi fname (vf,qs) =
  match fname with
  | "decode" -> (vf,qs)
  | "encode" -> (vf,qs)
  | "encodePacked" -> (vf,qs)
  | "encodeWithSignature" -> (vf,qs)
  | "encodeWithSelector" -> (vf,qs)
  | _ -> raise (Failure ("handle_abi : " ^ fname))

let handle_undefs (lvop,exp,args) loc curf (vf,qs) =
  match exp with
  | Lv (Var (f,_)) when List.mem f built_in_funcs -> 
    handle_built_in_funcs (lvop,f,args) (vf,qs)
  | Lv (Var (f,_)) when List.mem f init_funcs ->
    handle_init_funcs (lvop,f,args) (vf,qs)
  | Lv (MemberAccess (e,f,_,_)) when is_address (get_type_exp e) ->
    handle_address_built_in loc e (lvop,f,args) (vf,qs)
  | Lv (MemberAccess (e,f,_,_)) when is_array (get_type_exp e) ->
    handle_array_built_in (lvop,exp,args) f loc (vf,qs)
  | Lv (MemberAccess (Lv (Var ("abi",_)),f,_,_)) ->
    handle_abi f (vf,qs)
  | Lv (MemberAccess (Lv (Var ("block",_)),"blockhash",_,_)) ->
    (vf, qs)
  | _ ->
    (if !Options.debug = "undeflib" then
      prerr_endline ("Warning - undefined functions encountred : " ^ to_string_exp exp ^ ", line " ^ string_of_int loc));
    (vf, qs)

let handle_static_call global caller (lvop,e,args) vf =
  let caller_cname = (get_finfo caller).scope_s in
  let callees = FuncMap.find_matching_funcs caller_cname e (List.map get_type_exp args) global.cnames global.fmap in
  let _ = assert (BatSet.cardinal callees = 1) in
  let callee = BatSet.choose callees in
  (* 1. remove terms that include variables which may be modified in callee *)
  let k = get_fkey callee in
  let vf = weaken_vf2 vf (BatSet.to_list (FuncDefUse.find_def_set k global.f_defuse)) in
  (* 2. if lv exists, replace target var by true *)
  let final =
    match lvop with
    | None -> vf
    | Some lv ->
      let def = BatSet.to_list (FuncDefUse.get_def_set_lv lv) in
      weaken_vf2 vf def in
  final

let handle_object_call global caller (lvop,e,args) vf =
  match lvop with
  | None -> vf
  | Some lv ->
    let def = BatSet.to_list (FuncDefUse.get_def_set_lv lv) in
    weaken_vf2 vf def

let convert_stmt : Global.t -> func -> Node.t -> vformula * query list -> vformula * query list
= fun global curf node (vf,qs) ->
  let stmt = find_stmt node (Lang.get_cfg curf) in
  match stmt with
  | Assign (lv,e,_) -> assign (lv,e) (vf,qs)
  | Decl lv -> (vf,qs)
  | Skip -> (vf,qs)
  | Return (Some e,_) -> (* ret_params <- e *)
    let ret_params = get_ret_params curf in
    let lv = try params_to_lv ret_params with _ -> assert false in
    assign (lv,e) (vf,qs)
  | Return (None,_) -> (vf,qs)
  | Throw -> (VFalse,qs)
  | Assume (e,_) -> (VAnd (vf, Label (1, convert_bexp e)), qs)
  | Assert (e,_) -> (vf,qs) (* effects will be reflected by subsequent statements generated in translation step. *)
  | Assembly (lst,_) ->
    let vars = List.map fst lst in
    (List.fold_left weaken_vf vf vars, qs)
  | Call (lvop,e,args,loc,_) (* built-in functions *)
    when FuncMap.is_undef e (List.map get_type_exp args) global.fmap ->
    handle_undefs (lvop,e,args) loc curf (vf,qs)
  | Call (lvop,e,args,loc,_) when is_static_call global.cnames stmt -> (* static call *)
    (handle_static_call global curf (lvop,e,args) vf, qs)
  | Call (lvop,e,args,loc,_) -> (* object calls *)
    (handle_object_call global curf (lvop,e,args) vf, qs)
  | If _ | Seq _ | While _
  | Break | Continue -> raise (Failure "convert_stmt")
