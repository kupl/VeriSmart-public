open Lang
open MakeCfg
open Vlang
open Vocab
open Global
open ItvDom
open Query
open Options

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
  | Var (id,vinfo) -> VVar (id, vinfo.vtyp)
  | MemberAccess (e,"length",info,_) ->
    VVar ("@L", Mapping2 (get_type_exp e, info.vtyp))
  | MemberAccess (e,"balance",info,_) ->
    let _ = assert (info.vtyp = EType (UInt 256)) in
    let _ = assert (is_address (get_type_exp e)) in
    VVar ("@B", Mapping (Address, info.vtyp))
  | MemberAccess (e,x,xinfo,_) -> VVar (x, Mapping2 (get_type_exp e, xinfo.vtyp))
  | IndexAccess (Lv lv,_,_) -> get_target lv
  | _ -> raise (Failure ("semantics (get_target) : " ^ to_string_lv lv))

let rec recur : vexp -> vexp
= fun ve ->
  match ve with
  | Write (VVar _,_,_) -> ve
  | Write (Read (ve1,ve2),idx,e) -> recur (Write (ve1,ve2,ve))
  | _ -> failwith ("recur : " ^ to_string_vexp ve)

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
    if s="this" then VVar this_addr
    else if List.mem s Lang.keyword_vars then VVar (s, get_type_lv lv)
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
    (match bop with
     | Add -> VBinOp (VAdd, convert_aexp e1, convert_aexp e2, typ)
     | Sub -> VBinOp (VSub, convert_aexp e1, convert_aexp e2, typ)
     | Mul -> VBinOp (VMul, convert_aexp e1, convert_aexp e2, typ)
     | Div -> VBinOp (VDiv, convert_aexp e1, convert_aexp e2, typ)
     | Mod -> VBinOp (VMod, convert_aexp e1, convert_aexp e2, typ)
     | Exponent -> VBinOp (VPower, convert_aexp e1, convert_aexp e2, typ)
     | ShiftL -> VBinOp (VShiftL, convert_aexp e1, convert_aexp e2, typ)
     | ShiftR -> VBinOp (VShiftR, convert_aexp e1, convert_aexp e2, typ)
     | BAnd -> VBinOp (VBAnd, convert_aexp e1, convert_aexp e2, typ)
     | BOr -> VBinOp (VBOr, convert_aexp e1, convert_aexp e2, typ)
     | BXor -> VBinOp (VBXor, convert_aexp e1, convert_aexp e2, typ)
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
  | IndexAccess (e1,Some e2,t) when is_dbytes (get_type_exp e1) ->
    let lmap_typ = Mapping2 (get_type_exp e1, EType (UInt 256)) in
    let size = Read (VVar (length_map, lmap_typ), convert_aexp e1) in
    let idx = VBinOp (VSub, VBinOp (VSub, size, VInt BatBig_int.one, EType (UInt 256)), convert_aexp e2, EType (UInt 256)) in
    Read (convert_aexp e1, idx)
  | IndexAccess (e1,Some e2,t) -> Read (convert_aexp e1, convert_aexp e2)
  | IndexAccess (e,None,_) -> failwith "convert_lv - IndexAccess"
  | MemberAccess (e,"balance",_,_) -> Read (VVar eth_map, convert_aexp e)
  | MemberAccess (e,"length",_,_) when is_array (get_type_exp e) ->
    Read (VVar (length_map, Mapping2 (get_type_exp e, typ)), convert_aexp e)
  | MemberAccess (_,"selector",_,_) -> VVar (to_string_lv lv,typ) (* typ: bytes4 *)
  | MemberAccess (e,x,xinfo,etyp) when is_enum typ && BatString.exists x "__idx" ->
    let (_,idx) = BatString.split x "__idx" in
    VCast (typ, VInt (BatBig_int.of_int (int_of_string idx)))
  | MemberAccess (e,x,xinfo,etyp) ->
    Read (VVar (x, Mapping2 (get_type_exp e, xinfo.vtyp)), convert_aexp e)
  | Tuple _ -> failwith ("convert_lv - Tuple : " ^ to_string_lv lv) (* handled in assignment level *)

and convert_bexp : exp -> vformula 
= fun exp ->
  match exp with
  | True -> VTrue
  | False -> VFalse
  | Lv lv -> convert_bexp_lv lv
  | BinOp (bop,e1,e2,einfo) ->
    let _ = assert (not (is_dbytes (get_type_exp e1)) && not (is_dbytes (get_type_exp e1))) in
    (match bop with
     | GEq -> VBinRel (VGeq, convert_aexp e1, convert_aexp e2)
     | Gt -> VBinRel (VGt, convert_aexp e1, convert_aexp e2)
     | LEq -> VBinRel (VGeq, convert_aexp e2, convert_aexp e1)
     | Lt -> VBinRel (VGt, convert_aexp e2, convert_aexp e1)
     | Eq -> VBinRel (VEq, convert_aexp e1, convert_aexp e2)
     | NEq -> VNot (VBinRel (VEq, convert_aexp e1, convert_aexp e2))
     | LAnd -> VAnd (convert_bexp e1, convert_bexp e2)
     | LOr -> VOr (convert_bexp e1, convert_bexp e2)
     | _ -> failwith ("convert_bexp1 : " ^ to_string_exp exp))
  | UnOp (uop,e,typ) ->
    let _ = assert (not (is_dbytes (get_type_exp e))) in
    (match uop with
     | LNot -> VNot (convert_bexp e)
     | _ -> failwith ("convert_bexp2 : " ^ to_string_exp exp))
  | _ -> failwith ("convert_bexp3 : " ^ to_string_exp exp)

and convert_bexp_lv : lv -> vformula
= fun lv ->
  let _ = assert (is_bool (get_type_lv lv)) in
  VBinRel (VEq, convert_lv lv, VCond VTrue)

let rewrite_q : vexp -> vexp -> query -> query
= fun target replacement q ->
  {q with vc2 = match q.vc2 with Imply _ -> q.vc2 | _ -> rewrite_vf q.vc2 target replacement}
  (* {q with vc2 = rewrite_vf q.vc2 target replacement} *)

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
    let qs' = List.map (rewrite_q target replacement) qs in
    (VAnd (vf', Label (0, VBinRel (VEq,target,ve'))), qs')
  | IndexAccess (arr, Some idx, t), e ->
    let target = get_target lv in
    let replacement = rename target in
    let vf' = rewrite_vf vf target replacement in
    let ve = recur (Write (convert_aexp arr, convert_aexp idx, convert_aexp e)) in
    let ve' = rewrite_ve ve target replacement in
    let qs' = List.map (rewrite_q target replacement) qs in
    (VAnd (vf', Label (0, VBinRel (VEq,target,ve'))), qs')
  | MemberAccess (e1,x,xinfo,t), e2 ->
    let target = get_target lv in
    let replacement = rename target in
    let vf' = rewrite_vf vf target replacement in
    let ve = Write (target, convert_aexp e1, convert_aexp e2) in
    let ve' = rewrite_ve ve target replacement in
    let qs' = List.map (rewrite_q target replacement) qs in
    (VAnd (vf', Label (0, VBinRel (VEq,target,ve'))), qs')
  | Tuple (eops1,_), Lv (Tuple (eops2,_)) -> (* (a,b) := (1,2) *)
    List.fold_left2 (fun (acc_vf,acc_qs) eop1 eop2 ->
      match eop1,eop2 with
      | Some (Lv lv'),Some e' -> assign (lv',e') (acc_vf, acc_qs)
      | None,Some e' -> (acc_vf, acc_qs)
      | _ -> raise (Failure "invalid tuple assignment1")
    ) (vf,qs) eops1 eops2
  | Tuple _,_ -> raise (Failure "invalid tuple assignment2")
  | IndexAccess (_,None,_), _ -> raise (Failure "invalid IndexAccess assignment")


let bcnt = ref 0 (* bound variable i counter *)
let new_bound_var typ = bcnt:=!bcnt+1; ("@i" ^ string_of_int !bcnt, typ)

(* generate constraint for 'Decl lv' *)
(* bvars : accumulated bound variables; accumulated whenever 'mapping' type is encountered. *)
let rec decl : StructMap.t -> var list -> vexp -> vformula
= fun smap bvars vexp ->
  let typ = get_typ_vexp vexp in
  match typ with
  | ConstInt | ConstString | ConstReal -> assert false
  | EType etyp ->
    let vf =
      (match etyp with
       | Address -> VBinRel (VEq, vexp, VInt BatBig_int.zero)
       | Bool -> VBinRel (VEq, vexp, VCond VFalse)
       | String -> VBinRel (VEq, vexp, VVar ("@", ConstString))
       | UInt _ -> VBinRel (VEq, vexp, VInt BatBig_int.zero)
       | SInt _ -> VBinRel (VEq, vexp, VInt BatBig_int.zero)
       | Bytes _ | DBytes -> VTrue)
    in
    if List.length bvars = 0 then vf
    else ForAll (bvars, vf)

  | Mapping (etyp',typ') ->
    let i = new_bound_var (EType etyp') in
    let bvars' = bvars @ [i] in
    let vexp' = Read (vexp, VVar i) in
    decl smap bvars' vexp'

  | Array (t,sizeop) ->
    (match sizeop with
     | None -> (* dynamic array => @L[arr] = 0 *)
       VBinRel (VEq, Read (VVar (length_map, Mapping2 (typ, EType (UInt 256))), vexp), VInt BatBig_int.zero)
     | Some n -> (* static array with size 'n' => @L[arr] = n *)
       VBinRel (VEq, Read (VVar (length_map, Mapping2 (typ, EType (UInt 256))), vexp), VInt (BatBig_int.of_int n)))

  | Struct lst ->
    let members = StructMap.find (get_name_userdef typ) smap in
    let members = List.map (fun m -> (fst m, get_type_var2 m)) members in
    List.fold_left (fun acc m ->
      let ve = Read (VVar (fst m, Mapping2 (Struct lst, snd m)), vexp) in (* s.m => m'[s] *)
      let new_f = decl smap bvars ve in
      VAnd (acc, new_f)
    ) VTrue members
  | Contract cid -> VBinRel (VEq, vexp, VCast (Contract cid, VInt BatBig_int.zero))
  | Mapping2 _ -> assert false
  | Enum _ -> VBinRel (VEq, vexp, VCast (typ, VInt BatBig_int.zero))
  | TupleType _ -> assert false
  | Void -> assert false

let convert_decl : StructMap.t -> lv -> vformula
= fun smap lv ->
  let ve = convert_lv lv in
  let vf = decl smap [] ve in
  let _ = bcnt:=0 in
  vf

let handle_init_funcs (lvop,f,args) (vf,qs) =
  match lvop with
  | None -> failwith ("handle_init_funcs : " ^ f)
  | Some lv ->
    (match f with
     | "array_init" -> (vf,qs)
     | "dbytes_init" -> (vf,qs)
     | "string_init" -> (vf,qs)
     | "contract_init" -> (vf,qs)
     | "struct_init" -> failwith "struct_init : semantics.ml" (* must be handled in preprocessing step. *)
     | _ -> failwith ("handle_init_funcs : " ^ f))

let addr1 = "0x" ^ (BatString.repeat "0" 37) ^ "111"
let addr2 = "0x" ^ (BatString.repeat "0" 37) ^ "222"

let uint1 = "0"
let uint2 = "600000000000000000"
let uint3 = "1000000000000000000"

let bytes16 = "0x00000000000000000000000000000001"

let cond1 (a,b,c,d) =
  VAnd (VBinRel (VEq, a, VInt (BatBig_int.of_string bytes16)),
    VAnd (VBinRel (VEq, b, VInt (BatBig_int.of_string addr1)),
      VAnd (VBinRel (VEq, c, VInt (BatBig_int.of_string addr2)), VBinRel (VEq, d, VInt (BatBig_int.of_string uint1)))))

let cond2 (a,b,c,d) =
  VAnd (VBinRel (VEq, a, VInt (BatBig_int.of_string bytes16)),
    VAnd (VBinRel (VEq, b, VInt (BatBig_int.of_string addr1)),
      VAnd (VBinRel (VEq, c, VInt (BatBig_int.of_string addr1)), VBinRel (VEq, d, VInt (BatBig_int.of_string uint2)))))

let cond3 (a,b,c,d) =
  VAnd (VBinRel (VEq, a, VInt (BatBig_int.of_string bytes16)),
    VAnd (VBinRel (VEq, b, VInt (BatBig_int.of_string addr1)),
      VAnd (VBinRel (VEq, c, VInt (BatBig_int.of_string addr2)), VBinRel (VEq, d, VInt (BatBig_int.of_string uint3)))))

let hashout1 = VCast (EType (Bytes 32), VInt (BatBig_int.of_string "0x5dbf7fcec09ae7957550174580f0415015f0e9a5b1985a8bd55613aa9bff2c40"))
let hashout2 = VCast (EType (Bytes 32), VInt (BatBig_int.of_string "0xfaf9ec944ffac469e076d6ce56060c5d3efb34b6ab7b2c225d78ac5215568db1"))
let hashout3 = VCast (EType (Bytes 32), VInt (BatBig_int.of_string "0x19900eeb85ea846013af468c24b22b5f08e1dd47e0bb561c5ed03e30d61eee1d"))

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
     | "keccak256" | "sha3" -> (* outputs hash value *)
       let hash_typs = [EType (Bytes 16); EType Address; EType Address; EType (UInt 256)] in
       if (not (!Options.mode = "exploit") || not (List.map get_type_exp args = hash_typs) || not !check_re) then (vf,qs)
       else
         let a,b,c,d = BatList.at args 0, BatList.at args 1, BatList.at args 2, BatList.at args 3 in
         let a,b,c,d = convert_aexp a, convert_aexp b, convert_aexp c, convert_aexp d in
         let cond1,cond2,cond3 = cond1 (a,b,c,d), cond2 (a,b,c,d), cond3 (a,b,c,d) in
         let output = Ite (VCond cond1, hashout1, Ite(VCond cond2, hashout2, Ite(VCond cond3, hashout3, hashout3))) in
         (* assign *)
         let target = get_target lv in
         let replacement = rename target in
         let vf' = rewrite_vf vf target replacement in
         let ve' = rewrite_ve output target replacement in
         let qs' = List.map (rewrite_q target replacement) qs in
         (VAnd (vf', Label (1, VBinRel (VEq,target,ve'))), qs')
     | "sha256" | "ripemd160" -> (* outputs hash value *)
       (* if !Options.mode = "exploit" then (VFalse,qs)
       else *) (vf,qs)
     | "ecrecover" -> (* recover address *)
       if !Options.mode = "exploit" then (VFalse,qs)
       else (vf,qs)
     | "addmod" -> (vf,qs)
     | "blockhash" -> (vf,qs) (* hash of the given block *)
     | _ -> failwith ("handle_built_in_funcs: " ^ f))

let transfer_ether loc rcv ether (vf,qs) =
  (* 1. this.balance := this.balance - value *)
  (* 2. rcv.balance := rcv.balance + value *)
  let balance_info = mk_vinfo ~typ:(EType (UInt 256)) () in
  let this_info = mk_vinfo ~typ:(Contract !main_contract) () in
  let this = Cast (EType Address, Lv (Var ("this", this_info))) in
  (* let this_info = mk_vinfo ~typ:(EType Address) () in
  let this = Lv (Var ("this",this_info)) in *)
  let this_balance = MemberAccess (this,"balance", balance_info, EType (UInt 256)) in
  let this_dec = BinOp (Sub, Lv this_balance, ether, mk_einfo (EType (UInt 256))) in
  let rcv_balance = MemberAccess (rcv, "balance", balance_info, EType (UInt 256)) in
  let rcv_inc = BinOp (Add, Lv rcv_balance, ether, mk_einfo (EType (UInt 256))) in
  let (vf',qs') = assign (this_balance,this_dec) (vf,qs) in
  let (vf'',qs'') = assign (rcv_balance,rcv_inc) (vf',qs') in
  (vf'',qs'')


let handle_address_built_in loc rcv (lvop,f,args) (ethop,gasop) (vf,qs) =
  (* match lvop with *)
  match f with
  | "transfer" -> (vf,qs)
    (* let _ = assert (List.length args = 1) in
    let ether = List.hd args in
    transfer_ether loc rcv ether (vf,qs) *)
  | "send" -> (vf,qs)
    (* let _ = assert (List.length args = 1) in
    let ether = List.hd args in
    transfer_ether loc rcv ether (vf,qs) *)
  | "call" -> (vf,qs)
    (* (match ethop with
     | None -> (vf,qs)
     | Some ether ->
       transfer_ether loc rcv ether (vf,qs)) *)
  | "balance" -> (vf,qs)
  | "delegatecall" | "staticcall" -> (vf,qs)
  | _ -> failwith ("handle_address_built_in : " ^ f)


let handle_array_built_in smap (lvop,exp,args) fname loc (vf,qs) =
  match exp with
  | Lv (MemberAccess (arr,"push",_,_)) ->
    (* tmp := @L[arr]; arr[tmp] := v; @L[arr] := tmp + 1 *)
    (* Without the first stmt, we get unsound results. *)
    let len_map_typ = Mapping2 (get_type_exp arr, EType (UInt 256)) in
    let len_arr = IndexAccess (Lv (Var (length_map, mk_vinfo ~typ:len_map_typ ())), Some arr, EType (UInt 256)) in (* @L[arr] *)
    let tmp = Var (fst (gen_newsym (EType (UInt 256))), mk_vinfo ~typ:(EType (UInt 256)) ()) in
    let arr_tmp = IndexAccess (arr, Some (Lv tmp), range_typ (get_type_exp arr)) in (* arr[tmp] *)
    let (vf1,qs1) = assign (tmp, Lv len_arr) (vf,qs) in (* first stmt *)
    let snd_stmt =
      (match List.length args with
       | 0 -> (* 'arr.push()' is possible for solc >= 0.6.0 *)
         Decl arr_tmp (* initialize (arr[tmp]) : even 'mapping' type can be initialized when 'arr' is an array of mapping. *)
       | 1 -> Assign (arr_tmp, List.hd args, loc)
       | _ -> assert false)
    in
    let (vf2,qs2) = (* snd stmt *)
      (match snd_stmt with
       | Decl lv ->
         let vf' = convert_decl smap lv in
         let vf'' = VAnd (vf1,vf') in
         (vf'', qs1)
       | Assign (lv,e,loc) -> assign (lv,e) (vf1,qs1)
       | _ -> assert false)
    in
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

let handle_undefs global (lvop,exp,args) (ethop,gasop) loc (vf,qs) =
  match exp with
  | Lv (Var (f,_)) when List.mem f built_in_funcs ->
    handle_built_in_funcs (lvop,f,args) (vf,qs)
  | Lv (Var (f,_)) when List.mem f init_funcs ->
    handle_init_funcs (lvop,f,args) (vf,qs)
  | Lv (MemberAccess (e,f,_,_)) when is_address (get_type_exp e) ->
    handle_address_built_in loc e (lvop,f,args) (ethop,gasop) (vf,qs)
  | Lv (MemberAccess (e,f,_,_)) when is_array (get_type_exp e) ->
    handle_array_built_in global.smap (lvop,exp,args) f loc (vf,qs)
  | Lv (MemberAccess (Lv (Var ("abi",_)),f,_,_)) ->
    handle_abi f (vf,qs)
  | Lv (MemberAccess (Lv (Var ("block",_)),"blockhash",_,_)) ->
    (vf, qs)
  | _ ->
    (if !Options.debug = "undeflib" then
      prerr_endline ("Warning - undefined functions encountred : " ^ to_string_exp exp ^ ", line " ^ string_of_int loc.line));
    (vf, qs)

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
  | Decl lv ->
    let target = get_target lv in
    let replacement = rename target in
    let vf' = rewrite_vf vf target replacement in
    let new_vf = convert_decl global.smap lv in
    let vf'' = VAnd (vf',new_vf) in
    let qs' = List.map (rewrite_q target replacement) qs in
    (vf'',qs')
  | Skip -> (vf,qs)
  | Return (Some e,_) -> (* ret_params <- e *)
    let ret_params = get_ret_params curf in
    let lv = try params_to_lv ret_params with _ -> assert false in
    assign (lv,e) (vf,qs)
  | Return (None,_) -> (vf,qs)
  | Throw -> (VFalse,qs)
  | Assume (e,_) -> (VAnd (vf, Label (1, convert_bexp e)), qs)
  | Assert (e,_,_) -> (vf,qs) (* effects will be reflected by subsequent statements generated in translation step. *)
  | Assembly (lst,_) ->
    let vars = List.map fst lst in
    (List.fold_left weaken_vf vf vars, qs)

  | Call (lvop,e,args,ethop,gasop,loc,_) when is_undef_call global.fmap stmt ->
    handle_undefs global (lvop,e,args) (ethop,gasop) loc (vf,qs)

  | Call (lvop,e,args,ethop,gasop,loc,_) when is_internal_call global.fmap global.cnames stmt -> assert false
  | Call _ when MakeCfg.is_external_call_node node (Lang.get_cfg curf) -> assert false

  | Call (lvop,e,args,ethop,gasop,loc,_) -> (* external calls *)
    if !Options.mode="exploit" && not !check_re then (VFalse, qs)
    else
      (handle_object_call global curf (lvop,e,args) vf, qs)

  | If _ | Seq _ | While _ | Break | Continue
  | PlaceHolder | Unchecked _ -> failwith ("convert_stmt: " ^ to_string_stmt stmt)
