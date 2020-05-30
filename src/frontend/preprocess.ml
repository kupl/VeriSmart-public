open Lang
open Vocab
open CallGraph
open Options

(************************************)
(************************************)
(*** Move state_var_init to Cnstr ***)
(************************************)
(************************************)

let decl_to_stmt : string -> StructMap.t -> state_var_decl -> stmt
= fun cname smap (id,eop,vinfo) ->
  (match eop with
   | None -> get_init_stmt (Var (id,vinfo)) vinfo.vloc
   | Some e -> Assign (Var (id,vinfo), e, vinfo.vloc))

let move_f cid smap decls func =
  if is_constructor func then (* add initializations of decls only to constructor *)
    let fbody = get_body func in
    let inits = List.fold_left (fun acc decl -> Seq (acc, decl_to_stmt cid smap decl)) Skip decls in
    let rec replace_gvar_init stmt inits =
      match stmt with
      | Seq (s1,s2) -> Seq (replace_gvar_init s1 inits, replace_gvar_init s2 inits)
      | If (e,s1,s2) -> If (e, replace_gvar_init s1 inits, replace_gvar_init s2 inits)
      | While (e,s) -> While (e, replace_gvar_init s inits)
      | stmt when Lang.is_gvar_init stmt -> inits
      | _ -> stmt
    in
    update_body (replace_gvar_init fbody inits) func
  else func

let move_c smap (cid, decls, structs, enums, funcs, cinfo) =
  (cid, decls, structs, enums, List.map (move_f cid smap decls) funcs, cinfo)

let move_p contracts =
   let smap = StructMap.mk_smap contracts in
   List.map (move_c smap) contracts

let move_init_to_cnstr pgm = move_p pgm

(***********************)
(***********************)
(*** Replace TemExps ***)
(***********************)
(***********************)

let separator = "__"
let tmpvar_cnt = ref 0
let tmpvar = "Tmp"

let gen_tmpvar ?(org="") typ = 
  tmpvar_cnt:=!tmpvar_cnt+1;
  Var (tmpvar^(string_of_int !tmpvar_cnt), dummy_vinfo_with_typ_org typ org)

let rec is_member : exp -> bool
= fun e ->
  match e with
  | CallTemp (Lv (MemberAccess _), _, _) -> true
  | _ -> false

let rec hastmp_lv lv =
  match lv with
  | Var _ -> false
  | MemberAccess (e,_,_,_) -> hastmp_e e
  | IndexAccess (e,None,_) -> hastmp_e e
  | IndexAccess (e1,Some e2,_) -> hastmp_e e1 || hastmp_e e2
  | Tuple (eoplst,_) -> List.exists (fun eop -> match eop with None -> false | Some e -> hastmp_e e) eoplst

and hastmp_e e =
  match e with
  | Int _ | Real _ | Str _ -> false 
  | Lv lv -> hastmp_lv lv
  | Cast (_,e) -> hastmp_e e
  | BinOp (_,e1,e2,_) -> hastmp_e e1 || hastmp_e e2
  | UnOp (_,e,_) -> hastmp_e e
  | True | False | ETypeName _ -> false
  | AssignTemp _ | CondTemp _ | IncTemp _ | DecTemp _ | CallTemp _ -> true

and hastmp_s s =
  match s with
  | Assign (lv,e,_) -> hastmp_lv lv || hastmp_e e 
  | Decl _ -> false 
  | Seq (s1,s2) -> hastmp_s s1 || hastmp_s s2 
  | Call (None,e,params,_,_) -> hastmp_e e || List.exists hastmp_e params
  | Call (Some lv,e,params,_,_) -> hastmp_lv lv || hastmp_e e || List.exists hastmp_e params
  | Skip -> false
  | If (e,s1,s2) -> hastmp_e e || hastmp_s s1 || hastmp_s s2
  | While (e,s) -> hastmp_e e || hastmp_s s
  | Break -> false
  | Continue -> false
  | Return (None,_) -> false
  | Return (Some e,_) -> hastmp_e e 
  | Throw -> false
  | Assume (e,_) -> hastmp_e e
  | Assert (e,_) -> hastmp_e e
  | Assembly _ -> false

let hastmp_f (_,_,_,stmt,_) = hastmp_s stmt
let hastmp_c (_,_,_,_,funcs,_) = List.exists hastmp_f funcs
let hastmp_p contracts = List.exists hastmp_c contracts
let hastmp p = hastmp_p p

(* Given a exp, returns a pair of (replaced exp,new stmt) *)
let rec replace_tmpexp_e : exp -> exp * stmt
= fun exp ->
  match exp with
  | Int n -> (exp,Skip)
  | Real n -> (exp,Skip)
  | Str s -> (exp,Skip)
  | Lv lv ->
    let (lv',s) = replace_tmpexp_lv lv in 
    (Lv lv',s)
  | Cast (typ,e) ->
    let (e',s) = replace_tmpexp_e e in
    (Cast (typ,e'),s)
  | BinOp (bop,e1,e2,einfo) ->
    let (e1',s1) = replace_tmpexp_e e1 in
    let (e2',s2) = replace_tmpexp_e e2 in
    (BinOp (bop,e1',e2',einfo), Seq (s1,s2))
  | UnOp (uop,e,typ) ->
    let (e',s) = replace_tmpexp_e e in
    (UnOp (uop,e',typ), s)
  | True | False -> (exp,Skip)
  | ETypeName _ -> (exp,Skip)
  | IncTemp (Lv lv,prefix,loc) when prefix ->
    let typ = get_type_lv lv in
    (Lv lv,Assign (lv, BinOp (Add,Lv lv,Int (BatBig_int.of_int 1),{eloc=loc; etyp=typ; eid=0}),loc)) 
  | IncTemp (Lv lv,_,loc) -> (* postfix case *)
    let typ = get_type_lv lv in
    let tmpvar = gen_tmpvar typ in
    (Lv tmpvar,Seq (Assign (tmpvar, Lv lv, loc),
                    Assign (lv, BinOp (Add,Lv lv,Int (BatBig_int.of_int 1),{eloc=loc; etyp=typ; eid=0}),loc)))
  | DecTemp (Lv lv,prefix,loc) when prefix ->
    let typ = get_type_lv lv in
    (Lv lv,Assign (lv, BinOp (Sub,Lv lv,Int (BatBig_int.of_int 1),{eloc=loc; etyp=typ; eid=0}),loc)) 
  | DecTemp (Lv lv,_,loc) -> (* postfix case *)
    let typ = get_type_lv lv in
    let tmpvar = gen_tmpvar typ in
    (Lv tmpvar,Seq (Assign (tmpvar, Lv lv, loc),
                    Assign (lv, BinOp (Sub,Lv lv,Int (BatBig_int.of_int 1),{eloc=loc; etyp=typ; eid=0}),loc)))
  | CallTemp (Lv (Var (s,_)),params,einfo) when BatString.starts_with s "contract_init" ->
    let tmpvar = gen_tmpvar einfo.etyp in (* einfo.etyp : return type of call expression *)
    let fst_arg = Lv (Var (get_name_userdef einfo.etyp,dummy_vinfo)) in
    (Lv tmpvar, Call (Some tmpvar, Lv (Var ("contract_init",dummy_vinfo)), fst_arg::params, einfo.eloc, einfo.eid))
  | CallTemp (Lv (MemberAccess (Cast (t,e),id,id_info,typ)), params, einfo) -> (* ... := cast(y).f(33) *)
    let tmpvar = gen_tmpvar t in
    (CallTemp (Lv (MemberAccess (Lv tmpvar,id,id_info,typ)), params, einfo), Assign (tmpvar, Cast (t,e), einfo.eloc))
  | CallTemp (e,params,einfo) ->
    if is_tuple einfo.etyp then
      let tmpvars = List.map (gen_tmpvar ~org:(to_string_exp exp)) (unroll_tuple einfo.etyp) in
      let eoplst = List.map (fun tmp -> Some (Lv tmp)) tmpvars in
      let tuple = Tuple (eoplst, einfo.etyp) in
      (Lv tuple, Call (Some tuple, e, params, einfo.eloc, einfo.eid))
    else
      let tmpvar = gen_tmpvar ~org:(to_string_exp exp) einfo.etyp in
      (Lv tmpvar, Call (Some tmpvar, e, params, einfo.eloc, einfo.eid))
  | CondTemp (e1,e2,e3,typ,loc) ->
    let tmpvar = gen_tmpvar ~org:(to_string_exp exp) typ in
    (Lv tmpvar, Seq (Decl tmpvar, If (e1, Assign (tmpvar, e2, loc), Assign (tmpvar, e3, loc)))) 
  | AssignTemp (lv,e,loc) -> (Lv lv, Assign (lv,e,loc))
  | e -> raise (Failure ("replace_tmpexp_e : " ^ (to_string_exp e)))

and replace_tmpexp_lv : lv -> lv * stmt
= fun lv ->
  match lv with
  | Var _ -> (lv,Skip)
  | MemberAccess (Cast (t,e),id,id_info,typ) ->
    let tmpvar = gen_tmpvar ~org:(to_string_exp (Cast (t,e))) t in
    (MemberAccess (Lv tmpvar,id,id_info,typ), Assign (tmpvar,Cast (t,e),id_info.vloc))
  | MemberAccess (e,id,id_info,typ) ->
    let (e',s) = replace_tmpexp_e e in
    (MemberAccess (e',id,id_info,typ), s)
  | IndexAccess (e,None,typ) ->
    let (e',s) = replace_tmpexp_e e in
    (IndexAccess (e',None,typ), s)
  | IndexAccess (e1,Some e2,typ) ->
    let (e1',s1) = replace_tmpexp_e e1 in
    let (e2',s2) = replace_tmpexp_e e2 in
    (IndexAccess (e1',Some e2',typ), Seq (s1,s2))
  | Tuple (eoplst,typ) ->
    let (eoplst',final_s) =
      List.fold_left (fun (acc_lst,acc_s) eop ->
        match eop with
        | None -> (acc_lst@[None],acc_s)
        | Some e ->
          let (e',s) = replace_tmpexp_e e in
          (acc_lst@[Some e'], Seq (acc_s,s))
      ) ([],Skip) eoplst
    in
    (Tuple (eoplst',typ), final_s)

let has_gas_value_modifiers exp =
  match exp with
  | CallTemp (Lv (MemberAccess (e,"gas",_,_)),_,_) -> true
  | CallTemp (Lv (MemberAccess (e,"value",_,_)),_,_) -> true
  | _ -> false

(* e.g., given f.gas(10).value(5).gas(3) , return f *)
let rec remove_gas_value_modifiers exp =
  match exp with
  | CallTemp (Lv (MemberAccess (e,"gas",_,_)),_,_) -> remove_gas_value_modifiers e (* remove gas modifier chains, e.g., e.gas(10)(arg) => e(arg) *)
  | CallTemp (Lv (MemberAccess (e,"value",_,_)),_,_) -> remove_gas_value_modifiers e (* remove value modifier chains *)
  | _ -> exp 

(* get outer-most argument of gas modifier *)
let rec get_gas exp =
  match exp with
  (* | Lv (MemberAccess (e,"call",_,_)) when is_address (get_type_exp e) -> Int BatBig_int.zero *) 
  | CallTemp (Lv (MemberAccess (e,"gas",_,_)),args,_) ->
    let _ = assert (List.length args = 1) in
    List.hd args
  | CallTemp (Lv (MemberAccess (e,"value",_,_)),_,_) -> get_gas e
  | _ -> exp

(* get outer-most argument of value modifier *)
let rec get_value exp =
  match exp with
  (* | Lv (MemberAccess (e,"call",_,_)) when is_address (get_type_exp e) -> Int BatBig_int.zero *)
  | CallTemp (Lv (MemberAccess (e,"gas",_,_)),_,_) -> get_value e
  | CallTemp (Lv (MemberAccess (e,"value",_,_)),args,_) ->
    let _ = assert (List.length args = 1) in
    List.hd args
  | _ -> exp

let rec replace_tmpexp_s : stmt -> stmt
= fun stmt ->
  match stmt with
  | Assign (lv,e,loc) ->
    let (lv',new_stmt1) = replace_tmpexp_lv lv in
    let (e',new_stmt2) = replace_tmpexp_e e in
    Seq (Seq (new_stmt1,new_stmt2), Assign (lv',e',loc))
  | Decl lv -> stmt
  | Seq (s1,s2) -> Seq (replace_tmpexp_s s1, replace_tmpexp_s s2)
  | Call (lvop,e,params,loc,site) when has_gas_value_modifiers e ->
    let e' = remove_gas_value_modifiers e in
    (* let gas = get_gas e in
    let value = get_value e in *)
    Call (lvop,e',params,loc,site)
  | Call (None,e,params,loc,site) ->
    let (e',new_stmt1) = replace_tmpexp_e e in
    let (params',new_stmt2) = 
      List.fold_left (fun (acc_params,acc_stmt) param -> 
        let (param',s) = replace_tmpexp_e param in
        (acc_params@[param'], Seq (acc_stmt,s))
      ) ([],Skip) params
    in
    Seq (Seq (new_stmt1,new_stmt2), Call (None,e',params',loc,site))
  | Call (Some lv,e,params,loc,site) ->
    let (lv',new_stmt1) = replace_tmpexp_lv lv in
    let (e',new_stmt2) = replace_tmpexp_e e in
    let (params',new_stmt3) = 
      List.fold_left (fun (acc_params,acc_stmt) param ->  
        let (param',s) = replace_tmpexp_e param in
        (acc_params@[param'], Seq (acc_stmt,s))
      ) ([],Skip) params
    in
    Seq (Seq (Seq (new_stmt1,new_stmt2),new_stmt3), Call (Some lv',e',params',loc,site))
  | Skip -> stmt
  | If (e,s1,s2) ->
    let (e',new_stmt) = replace_tmpexp_e e in
    Seq (new_stmt, If (e',replace_tmpexp_s s1,replace_tmpexp_s s2))
  | While (e,s) ->
    let (e',new_stmt) = replace_tmpexp_e e in
    Seq (new_stmt, While (e', Seq(replace_tmpexp_s s,new_stmt)))
  | Break -> stmt
  | Continue -> stmt
  | Return (None,_) -> stmt
  | Return (Some e,loc_ret) ->
    let (e',new_stmt) = replace_tmpexp_e e in
    (match e',new_stmt with
     | Lv (Tuple ([],_)), Call (Some (Tuple ([],_)),e,args,loc,site) -> (* return f(), where f() returns void. *)
       Seq (Call (None,e,args,loc,site), Return (None,loc_ret))
     | _ -> Seq (new_stmt, Return (Some e',loc_ret)))
  | Throw -> stmt
  | Assume (e,loc) ->
    let (e',new_stmt) = replace_tmpexp_e e in
    Seq (new_stmt, Assume (e',loc))
  | Assert (e,loc) ->
    let (e',new_stmt) = replace_tmpexp_e e in
    Seq (new_stmt, Assert (e',loc))
  | Assembly _ -> stmt
  
let replace_tmpexp_f : func -> func
= fun (id, params, ret_params, stmt, finfo) ->
  (id, params, ret_params, replace_tmpexp_s stmt, finfo)

let replace_tmpexp_c : contract -> contract
= fun (id, decls, structs, enums, funcs, cinfo) -> 
  (id, decls, structs, enums, List.map replace_tmpexp_f funcs, cinfo)

let replace_tmpexp_p : pgm -> pgm
= fun pgm -> List.map replace_tmpexp_c pgm

let rec loop f pgm =
  let pgm' = f pgm in
    if not (hastmp pgm') then pgm'
    else loop f pgm'

let replace_tmpexp : pgm -> pgm
= fun pgm -> loop replace_tmpexp_p pgm 

(******************)
(******************)
(** Remove Skips **)
(******************)
(******************)

let rec rmskip_s s =
  match s with
  | Seq (Skip,s) -> rmskip_s s
  | Seq (s,Skip) -> rmskip_s s
  | Seq (s1,s2) -> Seq (rmskip_s s1,rmskip_s s2)
  | If (e,s1,s2) -> If (e,rmskip_s s1,rmskip_s s2)
  | While (e,s) -> While (e,rmskip_s s)
  | _ -> s

let rmskip_f (fid, params, ret_params, stmt, finfo) = (fid, params, ret_params, rmskip_s stmt, finfo)
let rmskip_c (cid, decls, structs, enums, funcs, cinfo) = (cid, decls, structs, enums, List.map rmskip_f funcs, cinfo) 
let rmskip_p contracts = List.map rmskip_c contracts
let rmskip p = p |> rmskip_p |> rmskip_p |> rmskip_p

(*******************************)
(*******************************)
(** Normalize many variations **)
(*******************************)
(*******************************)

let rec norm_s s =
  match s with
  | Seq (s1,s2) -> Seq (norm_s s1, norm_s s2)
  | If (e,s1,s2) -> If (e, norm_s s1, norm_s s2)
  | While (e,s) -> While (e, norm_s s)
  | Return (Some (Lv (Tuple ([],_))),loc) -> Return (None,loc) (* return (); => return; *)
  | _ -> s

let norm_f (fid, params, ret_params, stmt, finfo) = (fid, params, ret_params, norm_s stmt, finfo)
let norm_c (cid, decls, structs, enums, funcs, cinfo) = (cid, decls, structs, enums, List.map norm_f funcs, cinfo) 
let norm_p contracts = List.map norm_c contracts
let normalize p = norm_p p 

(***********************************)
(***********************************)
(** Handling Using-for-Directives **)
(***********************************)
(***********************************)

let find_matching_lib_name lib_funcs callee_name arg_typs =
  let matching_func =
    List.find (fun f ->
      let param_typs = get_param_types f in
      BatString.equal (get_fname f) callee_name &&
      List.length arg_typs = List.length param_typs && (* should be checked first before checking convertibility *)
      List.for_all2 FuncMap.is_implicitly_convertible arg_typs param_typs
    ) lib_funcs in
  (get_finfo matching_func).scope_s

let rec ufd_s : (id * typ) list -> func list -> stmt -> stmt
= fun lst lib_funcs stmt ->
  let lib_names = List.map fst lst in
  match stmt with
  | Call (lvop,Lv (MemberAccess (e,fname,fname_info,typ)),args,loc,site) 
    when List.mem fname (List.map get_fname lib_funcs) (* e.g., (a+b).add(c) when using SafeMath *)
         && not (List.mem (to_string_exp e) lib_names) (* e.g., SafeMath.add (a,b) should not be changed. *) -> 
    let e_typ = get_type_exp e in
    let lst' = List.filter (fun (_,t) -> t = e_typ || t = Void) lst in (* "Void" is for the case of "using libname for *". *)
    let cand_lib_names = List.map fst lst' in
    (match List.length cand_lib_names with
     | 0 -> stmt (* no using for syntax *)
     | _ ->
       let arg_typs = List.map get_type_exp (e::args) in (* move the receiver to the first argument *)
       let lib_funcs' = List.filter (fun f -> List.mem (get_finfo f).scope_s cand_lib_names) lib_funcs in
       let lib_name = find_matching_lib_name lib_funcs' fname arg_typs in (* from libs, using fname and arg_typs, find corresponding library name *)
       let lib_typ = Contract lib_name in
       let lib_var = Lv (Var (lib_name, dummy_vinfo_with_typ lib_typ)) in
       Call (lvop,Lv (MemberAccess (lib_var,fname,fname_info,typ)),e::args,loc,site))
  | Call _ -> stmt 
  | Assign _ -> stmt
  | Decl _ -> stmt
  | Skip -> stmt
  | Seq (s1,s2) -> Seq (ufd_s lst lib_funcs s1, ufd_s lst lib_funcs s2)
  | If (e,s1,s2) -> If (e, ufd_s lst lib_funcs s1, ufd_s lst lib_funcs s2) 
  | While (e,s) -> While (e, ufd_s lst lib_funcs s)
  | Break | Continue | Return _ | Throw 
  | Assume _ | Assert _ | Assembly _ -> stmt

let ufd_f lst lib_funcs (fid, params, ret_params, stmt, finfo) = (fid, params, ret_params, ufd_s lst lib_funcs stmt, finfo)

let ufd_c pgm (cid, decls, structs, enums, funcs, cinfo) =
  let lib_names = List.map fst cinfo.lib_typ_lst in
  let libs = List.map (find_contract_id pgm) lib_names in
  let lib_funcs = List.fold_left (fun acc lib -> acc @ (get_funcs lib)) [] libs in
  (cid, decls, structs, enums, List.map (ufd_f cinfo.lib_typ_lst lib_funcs) funcs, cinfo)

let ufd_p contracts = List.map (ufd_c contracts) contracts
let ufd p = ufd_p p (* abbreviation for using for directives *) 

let prop_libs_c : contract list -> contract -> contract
= fun parents c -> (* propagete parents => c *)
  List.fold_left (fun acc parent ->
    let libs_parent = (get_cinfo parent).lib_typ_lst in
    let acc_info = get_cinfo acc in
    let libs' = BatSet.to_list (BatSet.union (BatSet.of_list libs_parent) (BatSet.of_list acc_info.lib_typ_lst)) in
    update_cinfo {acc_info with lib_typ_lst = libs'} acc 
  ) c parents

let prop_libs_p p =
  List.map (fun c ->
    let nids_of_parents = get_inherit_order c in
    let parents = List.tl (List.map (find_contract_nid p) nids_of_parents) in 
    prop_libs_c parents c 
  ) p

let propagate_libtyp pgm = prop_libs_p pgm

let replace_lib_calls pgm =
  pgm |> propagate_libtyp |> ufd

(****************************************)
(****************************************)
(** Add a prefix (i.e., library name)  **)
(** for the function calls in library. **)
(****************************************)
(****************************************)

(* e.g., https://etherscan.io/address/0x3f354b0c5c5a554fcfcb7bac6b25a104da7a9fce#code *)
let rec add_libname_s : id -> stmt -> stmt
= fun lib stmt ->
  match stmt with
  | Seq (s1,s2) -> Seq (add_libname_s lib s1, add_libname_s lib s2)  
  | If (e,s1,s2) -> If (e, add_libname_s lib s1, add_libname_s lib s2)
  | Call (lvop,Lv (Var (v,vinfo)),args,loc,site) ->
    let libvar = Lv (Var (lib, dummy_vinfo_with_typ (Contract lib))) in
    Call (lvop, Lv (MemberAccess (libvar, v, vinfo, vinfo.vtype)), args, loc, site)
  | While (e,s) -> While (e, add_libname_s lib s)
  | _ -> stmt 

let add_libname_f lib f =
  let old_stmt = get_body f in
  let new_stmt = add_libname_s lib old_stmt in
  update_body new_stmt f

let add_libname_c c =
  let libname = get_cname c in
  let old_funcs = get_funcs c in
  let new_funcs = List.map (add_libname_f libname) old_funcs in
  update_funcs new_funcs c 

let add_libname_p contracts =
  List.map (fun c ->
    if is_library c then add_libname_c c
    else c
  ) contracts

let add_libname_fcalls_in_lib p = add_libname_p p

(*****************************)
(*****************************)
(** Merge into one contract **)
(*****************************)
(*****************************)

let add_func : func -> contract -> contract
= fun f ((cid,decls,structs,enums,funcs,cinfo) as contract) ->
  let b = List.exists (equal_sig f) funcs || (get_finfo f).is_constructor in
    (* Do not copy *)
    (* 1) if functions are constructors, and  *)
    (* 2) if functions with same signatures are already exist in the contract *)
    if b then contract 
    else
      let old_finfo = get_finfo f in
      let new_finfo = {old_finfo with scope = cinfo.numid; scope_s = cid} in
      let new_f = update_finfo new_finfo f in
      (cid, decls, structs, enums, funcs@[new_f], cinfo)

let add_func2 : contract -> contract -> contract
= fun _from _to ->
  let funcs = get_funcs _from in
  List.fold_left (fun acc f ->
    add_func f acc
  ) _to funcs

let equal_gdecl : state_var_decl -> state_var_decl -> bool 
= fun (id1,_,_) (id2,_,_) -> BatString.equal id1 id2

let add_decl : state_var_decl -> contract -> contract
= fun cand contract ->
  let (cid,decls,structs,enums,funcs,cinfo) = contract in
  let b = List.exists (equal_gdecl cand) decls in
    if b then contract
    else (cid, cand::decls, structs, enums, funcs, cinfo)

let add_decl2 : contract -> contract -> contract
= fun _from _to ->
  let decls = get_decls _from in
  List.fold_left (fun acc d ->
    add_decl d acc 
  ) _to decls

let add_enum : contract -> contract -> contract
= fun _from _to ->
  (* Duplicated (i.e., already declared) enums by inheritance will be rejected by solc, so just copy enums. *)
  let enums1 = get_enums _from in
  let enums2 = get_enums _to in
  update_enums (enums1 @ enums2) _to

let add_struct : contract -> contract -> contract
= fun _from _to ->
  (* Similarly, duplicated (i.e., already declared) structures by inheritance will be rejected by solc, so just copy structures. *)
  let structs1 = get_structs _from in
  let structs2 = get_structs _to in
  update_structs (structs1 @ structs2) _to

let copy_c : contract list -> contract -> contract
= fun parents c ->
  List.fold_left (fun acc parent ->
    acc |> add_func2 parent |> add_decl2 parent |> add_enum parent |> add_struct parent
  ) c parents

let copy_p : pgm -> pgm
= fun p ->
  List.fold_left (fun acc c ->
    let nids_of_parents = get_inherit_order c in
    let parents = List.tl (List.map (find_contract_nid p) nids_of_parents) in
    let c' = copy_c parents c in
    let acc' = modify_contract c' acc in
    acc'
  ) p p

let copy pgm = copy_p pgm

(*********************)
(*********************)
(** Replace 'super' **)
(*********************)
(*********************)

let find_next : id list -> id -> id
= fun lst target ->
  let target_idx = match BatList.index_of target lst with Some idx -> idx | None -> assert false in
  BatList.at lst (target_idx+1)

let find_next_contracts : contract list -> id -> contract list
= fun lst target ->
  let names = List.map get_cname lst in
  let target_idx = match BatList.index_of target names with Some idx -> idx | None -> assert false in
  BatList.fold_lefti (fun acc i c ->
    if i<target_idx+1 then acc 
    else acc@[c]
  ) [] lst

let rec rs_s : contract list -> id -> stmt -> stmt
= fun family cur_cname stmt ->
  match stmt with
  | Assign _ -> stmt
  | Decl _ -> stmt
  | Seq (s1,s2) -> Seq (rs_s family cur_cname s1, rs_s family cur_cname s2)
  | Call (lvop, Lv (MemberAccess (Lv (Var (x,xinfo)),id,id_info,typ)), args, loc, site)
    when BatString.equal x "super" ->
    let arg_typs = List.map get_type_exp args in
    let supers = find_next_contracts family cur_cname in
    let matched_parent =
      List.find (fun super ->
        let funcs = get_funcs super in
        List.exists (fun f ->
          let (id',typs') = get_fsig f in
          if BatString.equal id id' && List.length arg_typs = List.length typs' then
            List.for_all2 FuncMap.is_implicitly_convertible arg_typs typs'
          else false 
        ) funcs 
      ) supers in
    let matched_parent_name = get_cname matched_parent in
    Call (lvop, Lv (MemberAccess (Lv (Var (matched_parent_name,xinfo)),id,id_info,typ)), args, loc, site)
  | Call _ -> stmt
  | Skip -> stmt
  | If (e,s1,s2) -> If (e, rs_s family cur_cname s1, rs_s family cur_cname s2)
  | While (e,s) -> While (e, rs_s family cur_cname s)
  | _ -> stmt

let rs_f : contract list -> id -> func -> func
= fun final_inherit cur_cname f ->
  let old_body = get_body f in
  let new_body = rs_s final_inherit cur_cname old_body in
  update_body new_body f

let rs_c : contract list -> contract -> contract
= fun final_inherit c ->
  let cur_cname = get_cname c in 
  let old_funcs = get_funcs c in
  let new_funcs = List.map (rs_f final_inherit cur_cname) old_funcs in
  update_funcs new_funcs c 

let rs_p : pgm -> pgm
= fun p ->
  let main = get_main_contract p in
  (* left (parent) => right (children) *)
  let nids_of_parents = get_inherit_order main in 
  let final_inherit = List.map (find_contract_nid p) nids_of_parents in
  let family_names = List.map get_cname final_inherit in
  List.fold_left (fun acc c ->
    if List.mem (get_cname c) family_names then
      let c' = rs_c final_inherit c in
      modify_contract c' acc
    else acc
  ) p p 

let replace_super pgm = rs_p pgm 

(**********************)
(**********************)
(** Generate getters **)
(**********************)
(**********************)

let get_public_state_vars : contract -> (id * vinfo) list
= fun c ->
  let decls = get_decls c in 
  let decls' = List.filter (fun (_,_,vinfo) -> vinfo.vvis = Public && (is_uintkind vinfo.vtype || is_address vinfo.vtype)) decls in
  List.map (fun (v,_,vinfo) -> (v,vinfo)) decls'

(* generate getter functions for public state variables *)
let add_getter_x : string -> int -> id * vinfo -> func
= fun cname cnumid (x,xinfo) ->
  let ret = (Translator.gen_param_name(), dummy_vinfo_with_typ xinfo.vtype) in
  let stmt = Return (Some (Lv (Var (x,xinfo))), -1) in
  let finfo = {is_constructor=false; is_payable=false; fvis=External; fid=(-1); scope=cnumid; scope_s=cname; cfg=empty_cfg} in
  gen_func ~fname:x ~params:[] ~ret_params:[ret] ~stmt:stmt ~finfo:finfo

let add_getter_c : contract -> contract
= fun c ->
  let cname = get_cname c in
  let cnumid = (get_cinfo c).numid in
  let vars = get_public_state_vars c in
  List.fold_left (fun acc x ->
    let f = add_getter_x cname cnumid x in
    add_func f acc
  ) c vars

let add_getter_p p =
  List.fold_left (fun acc c ->
    let c' = add_getter_c c in
    let acc' = modify_contract c' acc in
    acc'
  ) p p

let add_getter pgm = add_getter_p pgm 

(******************************)
(******************************)
(** Inline Constructor Calls **)
(******************************)
(******************************)

let rec has_cnstr_calls_s : func list -> stmt -> bool
= fun cnstrs stmt ->
  match stmt with
  | Assign _ -> false
  | Seq (s1,s2) -> has_cnstr_calls_s cnstrs s1 || has_cnstr_calls_s cnstrs s2
  | Decl _ -> false
  | Call (None,Lv (Var (f,_)),_,_,_) when List.mem f (List.map get_fname cnstrs) -> true
  | Call _ -> false
  | Skip -> false
  | Assume _ -> false
  | While (_,s) -> has_cnstr_calls_s cnstrs s
  | If (_,s1,s2) -> has_cnstr_calls_s cnstrs s1 || has_cnstr_calls_s cnstrs s2 
  | Continue | Break | Return _ | Throw | Assert _ | Assembly _ -> false 

let has_cnstr_calls_f : func list -> func -> bool 
= fun cnstrs f ->
  if is_constructor f then
    has_cnstr_calls_s cnstrs (get_body f)
  else false

let has_cnstr_calls_c cnstrs c = List.exists (has_cnstr_calls_f cnstrs) (get_funcs c)
let has_cnstr_calls_p p = 
  let cnstrs = List.map get_cnstr p in 
  List.exists (has_cnstr_calls_c cnstrs) p
let has_cnstr_calls p = has_cnstr_calls_p p

let bind_params : int -> param list -> exp list -> stmt
= fun loc params args ->
  try
    List.fold_left2 (fun acc (x,xinfo) arg -> 
      Seq (acc, Assign (Var (x,xinfo), arg, loc)) 
    ) Skip params args
  with Invalid_argument _ -> Skip

(* postprocess recursive constructor calls from outer contracts *)
let rec post_cbody : id * exp list -> func list -> stmt -> stmt
= fun (f,args) cnstrs (cbody as stmt) ->
  match stmt with
  | Assign _ | Decl _ -> stmt
  | Seq (s1,s2) -> Seq (post_cbody (f,args) cnstrs s1, post_cbody (f,args) cnstrs s2)
  | Call (None,Lv (Var (f',_)),args',loc,_) when BatString.equal f f' ->
    if List.length args=0 && List.length args'>0 then
      let lst = List.filter (fun c -> BatString.equal f (get_fname c)) cnstrs in
      let _ = assert (List.length lst = 1) in
      let cnstr = List.hd lst in
      bind_params loc (get_params cnstr) args'
    else if List.length args>0 && List.length args'>0 then
      Skip (* argument values are already set; valid for 0.4.26 but invalid for 0.5.12 *)
    else raise (Failure "post_cbody")
  | Call _ -> stmt
  | Skip | Assume _ -> stmt
  | While (e,s) -> While (e, post_cbody (f,args) cnstrs s)
  | If (e,s1,s2) -> If (e, post_cbody (f,args) cnstrs s1, post_cbody (f,args) cnstrs s2)
  | Continue | Break | Return _ | Throw | Assert _ | Assembly _ -> stmt

let rec inline_cnstr_calls_s : id -> func list -> stmt -> stmt
= fun cname cnstrs stmt -> (* cname: contract name that contains statements *)
  match stmt with
  | Assign _ -> stmt
  | Seq (s1,s2) -> Seq (inline_cnstr_calls_s cname cnstrs s1, inline_cnstr_calls_s cname cnstrs s2)
  | Decl _ -> stmt
  | Call (None,Lv (Var (f,_)),_,loc,_) when BatString.equal cname f ->
    Skip (* recursive constructor calls from an enclosing contract have no side effects. *)
  | Call (None,Lv (Var (f,_)),args,loc,_) when List.mem f (List.map get_fname cnstrs) ->
    let lst = List.filter (fun c -> BatString.equal f (get_fname c)) cnstrs in
    let _ = assert (List.length lst = 1) in
    let cnstr = List.hd lst in
    let binding = bind_params loc (get_params cnstr) args in
    let cbody = get_body cnstr in
    let cbody = post_cbody (f,args) cnstrs cbody in
    Seq (binding, cbody)
  | Call _ -> stmt
  | Skip -> stmt
  | Assume _ -> stmt
  | While (e,s) -> While (e, inline_cnstr_calls_s cname cnstrs s)
  | If (e,s1,s2) -> If (e, inline_cnstr_calls_s cname cnstrs s1, inline_cnstr_calls_s cname cnstrs s2)
  | Continue | Break | Return _ | Throw | Assert _ | Assembly _ -> stmt

let inline_cnstr_calls_f : id -> func list -> func -> func
= fun cname cnstrs f ->
  if is_constructor f then
    let body' = inline_cnstr_calls_s cname cnstrs (get_body f) in
    update_body body' f 
  else f

let inline_cnstr_calls_c : func list -> contract -> contract
= fun cnstrs (id, decls, structs, enums, funcs, cinfo) ->
  (id, decls, structs, enums, List.map (inline_cnstr_calls_f id cnstrs) funcs, cinfo)

let rec loop_inline f p =
  let p' = f p in
    if not (has_cnstr_calls p') then p'
    else loop_inline f p'

let inline_cnstr_calls_p : pgm -> pgm
= fun p -> 
  let cnstrs = List.map get_cnstr p in 
  List.map (inline_cnstr_calls_c cnstrs) p 

let inline_cnstr_calls : pgm -> pgm
= fun p -> loop_inline inline_cnstr_calls_p p 

(*******************************)
(*******************************)
(** Add return initialization **)
(*******************************)
(*******************************)

let add_ret_init_f : func -> func
= fun f ->
  let ret_params = get_ret_params f in
  let new_stmt =
    List.fold_left (fun acc (x,xinfo) ->
      let s = get_init_stmt (Var (x,xinfo)) xinfo.vloc in
      if is_skip acc then s
      else Seq (acc,s)
    ) Skip ret_params in
  let body = get_body f in
  let new_body = if is_skip new_stmt then body else Seq (new_stmt,body) in
  update_body new_body f  

let add_ret_init_c : contract -> contract
= fun c ->
  let funcs = get_funcs c in
  let funcs = List.map add_ret_init_f funcs in
  update_funcs funcs c

let add_ret_init_p : pgm -> pgm
= fun contracts ->
  List.map (fun c ->
   if BatString.equal (get_cinfo c).ckind "library" then c (* for optimization, do not introduce additional stmt for lib functions. *)
   else add_ret_init_c c
  ) contracts 

let add_ret_init : pgm -> pgm
= fun p -> add_ret_init_p p

(***********************)
(***********************)
(** Variable Renaming **)
(***********************)
(***********************)

let should_not_be_renamed (id,vinfo) =
  BatString.starts_with id tmpvar
  || vinfo.refid = -1 (* some built-in variables do not have reference id, thus we assign '-1' *)

let rec rename_lv enums lv =
  match lv with
  | Var (id,vinfo) ->
    if should_not_be_renamed (id,vinfo) then lv
    else Var (id ^ separator ^ string_of_int vinfo.refid, vinfo)
  | MemberAccess (Lv (Var (x,xt)),id,id_info,typ)
    when is_enum typ && List.mem x (List.map fst enums) ->
    let members = List.assoc x enums in
    let idx = remove_some (BatList.index_of id members) in
    MemberAccess (Lv (Var (x,xt)),id ^ "__idx" ^ string_of_int idx, id_info,typ)
  | MemberAccess (Lv (MemberAccess (e,fname,finfo,typ1)),"selector",sinfo,typ2) ->
    MemberAccess (Lv (MemberAccess (rename_e enums e,fname,finfo,typ1)),"selector",sinfo,typ2)
  | MemberAccess (e,id,id_info,typ) ->
    let id' =
      if should_not_be_renamed (id,id_info) then id
      else id ^ separator ^ string_of_int id_info.refid
    in
    MemberAccess (rename_e enums e, id', id_info, typ)
  | IndexAccess (e,None,_) -> raise (Failure "rename_lv enums1")
  | IndexAccess (e1,Some e2,typ) -> IndexAccess (rename_e enums e1, Some (rename_e enums e2), typ)
  | Tuple (eoplst,typ) ->
    let eoplst' = 
      List.map (fun eop ->
        match eop with
        | None -> None
        | Some e -> Some (rename_e enums e)
      ) eoplst
    in
    Tuple (eoplst',typ)

and rename_e enums exp =
  match exp with
  | Int _ | Real _ | Str _ -> exp
  | Lv lv ->
    if List.mem (to_string_lv lv) Lang.keyword_vars then Lv lv
    else Lv (rename_lv enums lv)
  | Cast (typ,e) -> Cast (typ,rename_e enums e)
  | BinOp (bop,e1,e2,einfo) -> BinOp (bop, rename_e enums e1, rename_e enums e2, einfo)
  | UnOp (uop,e,typ) -> UnOp (uop, rename_e enums e, typ)
  | True | False | ETypeName _ -> exp
  | IncTemp _ | DecTemp _ -> raise (Failure "rename_e enums1")
  | CallTemp _ -> raise (Failure ("rename_e enums2: " ^ (to_string_exp exp)))
  | CondTemp _ -> raise (Failure ("rename_e enums3: " ^ (to_string_exp exp))) 
  | AssignTemp _ -> raise (Failure ("rename_e enums4: " ^ (to_string_exp exp)))

let rec rename_s cnames enums stmt =
  match stmt with
  | Assign (lv,exp,loc) -> Assign (rename_lv enums lv, rename_e enums exp, loc)
  | Decl lv -> Decl (rename_lv enums lv)
  | Seq (s1,s2) -> Seq (rename_s cnames enums s1, rename_s cnames enums s2)
  | Call (lvop, e, exps, loc, site) ->
    let lvop' =
      (match lvop with
       | None -> lvop
       | Some lv -> Some (rename_lv enums lv)) in
    let e' =
      (match e with
       | e when List.mem (to_string_exp e) built_in_funcs -> e
       | Lv (Var (fname,info)) -> e
       | Lv (MemberAccess (Lv (Var (prefix,prefix_info)) as arr, fname, fname_info, typ)) ->
         if List.mem prefix cnames || BatString.equal prefix "super" then e
         else Lv (MemberAccess (rename_e enums arr, fname, fname_info, typ)) 
       | _ -> e (* raise (Failure ("rename_s (preprocess.ml) : unexpected fname syntax - " ^ (to_string_stmt stmt))) *)) in
    let exps' =
      if to_string_exp e = "struct_init" (* Rule: the first arg is struct name *)
         || to_string_exp e = "struct_init2"
        then (List.hd exps)::(List.map (rename_e enums) (List.tl exps))
      else List.map (rename_e enums) exps in
    Call (lvop', e', exps', loc, site)
  | Skip -> Skip
  | If (e,s1,s2) -> If (rename_e enums e, rename_s cnames enums s1, rename_s cnames enums s2)
  | While (e,s) -> While (rename_e enums e, rename_s cnames enums s)
  | Break | Continue | Return (None,_) -> stmt
  | Return (Some e,loc) -> Return (Some (rename_e enums e), loc)
  | Throw -> Throw
  | Assume (e,loc) -> Assume (rename_e enums e, loc)
  | Assert (e,loc) -> Assert (rename_e enums e, loc)
  | Assembly (lst,loc) ->
    Assembly (List.map (fun (x,refid) -> (x ^ separator ^ string_of_int refid, refid)) lst, loc)

let rename_param (id,vinfo) =
  if BatString.starts_with id Translator.param_name then (id,vinfo)
  else (id ^ separator ^ string_of_int vinfo.refid, vinfo)

let rename_f cnames enums (fid, params, ret_params, stmt, finfo) =
  (fid, List.map rename_param params, List.map rename_param ret_params, rename_s cnames enums stmt, finfo)

let rename_d decl =
  match decl with
  | (id,None,vinfo) -> (id ^ separator ^ string_of_int vinfo.refid, None, vinfo)
  | (id,Some e,vinfo) -> (id ^ separator ^ string_of_int vinfo.refid, Some e, vinfo)

let rename_st (sname, members) =
  let members' = List.map (fun (v,vinfo) -> (v ^ separator ^ string_of_int vinfo.refid, vinfo)) members in
  (sname, members')

let rename_c cnames (cid, decls, structs, enums, funcs, cinfo) =
  (cid, List.map rename_d decls, List.map rename_st structs, enums, List.map (rename_f cnames enums) funcs, cinfo)

let rename_p p =
  let cnames = get_cnames p in
  List.map (rename_c cnames) p

let rename pgm = rename_p pgm  

let tuple_assign lv exp loc =
  match lv, exp with
  | Tuple (eops1, typ1), Lv (Tuple (eops2, _)) when List.length eops1 <> List.length eops2 -> begin
    match List.hd eops1 with
    | Some _ ->
      let (eops1', _) = list_fold (fun e (acc, acc_index) ->
        if acc_index = 0 then (acc@[None], acc_index)
        else (acc, acc_index - 1)
      ) eops2 (eops1, List.length eops1) in
      Assign (Tuple (eops1', typ1), exp, loc)
      
    | None ->
      let eops1' = List.tl eops1 in
      let (eops1'', _) = list_fold (fun e (acc, acc_index) ->
        if acc_index = 0 then (acc, acc_index)
        else (None::acc, acc_index - 1)
      ) eops2 (eops1', (List.length eops2) - (List.length eops1')) in
      Assign (Tuple (eops1'', typ1), exp, loc)
  end

  | _ -> Assign (lv, exp, loc)

let rec tuple_s stmt =
  match stmt with
  | Assign (lv,exp,loc) -> tuple_assign lv exp loc
  | Seq (s1,s2) -> Seq (tuple_s s1, tuple_s s2) 
  | If (e,s1,s2) -> If (e, tuple_s s1, tuple_s s2)
  | While (e,s) -> While (e, tuple_s s)
  | _ -> stmt

let tuple_f f = update_body (tuple_s (get_body f)) f
let tuple_c c = update_funcs (List.map tuple_f (get_funcs c)) c

let extend_tuple pgm = List.map tuple_c pgm

(*************)
(*************)
(** Casting **)
(*************)
(*************)

let rec cast_lv lv =
  match lv with
  | Var _ -> lv
  | MemberAccess (e,x,xinfo,typ) -> MemberAccess (cast_e e, x, xinfo, typ)
  | IndexAccess (e,None,typ) -> IndexAccess (cast_e e, None, typ)
  | IndexAccess (e1,Some e2,typ) ->
    let expected_idx_typ = domain_typ (get_type_exp e1) in
    let idx_typ = get_type_exp e2 in
    let e1' = cast_e e1 in
    let e2' = if expected_idx_typ = idx_typ then cast_e e2 else Cast (expected_idx_typ, cast_e e2) in
    IndexAccess (e1', Some e2', typ)
  | Tuple (eoplst,typ) ->
    let eoplst' = List.map (fun eop -> match eop with Some e -> Some (cast_e e) | None -> None) eoplst in
    Tuple (eoplst',typ)

and cast_e exp =
  match exp with
  | Int _ | Real _ | Str _ -> exp
  | Lv lv -> Lv (cast_lv lv)
  | Cast (typ,e) -> Cast (typ, cast_e e)
  | BinOp (bop,e1,e2,einfo) ->
    let t1 = get_type_exp e1 in
    let t2 = get_type_exp e2 in
    let ctyp = common_typ e1 e2 in
    let e1' = if t1 = ctyp then cast_e e1 else Cast (ctyp, cast_e e1) in
    let e2' = if t2 = ctyp then cast_e e2 else Cast (ctyp, cast_e e2) in
    BinOp (bop, e1', e2', einfo)
  | UnOp (uop,e,typ) -> UnOp (uop, cast_e e, typ)
  | True | False -> exp 
  | ETypeName _ -> exp
  | IncTemp _ | DecTemp _ | CallTemp _
  | CondTemp _ | AssignTemp _ -> failwith "cast_e" 

and cast_s stmt =
  match stmt with
  | Assign (lv,e,loc) ->
    let lv_typ = get_type_lv lv in
    let e_typ = get_type_exp e in
    let lv' = cast_lv lv in
    let e' = if lv_typ = e_typ then cast_e e else Cast (lv_typ, cast_e e) in
    Assign (lv', e', loc)
  | Decl lv -> stmt
  | Seq (s1,s2) -> Seq (cast_s s1, cast_s s2)
  | Call (lvop,e,elst,loc,site) ->
    let lvop' = match lvop with Some lv -> Some (cast_lv lv) | None -> None in
    let e' = cast_e e in
    let elst' = List.map cast_e elst in
    Call (lvop', e', elst', loc, site) 
  | Skip -> stmt
  | If (e1,s1,s2) -> If (cast_e e1, cast_s s1, cast_s s2) 
  | While (e,s) -> While (cast_e e, cast_s s)
  | Break | Continue -> stmt
  | Return _ | Throw -> stmt
  | Assume (e,loc) -> Assume (cast_e e, loc) 
  | Assert (e,loc) -> Assert (cast_e e, loc)
  | Assembly _ -> stmt

let cast_f f = update_body (cast_s (get_body f)) f
let cast_c c = update_funcs (List.map cast_f (get_funcs c)) c

let cast pgm = List.map cast_c pgm

(*************************************************)
(**** Add non-zero assumption after division  ****)
(*************************************************)

(* Reference: https://github.com/Z3Prover/z3/issues/2843 *)
let rec add_nz_s stmt =
  match stmt with
  | Assign (lv,e,loc) ->
    let lst = (add_nz_lv lv) @ (add_nz_e e) in
    List.fold_left (fun acc x -> Seq (acc, Assume (x, -1))) stmt lst
  | Decl lv -> stmt
  | Seq (s1,s2) -> Seq (add_nz_s s1, add_nz_s s2)
  | Call (None,e,elst,loc,site) ->
    let lst = (add_nz_e e) @ (List.fold_left (fun acc e' -> acc @ (add_nz_e e')) [] elst) in
    List.fold_left (fun acc x -> Seq (acc, Assume (x,-1))) stmt lst
  | Call (Some lv,e,elst,loc,site) ->
    let lst = (add_nz_lv lv) @ (add_nz_e e) @ (List.fold_left (fun acc e' -> acc @ (add_nz_e e')) [] elst) in
    List.fold_left (fun acc x -> Seq (acc, Assume (x,-1))) stmt lst
  | Skip -> stmt
  | If (e,s1,s2) ->
    let lst = add_nz_e e in
    if List.length lst = 0 then stmt (* just for readability of IL *)
    else
      let s' = List.fold_left (fun acc x -> Seq (acc, Assume (x,-1))) Skip lst in
      If (e, Seq (s', add_nz_s s1), Seq (s', add_nz_s s2))
  | While (e,s) ->
    let lst = add_nz_e e in
    if List.length lst = 0 then stmt (* just for readability of IL *)
    else
      let s' = List.fold_left (fun acc x -> Seq (acc, Assume (x,-1))) Skip lst in
      Seq (While (e, Seq (s', add_nz_s s)), s')
  | Break | Continue -> stmt
  | Return _ | Throw -> stmt
  | Assume (e,loc) ->
    let lst = add_nz_e e in
    List.fold_left (fun acc x -> Seq (acc, Assume (x, -1))) stmt lst
  | Assert (e,loc) ->
    let lst = add_nz_e e in
    List.fold_left (fun acc x -> Seq (acc, Assume (x, -1))) stmt lst
  | Assembly _ -> stmt

and add_nz_e exp =
  match exp with
  | Int _ | Real _ | Str _ -> []
  | Lv lv -> add_nz_lv lv
  | Cast (_,e) -> add_nz_e e
  | BinOp (Div,e1,e2,einfo) ->
    (mk_neq e2 (Int BatBig_int.zero)) :: ((add_nz_e e1) @ (add_nz_e e2))
  | BinOp (_,e1,e2,_) -> (add_nz_e e1) @ (add_nz_e e2)
  | UnOp (_,e,_) -> add_nz_e e
  | True | False | ETypeName _ -> []
  | IncTemp _ | DecTemp _ | CallTemp _
  | CondTemp _ | AssignTemp _ -> failwith "add_nz_e"

and add_nz_lv lv =
  match lv with
  | Var _ -> []
  | MemberAccess (e,_,_,_) -> add_nz_e e
  | IndexAccess (e,None,t) -> add_nz_e e
  | IndexAccess (e1,Some e2,t) -> (add_nz_e e1) @ (add_nz_e e2)
  | Tuple (eops,_) ->
    List.fold_left (fun acc eop ->
      match eop with
      | None -> acc
      | Some e -> acc @ (add_nz_e e)
    ) [] eops

let add_nz_f f = update_body (add_nz_s (get_body f)) f
let add_nz_c c = update_funcs (List.map add_nz_f (get_funcs c)) c
let add_nz pgm = List.map add_nz_c pgm

(*****************************)
(**** Desugar struct_init ****)
(*****************************)

let rec fold_left2 lv loc acc members values =
  match members, values with
  | [], [] -> acc
  | [], h2::t2 -> invalid_arg "preprocess: desugar struct init"
  | h1::t1, [] ->
    if is_mapping (get_type_var2 h1) then fold_left2 lv loc acc t1 []
    else invalid_arg "preprocess: desugar struct init"
  | h1::t1, h2::t2 ->
    if is_mapping (get_type_var2 h1) then fold_left2 lv loc acc t1 t2
    else
      let lv' = MemberAccess (Lv lv, fst h1, snd h1, get_type_var2 h1) in
      let stmt' = Assign (lv', h2, loc) in
      let stmt'' = if is_skip acc then stmt' else Seq (acc,stmt') in
      fold_left2 lv loc stmt'' t1 t2

let rec dsg cname smap stmt =
  match stmt with
  | Assign _ | Decl _ -> stmt
  | Seq (s1,s2) -> Seq (dsg cname smap s1, dsg cname smap s2)
  | Call (Some lv, Lv (Var ("struct_init",_)), args, loc, site) ->
    let (struct_exp, member_values) = (List.hd args, List.tl args) in
    let members = snd (StructMap.find cname struct_exp smap) in
    fold_left2 lv loc Skip members member_values
  | Call (Some lv, Lv (Var ("struct_init2",_)), args, loc, site) ->
    let (args1, args2) = BatList.split_at ((List.length args / 2) + 1) args in
    let (struct_exp, member_names, member_values) = (List.hd args1, List.tl args1, args2) in
    let org_members = snd (StructMap.find cname struct_exp smap) in
    let find_matching_member mname member_lst = List.find (fun (name',_) -> BatString.starts_with name' (to_string_exp mname)) member_lst in
    let members = List.map (fun name -> find_matching_member name org_members) member_names in
    fold_left2 lv loc Skip members member_values
  | Call _ -> stmt
  | Skip -> stmt
  | If (e,s1,s2) -> If (e, dsg cname smap s1, dsg cname smap s2)
  | While (e,s) -> While (e, dsg cname smap s)
  | Break | Continue -> stmt
  | Return _ | Throw -> stmt
  | Assume _ | Assert _ | Assembly _ -> stmt

let desugar_struct_f cname smap f = update_body (dsg cname smap (get_body f)) f

let desugar_struct_c smap c =
  let cname = get_cname c in
  update_funcs (List.map (desugar_struct_f cname smap) (get_funcs c)) c

let desugar_struct pgm =
  let smap = StructMap.mk_smap pgm in
  List.map (desugar_struct_c smap) pgm

let run : pgm -> pgm
= fun p ->
  let p = move_init_to_cnstr p in
  let p = replace_tmpexp p in
  let p = normalize p in
  let p = rmskip p in
  let p = replace_lib_calls p in
  let p = add_libname_fcalls_in_lib p in
  let p = inline_cnstr_calls p in
  let p = add_getter p in
  let p = rmskip p in
  let p = replace_super p in
  let p = copy p in
  let p = rename p in
  let p = add_ret_init p in 
  let p = extend_tuple p in
  let p = add_nz p in
  let p = desugar_struct p in
  p
