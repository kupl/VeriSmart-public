open Itv
open ItvDom
open Lang
open Vocab
open Global
open Vlang

let rec eval_aexp : exp -> Mem.t -> Val.t 
= fun e mem ->
  match e with
  | Int n -> (Itv (V n, V n), GTaint.bot, BTaint.bot)
  | Str s -> (Itv.top, GTaint.bot, BTaint.bot)
  | Lv lv ->
    if List.mem (to_string_lv lv) Lang.keyword_vars || Lang.is_balance_keyword lv then
      if List.mem (to_string_lv lv) Lang.blk_keyword_vars then
        (Itv.top, Val.gtaint_of (Mem.find (loc_of lv) mem), BTaint.top)
      else Val.update_itv Itv.top (Mem.find (loc_of lv) mem) 
    else Mem.find (loc_of lv) mem 
  | Cast (t,e) -> (* overapproximation by not performing wrap-aroud *)
    eval_aexp e mem
  | True -> Val.bot 
  | False -> Val.bot 
  | UnOp (uop,e,t) ->
    let v = eval_aexp e mem in
    eval_uop uop v
  | BinOp (bop,e1,e2,einfo) ->
    let v1,v2 = eval_aexp e1 mem, eval_aexp e2 mem in
    eval_bop bop v1 v2
  | _ -> raise (Failure ("eval_aexp : tmp expressions should not exist."))

and eval_uop : uop -> Val.t -> Val.t
= fun uop v ->
  match uop with
  | Pos -> v 
  | Neg -> Val.update_itv Itv.top v
  | LNot -> Val.bot
  | BNot -> Val.update_itv Itv.top v

and eval_bop : bop -> Val.t -> Val.t -> Val.t
= fun bop v1 v2 ->
  let gtaint = GTaint.join (Val.gtaint_of v1) (Val.gtaint_of v2) in
  let btaint = BTaint.join (Val.btaint_of v1) (Val.btaint_of v2) in
  let itv1,itv2 = Val.itv_of v1, Val.itv_of v2 in
  match bop with
  | Add -> (Itv.plus itv1 itv2, gtaint, btaint) 
  | Sub -> (Itv.minus itv1 itv2, gtaint, btaint) 
  | Mul -> (Itv.times itv1 itv2, gtaint, btaint)
  | Div -> (Itv.divide itv1 itv2, gtaint, btaint)
  | Mod -> (Itv.top, gtaint, btaint)
  | Exponent -> (Itv.power itv1 itv2, gtaint, btaint)
  | ShiftL | ShiftR | BAnd | BOr | BXor
  | GEq | Gt | LEq | Lt | Eq | NEq | LAnd | LOr -> (Itv.top, gtaint, btaint)

and loc_of : lv -> Loc.t
= fun lv ->
  match lv with
  | Var (id,vinfo) -> (id, vinfo.vtype)
  | MemberAccess (Lv lv,x,xinfo,_) -> loc_of lv
  | IndexAccess (Lv lv,_,_) -> loc_of lv
  | _ -> raise (Failure ("loc_of in itvSem.ml : " ^ (to_string_lv lv)))

let update : Loc.t -> Val.t -> Mem.t -> Mem.t
= fun loc v mem -> Mem.weak_update loc v mem

(* always weakly updates *)
let rec assign (lv,e) mem =
  let lv_typ = get_type_lv lv in
  match lv,e with
  | _, Lv (Tuple (eops,_)) when is_array lv_typ ->
    let mem' =
      if is_static_array lv_typ then
        let size = BatBig_int.of_int (remove_some (get_array_size lv_typ)) in
        Mem.weak_update (length_map, EType (UInt 256)) ((Itv (V size,V size)), GTaint.bot, BTaint.bot) mem
      else (* dynamic array *)
        Mem.weak_update (length_map, EType (UInt 256)) (Itv.top, GTaint.bot, BTaint.bot) mem
    in
    BatList.fold_lefti (fun acc i eop ->
      match eop with
      | Some e ->
        let t = get_type_array_elem lv_typ in (* type of "lv[i]" *)
        assign (IndexAccess (Lv lv,Some (Int (BatBig_int.of_int i)),t), e) acc
      | None -> acc
    ) mem' eops
  | Tuple (eops1,_), Lv (Tuple (eops2,_)) -> (* (a,b) := (1,2) *)
    List.fold_left2 (fun acc eop1 eop2 ->
      match eop1,eop2 with
      | Some (Lv lv'),Some e' -> assign (lv',e') acc
      | None,Some e' -> acc
      | _ -> raise (Failure "invalid tuple assignment1")
    ) mem eops1 eops2
  | _ -> update (loc_of lv) (eval_aexp e mem) mem

let handle_one_callee callee (lvop,e,args) mem =
  let params = get_params callee in
  let ret_params = get_ret_params callee in
  (* params <- args *)
  let mem = try assign (params_to_lv params, args_to_exp args) mem with NoParameters -> mem in
  (* lvop <- ret_params *)
  let mem =
    match lvop with
    | None -> mem
    | Some lv -> try assign (lv, Lv (params_to_lv ret_params)) mem with NoParameters -> mem in
  mem

let handle_fcall global caller (lvop,e,args) mem =
  let cid = (get_finfo caller).scope_s in
  let callees = FuncMap.find_matching_funcs cid e (List.map get_type_exp args) global.cnames global.fmap in
  BatSet.fold (fun callee acc ->
    handle_one_callee callee (lvop,e,args) mem 
  ) callees mem

let handle_init_funcs global ctx_cname (lvop,f,args) loc mem =
  match lvop with
  | None ->
    (match f with
     | "mapping_init" | "mapping_init2" ->
       let _ = assert (List.length args = 1) in
       let loc = BatSet.choose (var_exp (List.hd args)) in
       update loc (Itv (V zero, V zero), GTaint.bot, BTaint.bot) mem
     | "array_decl"
     | "dummy_init" ->
       let vars = List.fold_left (fun acc arg -> BatSet.union (var_exp arg) acc) BatSet.empty args in
       BatSet.fold (fun loc acc ->
         update loc (Itv.top, GTaint.bot, BTaint.bot) acc
       ) vars mem
     | _ -> raise (Failure ("handle_init_funcs1: " ^ f)))
  | Some lv ->
    (match f with
     | "array_init"
     | "dbytes_init"
     | "string_init"
     | "contract_init" ->
       let vars = List.fold_left (fun acc arg -> BatSet.union (var_exp arg) acc) (var_lv lv) args in
       BatSet.fold (fun loc acc ->
         update loc (Itv.top, GTaint.bot, BTaint.bot) acc
       ) vars mem
     | "struct_init" -> failwith "struct_init : itvSem.ml" (* must be handled in preprocessing step. *)
     | _ -> raise (Failure ("handle_init_funcs2: " ^ f)))

let handle_abi (lvop,f,args) mem =
  match lvop with
  | None -> mem
  | Some lv -> 
    (match f with
     | "encode" | "decode" | "encodePacked" | "encodeWithSelector" | "encodeWithSignature" ->
        let lub = List.fold_left (fun acc e -> Val.join acc (eval_aexp e mem)) Val.bot args in 
        let v = Val.update_itv Itv.top lub in 
        update (loc_of lv) v mem 
     | _ -> raise (Failure "handle_abi"))

let handle_undefs global ctx_cname (lvop,exp,args) loc mem =
  match exp with
  | Lv (Var (f,_)) when List.mem f Lang.init_funcs ->
    handle_init_funcs global ctx_cname (lvop,f,args) loc mem
  | Lv (MemberAccess (Lv (Var ("abi",_)),f,_,_)) ->
    handle_abi (lvop,f,args) mem 
  | _ ->
    (* same as 'handle_abi' *)
    (match lvop with
     | None -> mem
     | Some lv ->
       let lub = List.fold_left (fun acc e -> Val.join acc (eval_aexp e mem)) Val.bot args in 
       let v = Val.update_itv Itv.top lub in 
       update (loc_of lv) v mem) 

let eval_stmt : Global.t -> id -> func -> Node.t -> Mem.t -> Mem.t
= fun global main_name func node mem ->
  let stmt = find_stmt node (Lang.get_cfg func) in
  let ctx_cname = (Lang.get_finfo func).scope_s in
  match stmt with
  | Assign (lv,e,_) -> assign (lv,e) mem
  | Decl lv ->
    update (loc_of lv) (Itv (V zero, V zero), GTaint.bot, BTaint.bot) mem
  | Call (lvop,e,args,loc,_) (* built-in functions *)
    when FuncMap.is_undef e (List.map get_type_exp args) global.fmap ->
    handle_undefs global ctx_cname (lvop,e,args) loc mem 
  | Call (lvop,e,args,loc,_) -> (* normal calls *)
    handle_fcall global func (lvop,e,args) mem
  | Return (None,_) -> mem
  | Return (Some e,_) -> (* ret_params <- e *)
    let ret_params = get_ret_params func in
    let lv = try params_to_lv ret_params with _ -> assert false in
    if BatString.equal (get_finfo func).scope_s main_name then
      assign (lv, e) mem
    else
      update (loc_of lv) (Itv.top, GTaint.bot, BTaint.bot) mem
  | Assembly (lst,_) ->
    let lst = List.map fst lst in
    Mem.map (fun (x,t) v ->
      if List.mem x lst then
        (Itv.top, Val.gtaint_of v, Val.btaint_of v)
      else v 
    ) mem
  | Skip | Throw | Assume _ | Assert _  -> mem
  | If _ | Seq _ | While _ | Break | Continue -> raise (Failure "eval_stmt")
