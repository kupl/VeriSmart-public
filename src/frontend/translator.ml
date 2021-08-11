open Lang
open Options
open Vocab

(* helper functions *)
let value_of = Yojson.Basic.Util.member
let to_string = Yojson.Basic.Util.to_string
let to_list = Yojson.Basic.Util.to_list
let to_bool = Yojson.Basic.Util.to_bool
let to_int = Yojson.Basic.Util.to_int

let end_of_lines = ref [-1]

let line_indicator : int list -> int -> int
= fun lst byte ->
  let (_,n) =
  List.fold_left (fun (set,line) cur ->
    if not set && byte < cur then (true,line)
    else if set then (set,line)
    else (set,line+1)
  ) (false,1) lst in
  n

let get_loc : Yojson.Basic.t -> int
= fun json ->
  let byte = BatString.split (json |> value_of "src" |> to_string) ":" |> fst |> int_of_string in
  line_indicator !end_of_lines byte

let get_id : Yojson.Basic.t -> int
= fun json -> json |> value_of "id" |> to_int

(* a list of elementary type names *)
let type_list = ["address"; "bool"; "int"; "uint"; "byte"; "fixed"; "ufixed"; "bytes"; "string"]

(**********************)
(**********************)
(***** Translator *****)
(**********************)
(**********************)

(* nodeType: X *)
let rec trans_typeName : Yojson.Basic.t -> typ 
= fun json ->
  let node_typ = value_of "nodeType" json in
  match node_typ with
  | `String "ElementaryTypeName" ->
     EType (trans_elementaryTypeName (json |> value_of "typeDescriptions" |> value_of "typeString" |> to_string))
  | `String "Mapping" -> 
     let key = trans_elementaryTypeName (json |> value_of "keyType" |> value_of "typeDescriptions" |> value_of "typeString" |> to_string) in
     let value = json |> value_of "valueType" |> trans_typeName
     in Mapping (key, value)
  | `String "ArrayTypeName" ->
     let base = json |> value_of "baseType" |> trans_typeName in
     let length = json |> value_of "length" in
     (match length with
      | `Null -> Array (base,None) 
      | len -> Array (base,Some (get_int (trans_expression len))))
  | `String "UserDefinedTypeName" -> 
     let type_string = json |> value_of "typeDescriptions" |> value_of "typeString" |> to_string in
     trans_str_to_typeName type_string
  | `String s -> raise (Failure ("Unsupported: trans_typeName " ^ s))
  | _ -> raise (Failure "Unsupported: trans_typeName")

and trans_struct_type : string -> typ
= fun str ->
  let _ = assert (BatString.starts_with str "struct") in
  let (_, str') = BatString.replace str " pointer" "" in
  let (_, final) = BatString.replace str' "struct " "" in (* struct ContractName.StructName => ContractName.StructName *)
  let (left, right) = BatString.split final "." in (* ContractName.StructName => (ContractName, StructName) *)
  Struct [left;right]

and trans_enum_type : string -> typ
= fun str ->
  let _ = assert (BatString.starts_with str "enum") in
  let (_, str') = BatString.replace str " pointer" "" in
  let (_, final) = BatString.replace str' "enum " "" in (* struct tmp.tmp1 => tmp.tmp1 *)
  let (left, right) = BatString.split final "." in (*tmp.tmp1 => (tmp, tmp1) || tmp1 => ("", tmp1) *)
  Enum right

and trans_mapping : string -> typ
= fun str ->
  let _ = assert (BatString.exists str "mapping") in
  if BatString.ends_with str "]" then trans_array str
  else
    let (left, right) = BatString.split str " => " in (* "mapping(key => val)" -> ( "mapping(key", "val)" )*)
    let left' = BatString.lchop ~n:8 left in (* "mapping(key" -> key *)
    let right' = BatString.rchop ~n:1 right in (* "val)" -> "val" *)
    let key = trans_elementaryTypeName left' in
    let value = trans_str_to_typeName right' in
    Mapping (key, value)

and trans_array : string -> typ
= fun str ->
  let str = BatString.strip str in
  let (left, right) = BatString.rsplit str "[" in (* type[25][30] => (type[25], 30] *)
  let (size, _) = BatString.split right "]" in (* 30] => (30, _) *)
  let t = trans_str_to_typeName left in
  let arr_size = try Some (int_of_string size) with _ -> None in
  Array (t, arr_size)

and trans_lib_type : string -> typ
= fun str ->
  let _ = assert (BatString.exists str "contract" || BatString.exists str "library") in
  let (_, str) = BatString.replace str "contract " "" in
  let (_, name) = BatString.replace str "library " "" in
  Contract name

and trans_function_returns : string -> typ
= fun str ->
  let _ = assert (BatString.exists str "function" && BatString.exists str "returns (") in
  let (_, returns) = BatString.split str "returns (" in
  let returns_typ = BatString.rchop ~n:1 returns in
  if BatString.exists returns_typ "," then trans_tuple ("tuple(" ^ returns_typ ^ ")")
  else trans_str_to_typeName returns_typ 

and trans_tuple : string -> typ
= fun str ->
  let _ = assert (BatString.exists str "tuple") in
  let str' = BatString.chop ~l:6 ~r:1 str in (*tuple(uint,,string,) => uint,,string, *)
  let _ = assert (not (str' = "")) in
  let strs = BatString.split_on_char ',' str' in (*uint,,string, => [uint,"",string,""]*)
  TupleType (List.map trans_str_to_typeName strs)

and trans_str_to_typeName : string -> typ
= fun str ->
  let str' = if BatString.exists str "type(" then BatString.chop ~l:5 ~r:1 str else str in
  let str' = BatString.nreplace ~str:str' ~sub:" storage " ~by:" " in
  let str' = BatString.nreplace ~str:str' ~sub:" ref" ~by:"" in
  let str'' = BatString.nreplace ~str:str' ~sub:" memory" ~by:"" in
  let final = BatString.nreplace ~str:str'' ~sub:" calldata" ~by:"" in
  let final = BatString.nreplace ~str:final ~sub:" super " ~by:"" in
  match final with
    | _ when BatString.ends_with (BatString.nreplace ~str:final ~sub:" pointer" ~by:"") "]" -> trans_array final
    | _ when BatString.exists final "function" -> trans_function_returns final
    | _ when BatString.starts_with final "contract" || BatString.starts_with final "library" -> trans_lib_type final
    | _ when BatString.exists final "mapping" -> trans_mapping final
    | _ when BatString.exists final "tuple" -> trans_tuple final
    | _ when BatString.starts_with final "struct" -> trans_struct_type final
    | _ when BatString.exists final "enum" -> trans_enum_type final
    | _ when BatString.exists final "int_const" -> ConstInt
    | _ when BatString.exists final "rational_const" -> ConstReal
    | _ when BatString.exists final "literal_string" -> ConstString
    | "address payable" -> EType Address
    | _ when List.exists (fun e -> BatString.starts_with final e) type_list -> EType (trans_elementaryTypeName final)
    | _ -> Void

and trans_typeName_Descriptions : Yojson.Basic.t -> typ
= fun json ->
  let tmp = try Some (json |> value_of "typeName" |> trans_typeName) with _ -> None in
  match tmp with
  | Some t -> t
  | None ->
  try
    let type_string = json |> value_of "typeDescriptions" |> value_of "typeString" |> to_string in
      trans_str_to_typeName type_string
  with _ -> Void

(* nodeType: O *)
and trans_elementaryTypeName : string -> elem_typ 
= fun str ->
  match str with
  | s when BatString.exists s "string" -> String 
  | "address" -> Address
  | "bool" -> Bool
  | s when BatString.starts_with s "uint" ->
     let n_str = BatString.tail s 4 in
     if BatString.equal n_str "" then UInt 256
     else UInt (int_of_string n_str)
  | s when BatString.starts_with s "int" ->
     let n_str = BatString.tail s 3 in
     if BatString.equal n_str "" then SInt 256
     else SInt (int_of_string n_str)
  | "byte" -> Bytes 1
  | s when BatString.starts_with s "bytes" ->
     let n_str = BatString.tail s 5 in
     if BatString.equal n_str "" || BatString.exists s " " then DBytes
     else Bytes (int_of_string n_str)
  (* currently, (u)fixed point numbers are unstable in Solidity. *)
  | "fixed" -> raise (Failure "Unsupported: fixed") 
  | "ufixed" -> raise (Failure "Unsupported: ufixed")
  | s -> raise (Failure ("Unsupported: trans_elementraryTypeName-" ^ s))

(* nodeType: X *)
and trans_expression : Yojson.Basic.t -> exp 
= fun json ->
  let typ = trans_typeName_Descriptions json in
  let node_typ = value_of "nodeType" json in
  let loc = get_loc json in
  let nid = get_id json in
  match node_typ with
  | `String "BinaryOperation" ->
     let left = json |> value_of "leftExpression" |> trans_expression in
     let right = json |> value_of "rightExpression" |> trans_expression in
     (match value_of "operator" json with
      | `String "+" -> BinOp (Add, left, right, {eloc=loc; etyp=typ; eid=nid})
      | `String "-" -> BinOp (Sub, left, right, {eloc=loc; etyp=typ; eid=nid})
      | `String "*" ->
         (match left,right with
          | Int n1, Real n2 -> Int (BatBig_int.of_float (BatBig_int.float_of_big_int n1 *. n2))
          | Real n1, Int n2 -> Int (BatBig_int.of_float (n1 *. BatBig_int.float_of_big_int n2))
          | Real n1, BinOp (Exponent, Int n2, Int n3, _) -> Int (BatBig_int.of_float (n1 *. (BatBig_int.float_of_big_int (BatBig_int.pow n2 n3))))
          | _ -> BinOp (Mul, left, right, {eloc=loc; etyp=typ; eid=nid}))
      | `String "/" -> BinOp (Div, left, right, {eloc=loc; etyp=typ; eid=nid})
      | `String "%" -> BinOp (Mod, left, right, {eloc=loc; etyp=typ; eid=nid})
      | `String "**" -> BinOp (Exponent, left, right, {eloc=loc; etyp=typ; eid=nid})
      | `String ">=" -> BinOp (GEq, left, right, {eloc=loc; etyp=typ; eid=nid})
      | `String ">" -> BinOp (Gt, left, right, {eloc=loc; etyp=typ; eid=nid})
      | `String "<=" -> BinOp (LEq, left, right, {eloc=loc; etyp=typ; eid=nid})
      | `String "<" -> BinOp (Lt, left, right, {eloc=loc; etyp=typ; eid=nid})
      | `String "&&" -> BinOp (LAnd, left, right, {eloc=loc; etyp=typ; eid=nid})
      | `String "||" -> BinOp (LOr, left, right, {eloc=loc; etyp=typ; eid=nid})
      | `String "==" -> BinOp (Eq, left, right, {eloc=loc; etyp=typ; eid=nid})
      | `String "!=" -> BinOp (NEq, left, right, {eloc=loc; etyp=typ; eid=nid})
      | `String "<<" -> BinOp (ShiftL, left, right, {eloc=loc; etyp=typ; eid=nid})
      | `String ">>" -> BinOp (ShiftR, left, right, {eloc=loc; etyp=typ; eid=nid})
      | `String "^" -> BinOp (BXor, left, right, {eloc=loc; etyp=typ; eid=nid})
      | `String "&" -> BinOp (BAnd, left, right, {eloc=loc; etyp=typ; eid=nid})
      | `String "|" -> BinOp (BOr, left, right, {eloc=loc; etyp=typ; eid=nid})
      | _ -> raise (Failure "Unsupported: trans_expression1"))
  | `String "Identifier" ->
     (try
       let vname = json |> value_of "name" |> to_string in
       let vinfo = (* the information is not exact at the moment, but will be updated in the preprocessing. *)
         { vloc = loc;
           is_gvar = false;
           vtype = trans_typeName_Descriptions json;
           vvis = Private; 
           vid = (try json |> value_of "id" |> to_int with _ -> assert false);
           refid = (try json |> value_of "referencedDeclaration" |> to_int with _ -> assert false);
           vscope = -1;
           storage = "";
           flag = false; (* should be marked as false *)
           org = vname
         } in
       Lv (Var (vname,vinfo))
     with _ -> assert false)
  | `String "MemberAccess" -> 
     (try
       let exp = json |> value_of "expression" |> trans_expression in
       let id = json |> value_of "memberName" |> to_string in
       let id_info = 
         {dummy_vinfo with 
            refid = (try json |> value_of "referencedDeclaration" |> to_int with _ -> -1);
            vtype = trans_typeName_Descriptions json;
            org = id
         } in
       Lv (MemberAccess (exp,id,id_info,typ))
      with _ -> assert false)
  | `String "IndexAccess" ->
     let base = json |> value_of "baseExpression" |> trans_expression in
     let idx = try json |> value_of "indexExpression" |> trans_expression 
               with _ -> raise (Failure "indexExpression may be null: trans_expression") in
     Lv (IndexAccess (base,Some idx,typ))
  | `String "Literal" ->
     (match value_of "kind" json with
      | `String "number" ->
         let factor =
           (match value_of "subdenomination" json with
            | `Null -> 1.
            | `String "wei" -> 1. 
            | `String "szabo" -> 1e12
            | `String "finney" -> 1e15
            | `String "ether" -> 1e18
            | `String "seconds" -> 1.
            | `String "minutes" -> 60.
            | `String "hours" -> 3600.
            | `String "days" -> 86400. (* 24*3600 *)
            | `String "weeks" -> 604800. (* 7*24*3600 *)
            | `String "years" -> 31536000. (* 365 * 86400 *)
            | _ -> assert false)
         in
         let str = json |> value_of "value" |> to_string in 
         (match typ with
          | ConstInt ->
            let value = float_of_string str in
            Int (BatBig_int.of_float (value *. factor))
          | EType Address ->
            let value = try BatBig_int.of_string str with _ -> BatBig_int.of_float (float_of_string str) in
            Cast (EType Address, Int (BatBig_int.mul value (BatBig_int.of_float factor)))
          | ConstReal ->
            let value = float_of_string str in
            Real (value *. factor)
          | _ -> assert false)
      | `String "bool" ->
         let b = json |> value_of "value" in
         (match b with
          | `String "true" -> True
          | `String "false" -> False
          | _ -> assert false)
      | `String "string" ->
         let s = try json |> value_of "value" |> to_string with _ -> json |> value_of "hexValue" |> to_string in
         Str s
      | `String "hexString" ->
         let s = json |> value_of "hexValue" |> to_string in
         Str s
      | `String s -> raise (Failure ("Unsupported: trans_expression2 - " ^ s ^ " : line " ^ string_of_int loc))
      | _ -> assert false)
  | `String "FunctionCall" ->
     (match value_of "kind" json with
      | `String "functionCall" when json |> value_of "expression" |> value_of "nodeType" = `String "FunctionCallOptions" ->
         let json' = json |> value_of "expression" in
         let _ = assert (value_of "nodeType" json' = `String "FunctionCallOptions") in
         let args = json |> value_of "arguments" |> trans_functionCallArguments in (* should be be json, not json' *)
         let exp = json' |> value_of "expression" |> trans_expression in (* for the rest, should be json', not json *)
         let opnames = json' |> value_of "names" |> to_list |> List.map to_string in
         let ops = json' |> value_of "options" |> to_list |> List.map trans_expression in
         let _ = assert (List.length opnames = List.length ops) in
         let _ = assert (List.length opnames <=2 && List.length ops <=2) in
         let ethop = match BatList.index_of "value" opnames with Some n -> Some (BatList.at ops n) | None -> None in
         let gasop = match BatList.index_of "gas" opnames with Some n -> Some (BatList.at ops n) | None -> None in
         CallTemp (exp, args, ethop, gasop, {eloc=loc; etyp=typ; eid=nid})
      | `String "functionCall" ->
         let exp = json |> value_of "expression" |> trans_expression in
         let args = json |> value_of "arguments" |> trans_functionCallArguments in
         CallTemp (exp,args,None,None,{eloc=loc; etyp=typ; eid=nid})
      | `String "typeConversion" ->
         let arg = json |> value_of "arguments" |> to_list in
         let _ = assert (List.length arg = 1) in
         let exp = trans_expression (List.hd arg)
         in Cast (typ, exp)
      | `String "structConstructorCall" ->
         let exp = json |> value_of "expression" |> trans_expression in
         let args = json |> value_of "arguments" |> trans_functionCallArguments in
         let names = json |> value_of "names" |> to_list in
         if List.length names = 0 then (* member names are not given *)
           CallTemp (Lv (Var ("struct_init",dummy_vinfo)), exp::args, None, None, {eloc=loc; etyp=typ; eid=nid})
         else
           let args_names = List.map (fun name -> Lv (Var (to_string name, dummy_vinfo))) names in
           CallTemp (Lv (Var ("struct_init2",dummy_vinfo)), exp::args_names@args, None, None, {eloc=loc; etyp=typ; eid=nid})
      | `String s -> raise (Failure ("Unsupported: trans_expression3-"^s))
      | _ -> assert false)
  | `String "UnaryOperation" ->
     let sub = json |> value_of "subExpression" |> trans_expression in
     (match value_of "operator" json with
      | `String "+" -> UnOp (Pos,sub,typ)
      | `String "-" -> UnOp (Neg,sub,typ) 
      | `String "!" -> UnOp (LNot,sub,typ)
      | `String "~" -> UnOp (BNot,sub,typ)
      | `String "++" ->
         let pre = json |> value_of "prefix" |> to_bool in
         IncTemp (sub,pre,loc)
      | `String "--" ->
         let pre = json |> value_of "prefix" |> to_bool in
         DecTemp (sub,pre,loc)
      | _ -> raise (Failure "Unsupported: trans_expression4"))
  | `String "TupleExpression" ->
     let tuples = json |> value_of "components" |> to_list in
     if is_array typ then Lv (Tuple ((List.map (fun e -> try Some (trans_expression e) with _ -> None) tuples), typ)) else
     if List.length tuples = 1 then trans_expression (List.hd tuples)
     else Lv (Tuple ((List.map (fun e -> try Some (trans_expression e) with _ -> None) tuples), typ))
  | `String "Conditional" -> (* cond ? t : f *)
     let cond = json |> value_of "condition" |> trans_expression in
     let t = json |> value_of "trueExpression" |> trans_expression in
     let f = json |> value_of "falseExpression" |> trans_expression in
     CondTemp (cond,t,f,typ,loc)
  | `String "NewExpression" ->
     if is_array typ then Lv (Var ("array_init",dummy_vinfo)) else
     if is_contract typ then Lv (Var ("contract_init_"^get_name_userdef typ,dummy_vinfo)) else
     if is_struct typ then Lv (Var ("struct_init_"^get_name_userdef typ, dummy_vinfo)) else
     if is_enum typ then Lv (Var ("enum_init_"^get_name_userdef typ, dummy_vinfo)) else
     if is_dbytes typ then Lv (Var ("dbytes_init",dummy_vinfo)) else
     if is_string typ then Lv (Var ("string_init",dummy_vinfo))
     else raise (Failure "NewExpression")
  | `String "Assignment" ->
     let lv = json |> value_of "leftHandSide" |> trans_expression |> exp_to_lv in
     let exp = json |> value_of "rightHandSide" |> trans_expression in
     let typ = json |> value_of "leftHandSide" |> trans_typeName_Descriptions in 
     let op = value_of "operator" json in 
     (match op with
       | `String "=" -> AssignTemp (lv, exp, loc)
       | `String "+=" -> AssignTemp (lv, BinOp (Add,Lv lv,exp, {eloc=loc; etyp=typ; eid=nid}), loc)
       | `String "-=" -> AssignTemp (lv, BinOp (Sub,Lv lv,exp, {eloc=loc; etyp=typ; eid=nid}), loc)
       | `String "*=" -> AssignTemp (lv, BinOp (Mul,Lv lv,exp, {eloc=loc; etyp=typ; eid=nid}), loc)
       | `String "/=" -> AssignTemp (lv, BinOp (Div,Lv lv,exp, {eloc=loc; etyp=typ; eid=nid}), loc)
       | `String "%=" -> AssignTemp (lv, BinOp (Mod,Lv lv,exp, {eloc=loc; etyp=typ; eid=nid}), loc)
       | `String "|=" -> AssignTemp (lv, BinOp (BOr,Lv lv,exp, {eloc=loc; etyp=typ; eid=nid}), loc)
       | `String "^=" -> AssignTemp (lv, BinOp (BXor,Lv lv,exp, {eloc=loc; etyp=typ; eid=nid}), loc)
       | `String "&=" -> AssignTemp (lv, BinOp (BAnd,Lv lv,exp, {eloc=loc; etyp=typ; eid=nid}), loc)
       | `String "<<=" -> AssignTemp (lv, BinOp (ShiftL,Lv lv,exp, {eloc=loc; etyp=typ; eid=nid}), loc)
       | `String ">>=" -> AssignTemp (lv, BinOp (ShiftR,Lv lv,exp, {eloc=loc; etyp=typ; eid=nid}), loc)
       | _ -> raise (Failure " Unsupported: trans_expression5"))
  | `String "ElementaryTypeNameExpression" ->
     (* json AST from solc is slightly differnt per version. *)
     (try
       let etyp = json |> value_of "typeName" |> to_string |> trans_elementaryTypeName in
       ETypeName etyp
     with
       _ ->
       let etyp = json |> value_of "typeName" |> value_of "name" |> to_string |> trans_elementaryTypeName in
       ETypeName etyp)
  | `String s ->
     failwith ("trans_expression6-" ^ s ^ "@" ^ string_of_int loc)
  | _ -> failwith "Unsupported: trans_expression7"

(* nodeType: X *)  
and trans_functionCallArguments : Yojson.Basic.t -> exp list
= fun json ->
  match json with 
  | `List l ->
     List.fold_left (fun acc j -> acc @ [(trans_expression j)]) [] l
  | `Null -> [] (* no arguments: `Null, not `List [] *)
  | _ -> assert false

(* nodeType : O *)
and trans_expressionStatement : Yojson.Basic.t -> stmt
= fun json ->
  let _ = assert (value_of "nodeType" json = `String "ExpressionStatement") in
  let json' = value_of "expression" json in
  let loc = get_loc json' in
  let nid = get_id json' in
  match value_of "nodeType" json' with
  | `String "FunctionCall" ->
     (match value_of "kind" json' with
      | `String "functionCall" when json' |> value_of "expression" |> value_of "nodeType" = `String "FunctionCallOptions" ->
         let json'' = json' |> value_of "expression" in
         let _ = assert (value_of "nodeType" json'' = `String "FunctionCallOptions") in
         let args = json' |> value_of "arguments" |> trans_functionCallArguments in (* should be be json', not json'' *)
         let exp = json'' |> value_of "expression" |> trans_expression in (* for the rest, should be json'', not json' *)
         let opnames = json'' |> value_of "names" |> to_list |> List.map to_string in
         let ops = json'' |> value_of "options" |> to_list |> List.map trans_expression in
         let _ = assert (List.length opnames = List.length ops) in
         let _ = assert (List.length opnames <=2 && List.length ops <=2) in
         let ethop = match BatList.index_of "value" opnames with Some n -> Some (BatList.at ops n) | None -> None in
         let gasop = match BatList.index_of "gas" opnames with Some n -> Some (BatList.at ops n) | None -> None in
         Call (None, exp, args, ethop, gasop, get_loc json', json' |> value_of "id" |> to_int)
      | `String "functionCall" ->
         let exp = json' |> value_of "expression" |> trans_expression in (* function name *)
         let args = json' |> value_of "arguments" |> trans_functionCallArguments in
         (* Call (None, exp, args) *)
           (* Built-in function checkers. Lists need to be updated. *)
           if is_require exp then 
             (assert (List.length args = 1 || List.length args = 2);
              If (List.hd args, Skip, Throw)) else
           if is_assert exp then
             (assert (List.length args = 1);
              Seq (Assert (List.hd args, "default", get_loc json'), If (List.hd args, Skip, Throw)))
           else Call (None, exp, args, None, None, get_loc json', json' |> value_of "id" |> to_int) (* normal case *) 
      | _ -> raise (Failure "Unsupported: trans_expressionStatement1"))
  | `String "Assignment" ->
     let lv = json' |> value_of "leftHandSide" |> trans_expression |> exp_to_lv in
     let exp = json' |> value_of "rightHandSide" |> trans_expression in
     let typ = json' |> value_of "leftHandSide" |> trans_typeName_Descriptions in 
     let op = value_of "operator" json' in 
       (match op with
       | `String "=" -> Assign (lv, exp, loc)
       | `String "+=" -> Assign (lv, BinOp (Add,Lv lv,exp, {eloc=loc; etyp=typ; eid=nid}), loc)
       | `String "-=" -> Assign (lv, BinOp (Sub,Lv lv,exp, {eloc=loc; etyp=typ; eid=nid}), loc)
       | `String "*=" -> Assign (lv, BinOp (Mul,Lv lv,exp, {eloc=loc; etyp=typ; eid=nid}), loc)
       | `String "/=" -> Assign (lv, BinOp (Div,Lv lv,exp, {eloc=loc; etyp=typ; eid=nid}), loc)
       | `String "%=" -> Assign (lv, BinOp (Mod,Lv lv,exp, {eloc=loc; etyp=typ; eid=nid}), loc)
       | `String "|=" -> Assign (lv, BinOp (BOr,Lv lv,exp, {eloc=loc; etyp=typ; eid=nid}), loc)
       | `String "^=" -> Assign (lv, BinOp (BXor,Lv lv,exp, {eloc=loc; etyp=typ; eid=nid}), loc)
       | `String "&=" -> Assign (lv, BinOp (BAnd,Lv lv,exp, {eloc=loc; etyp=typ; eid=nid}), loc)
       | `String "<<=" -> Assign (lv, BinOp (ShiftL,Lv lv,exp, {eloc=loc; etyp=typ; eid=nid}), loc)
       | `String ">>=" -> Assign (lv, BinOp (ShiftR,Lv lv,exp, {eloc=loc; etyp=typ; eid=nid}), loc)
       | _ -> raise (Failure " Unsupported: trans_expressionStatement2"))
  | `String "UnaryOperation" ->
     let op = value_of "operator" json' in
     (match op with 
     | `String "++" ->
        let sub = json' |> value_of "subExpression" |> trans_expression in
        let lv = exp_to_lv sub in
        Assign (lv, BinOp (Add,Lv lv,Int (BatBig_int.of_int 1),{eloc=loc; etyp=get_type_lv lv; eid=nid}), loc)
     | `String "--" ->
        let sub = json' |> value_of "subExpression" |> trans_expression in
        let lv = exp_to_lv sub in
        Assign (lv, BinOp (Sub,Lv lv,Int (BatBig_int.of_int 1),{eloc=loc; etyp=get_type_lv lv; eid=nid}), loc)
     | `String "delete" ->
        let sub = json' |> value_of "subExpression" |> trans_expression in
        let lv = Var ("delete",dummy_vinfo) in
        Call (None, Lv lv, [sub], None, None, loc, nid)
     | `String s -> raise (Failure ("Unsupported Unary Op: " ^ s))
     | _ -> assert false)
  | `String "Identifier" -> Skip
  | `String "BinaryOperation" -> Skip
  | `String "IndexAccess" -> Skip
  | `String "Conditional" -> (* cond ? t : f *)
     let cond = json' |> value_of "condition" |> trans_expression in
     (* since json generated by solc does not have proper structure,
      * this additional manipulation step should be forced. *)
     let t = `Assoc [("expression", value_of "trueExpression" json'); ("nodeType", `String "ExpressionStatement")] |> trans_expressionStatement in
     let f = `Assoc [("expression", value_of "falseExpression" json'); ("nodeType", `String "ExpressionStatement")] |> trans_expressionStatement in
     If (cond, t, f)
  | `String "TupleExpression" -> Skip
  | `String "FunctionCallOptions" -> Skip (* e.g., "msg.sender.call{value: msg.value-amountEth};" does nothing. E.g., '("")' should be appended. *)
  | `String s -> raise (Failure ("Unsupported: trans_expressionStatement3 - " ^ s ^ " : line " ^ string_of_int loc))
  | _ -> assert false

(* nodeType: X *)
let trans_visibility : Yojson.Basic.t -> visibility
= fun json ->
  match json with
  | `String "public" -> Public 
  | `String "internal" -> Internal
  | `String "external" -> External
  | `String "private" -> Private
  | _ -> raise (Failure "trans_visibility")

(* nodeType : O *)
let trans_variable_declaration : Yojson.Basic.t -> var_decl
= fun json ->
  let _ = assert (value_of "nodeType" json = `String "VariableDeclaration") in
  let vname = json |> value_of "name" |> to_string in
  let vinfo =
    { vloc = json |> get_loc;
      is_gvar = json |> value_of "stateVariable" |> to_bool;
      vtype = trans_typeName_Descriptions json;
      vvis = json |> value_of "visibility" |> trans_visibility;
      vid = (try json |> value_of "id" |> to_int with _ -> assert false);
      refid = (try json |> value_of "id" |> to_int with _ -> assert false); (* for the declarations, assign themselves. *)
      vscope = (try json |> value_of "scope" |> to_int with _ -> assert false);
      storage = (try json |> value_of "storageLocation" |> to_string with _ -> assert false);
      flag = true; (* true only for variable declarations *)
      org = vname
    } in
  (vname,vinfo)

let rec trans_yul_exp : (string * int) list -> int -> Yojson.Basic.t -> (id * int) list
= fun ref ast_id json ->
  let node_typ = json |> value_of "nodeType" in
  match node_typ with
  | `String "YulIdentifier" ->
     let name = json |> value_of "name" |> to_string in
     (* Locals in assembly block do not have references in external blocks. Thus, assign assembly block's AST id. *)
     let refid = try List.assoc (json |> value_of "src" |> to_string) ref with Not_found -> ast_id in
     [(name, refid)]
  | `String "YulLiteral" -> []
  | `String "YulFunctionCall" ->
     (* let fname = json |> value_of "functionName" |> value_of "name" |> to_string in *)
     let args = json |> value_of "arguments" |> to_list in
     let args = List.fold_left (fun acc arg -> acc @ (trans_yul_exp ref ast_id arg)) [] args in
     args
  | _ -> failwith "trans_yul_exp"

let trans_yul_stmt : Yojson.Basic.t -> (string * int) list -> int -> (id * int) list
= fun json ref ast_id ->
  let node_typ = json |> value_of "nodeType" in
  match node_typ with
  | `String "YulVariableDeclaration" ->
     let lhs = json |> value_of "variables" |> to_list in
     let lhs =
       List.map (fun j ->
         let name = j |> value_of "name" |> to_string in
         (* let _ = print_endline name in
         let _ = print_endline (j |> value_of "src" |> to_string) in
         let _ = print_endline (Vocab.string_of_list (fun (src,refid) -> src ^ " : " ^ string_of_int refid) ref) in *)
         (* Locals in assembly block do not have references in external blocks. Thus, assign assembly block's AST id. *)
         let refid = try List.assoc (j |> value_of "src" |> to_string) ref with Not_found -> ast_id 
         in
         (name,refid)
       ) lhs in
     let rhs = json |> value_of "value" |> trans_yul_exp ref ast_id in
     rhs@lhs
  | `String "YulAssignment" ->
     let lhs = json |> value_of "variableNames" |> to_list in
     let lhs =
       List.map (fun j ->
         let name = j |> value_of "name" |> to_string in
         let refid = List.assoc (j |> value_of "src" |> to_string) ref in
         (name,refid)
       ) lhs in
     let rhs = json |> value_of "value" |> trans_yul_exp ref ast_id in
     rhs@lhs
  | `String "YulExpressionStatement" ->
     json |> value_of "expression" |> trans_yul_exp ref ast_id
  | `String s -> failwith ("trans_yul_stmt : " ^ s ^ " @ " ^ string_of_int (get_loc json))
  | _ -> assert false

let trans_yul_block : Yojson.Basic.t -> (id * int) list
= fun json ->
  let _ = assert (value_of "nodeType" json = `String "InlineAssembly") in
  let ext_refs = json |> value_of "externalReferences" |> to_list in
  let ext_refs =
    List.map (fun er ->
      (er |> value_of "src" |> to_string,  er |> value_of "declaration" |> to_int)
    ) ext_refs in
  let ast_id = json |> value_of "id" |> to_int in
  let j = value_of "AST" json in
  let _ = assert (value_of "nodeType" j = `String "YulBlock") in
  let statements = j |> value_of "statements" |> to_list in
  List.fold_left (fun acc j' ->
    acc @ (trans_yul_stmt j' ext_refs ast_id)
  ) [] statements


(* nodeType : X *)
let rec trans_statement : Yojson.Basic.t -> stmt
= fun json ->
  let node_typ = value_of "nodeType" json in
  let loc = get_loc json in
  match node_typ with
  | `String "VariableDeclarationStatement" -> (* declaration := initialValue *)
     let decl = json |> value_of "declarations" |> to_list in
     let _ = assert (List.length decl > 0) in
     let lv = (
       if List.length decl = 1 then   (* uint a; *)
         let var_decl = List.hd decl in
         let (vname,vinfo) = trans_variable_declaration var_decl in
         Var (vname,vinfo) 
       else  (* (a, b, c); *)
         let elst =  List.map (fun v -> 
           try
             let (vname,vinfo) = trans_variable_declaration v in
             Some (Lv (Var (vname, vinfo)))
           with _ -> None
         ) decl in
         Tuple (elst, Void)
     ) in
     (match value_of "initialValue" json with
      | `Null -> Decl lv
      | exp -> Assign (lv, trans_expression exp, loc))
  | `String "ExpressionStatement" -> trans_expressionStatement json
  | `String "PlaceholderStatement" -> PlaceHolder
  | `String "ForStatement" ->
     let init = try json |> value_of "initializationExpression" |> trans_statement with _ -> Skip in (* for ( ;cond;a++) *)
     let cond = try json |> value_of "condition" |> trans_expression with _ -> True in (* for (init; ;a++) *)
     let body_wo_last = json |> value_of "body" |> trans_statement in 
     let body_last = try json |> value_of "loopExpression" |> trans_statement with _ -> Skip in (* for (init;cond; ) *)
     let body = Seq (body_wo_last,body_last) in 
     Seq (init,While (cond,body))
  | `String "WhileStatement" ->
     let cond = json |> value_of "condition" |> trans_expression in
     let body = json |> value_of "body" |> trans_statement in
     While (cond,body)
  | `String "DoWhileStatement" ->
     let cond = json |> value_of "condition" |> trans_expression in
     let body = json |> value_of "body" |> trans_statement in
     Seq (body, While (cond,body))
  | `String "IfStatement" ->
     let cond = json |> value_of "condition" |> trans_expression in
     let tbody = json |> value_of "trueBody" |> trans_statement in
     let fbody = 
       match json |> value_of "falseBody" with
       | `Null -> Skip
       | fb -> trans_statement fb in
     If (cond,tbody,fbody)
  | `String "Return" ->
     (match value_of "expression" json with
      | `Null -> Return (None, loc)
      | exp -> Return (Some (trans_expression exp), loc))
  | `String "Throw" -> Throw
  | `String "Block" -> trans_block json
  | `String "EmitStatement" -> Skip
  | `String "Break" -> Break
  | `String "Continue" -> Continue
  | `String "InlineAssembly" ->
     (try
        let ext_refs = json |> value_of "externalReferences" |> to_list in
        let var_refid_pairs =
          List.map (fun j ->
            match j with
            | `Assoc ((s,j')::[]) -> (s, j' |> value_of "declaration" |> to_int)
            | _ -> raise (Failure "InlineAssembly")
        ) ext_refs in
        Assembly (var_refid_pairs, loc)
     with _ ->
       let var_refid_pairs = trans_yul_block json in
       Assembly (var_refid_pairs, loc))
  | `String "UncheckedBlock" -> failwith ("Unsupported: UncheckedBlock, line " ^ string_of_int loc)
     (* let statements = json |> value_of "statements" |> to_list in
     List.fold_left (fun acc j ->
       Seq (acc, trans_statement j)
     ) Skip statements *)
  | `String "TryStatement" -> failwith ("Unsupported: TryStatement, line " ^ string_of_int loc)
  | `String s -> raise (Failure ("Unsupported: trans_statement - " ^ s ^ " : line " ^ string_of_int loc))
  | _ -> assert false

(* nodeType : O *)
and trans_block : Yojson.Basic.t -> stmt
= fun json ->
  let _ = assert (value_of "nodeType" json = `String "Block") in
  let statements = json |> value_of "statements" |> to_list in
  List.fold_left (fun acc j ->
    let new_stmt = trans_statement j in
    Seq (acc, new_stmt)
  ) Skip statements 

(* usual: defined modifiers appear as invocations *)
(* unusual: consturctor invocations appear as modifiers *)
let is_usual_modifier: string list -> Yojson.Basic.t -> bool
= fun cnames json ->
  let _ = assert (value_of "nodeType" json = `String "ModifierInvocation") in
  let modname = json |> value_of "modifierName" |> value_of "name" |> to_string in
  not (List.mem modname cnames)

(* nodeType: O *)
let trans_modifierInvocation : Yojson.Basic.t -> mod_call
= fun json ->
  let _ = assert (value_of "nodeType" json = `String "ModifierInvocation") in
  let name = json |> value_of "modifierName" |> value_of "name" |> to_string in
  let args = json |> value_of "arguments" |> trans_functionCallArguments in
  let loc = get_loc json in
  (name, args, loc)

(* generate Constructor call *)
let trans_inheritanceSpecifier : Yojson.Basic.t -> mod_call
= fun json ->
  let _ = assert (value_of "nodeType" json = `String "InheritanceSpecifier") in
  let name = json |> value_of "baseName" |> value_of "name" |> to_string in
  let args = json |> value_of "arguments" |> trans_functionCallArguments in
  let loc = get_loc json in
  (name, args, loc)

let resolve_cnstr_calls : mod_call list -> mod_call list ->
                          mod_call list
= fun inherit_calls mod_calls ->
  (* In solc 0.4x, mod_calls has the priority over the inherit_calls. *)
  (* In recent solc, specifying arguments for both places is an error. *)
  (* E.g.,
   * Inherit: A(5) B(3), Mod: A(8) C(7) => B(3) A(8) C(7) *)
  let combined = inherit_calls @ mod_calls in
  let combined = List.rev combined in (* rev list to give the priority to mod_calls *)
  List.fold_left (fun acc m ->
    let b = List.exists (fun (x,_,_) -> x = triple_fst m) acc in
    if b then acc
    else m::acc
  ) [] combined

let param_cnt = ref 0
let param_name = "Param"
let gen_param_name () =
  param_cnt:=!param_cnt+1;
  param_name ^ (string_of_int !param_cnt)

(* nodeType: O *)
let trans_parameterList : Yojson.Basic.t -> param list
= fun json ->
  let _ = assert (value_of "nodeType" json = `String "ParameterList") in
  let parameters = json |> value_of "parameters" |> to_list in (* 0 parameters => `List [] *)
  let reversed_params = 
    List.fold_left (fun acc j ->
      let (vname,vinfo) = trans_variable_declaration j in
      let vname = if BatString.equal vname "" then gen_param_name () else vname in 
      (vname, vinfo)::acc 
    ) [] parameters in
  let params = List.rev reversed_params
  in params

let trans_isConstructor : Yojson.Basic.t -> bool
= fun j ->
  let _ = assert (value_of "nodeType" j = `String "FunctionDefinition") in
  try
    j |> value_of "isConstructor" |> to_bool (* solc 0.4x *)
  with _ -> (* solc 0.5x *)
   (match value_of "kind" j with
    | `String "constructor" -> true
    | `String "function" -> false
    | `String "fallback" -> false
    | `String "receive" -> false
    | `String s -> failwith ("trans_isConstructor: " ^ s)
    | _ -> assert false)

let trans_payable : Yojson.Basic.t -> bool
= fun j ->
  let _ = assert (value_of "nodeType" j = `String "FunctionDefinition") in
  try
    j |> value_of "payable" |> to_bool (* 0.4x *)
  with _ -> (* 0.5x *)
    (match value_of "stateMutability" j with
     | `String "payable" -> true
     | `String "nonpayable" -> false
     | `String "view" -> false
     | `String "pure" -> false
     | _ -> failwith "stateMutability")

(* nodeType : O *)
let trans_contractDefinition : string list -> Yojson.Basic.t -> contract
= fun cnames json ->
  let cid = json |> value_of "name" |> to_string in
  let contract_parts = json |> value_of "nodes" |> to_list in
  let cinfo =
    { numid = json |> value_of "id" |> to_int;
      inherit_order = List.map to_int (json |> value_of "linearizedBaseContracts" |> to_list);
      lib_typ_lst = [];
      ckind = json |> value_of "contractKind" |> to_string
    } in
  let base_contracts = json |> value_of "baseContracts" |> to_list in (* A is B,C,D => base_contracts : [B; C; D] *)
  let cnstr_calls_inherit =
    List.fold_left (fun acc base ->
      let cnstr_call = trans_inheritanceSpecifier base in
      if List.length (triple_snd cnstr_call) > 0 then
        acc @ [cnstr_call] (* constructors are called starting from parents *)
      else acc
    ) [] base_contracts in
  (* NOTE: lists are stored in a reversed order *)
  let (cid, gvar_decls, structs, enums, func_defs, cinfo) =
    List.fold_left (fun (cid, gvar_decls, structs, enums, func_defs, cinfo) j ->
      let node_typ = value_of "nodeType" j in
      match node_typ with
      | `String "VariableDeclaration" ->
         let (vname,vinfo) = trans_variable_declaration j in
         let expop =
           (match j |> value_of "value" with
            | `Null -> None
            | exp -> Some (trans_expression exp)) in
         let decl = (vname, expop, vinfo) in
         (cid, decl::gvar_decls, structs, enums, func_defs, cinfo)
      | `String "EventDefinition" -> (* Event is modeled as a function with internal visibility and a skip body *)
         let fname = j |> value_of "name" |> to_string in
         let params = j |> value_of "parameters" |> trans_parameterList in
         let finfo =
           { is_constructor = false;
             is_payable = false;
             is_modifier = false;
             mod_list = [];
             mod_list2 = [];
             ret_param_loc = (-1);
             fvis = Internal;
             fid = j |> value_of "id" |> to_int;
             scope = cinfo.numid;
             scope_s = cid; (* to be filled by preprocessor *)
             org_scope_s = cid;
             cfg = empty_cfg
           } in
         let stmt = Skip in
         let func = (fname,params,[],stmt,finfo) in
         (cid, gvar_decls, structs, enums, func::func_defs, cinfo)
      | `String "EnumDefinition" ->
         let name = j |> value_of "name" |> to_string in
         let members = List.map (fun j' -> j' |> value_of "name" |> to_string) (j |> value_of "members" |> to_list) in
         let enum = (name,members) in
         (cid, gvar_decls, structs, enums@[enum], func_defs, cinfo)
      | `String "StructDefinition" ->
         let name = j |> value_of "canonicalName" |> to_string in
         let decls = List.map trans_variable_declaration (j |> value_of "members" |> to_list) in
         let structure = (name,decls) in 
         (cid, gvar_decls, structure::structs, enums, func_defs, cinfo)
      | `String "UsingForDirective" -> 
         let lib_name = j |> value_of "libraryName" |> value_of "name" |> to_string in
         let typ = trans_typeName_Descriptions j in
         let cinfo = {cinfo with lib_typ_lst = (lib_name,typ)::cinfo.lib_typ_lst} in
         (cid, gvar_decls, structs, enums, func_defs, cinfo)
      | `String "FunctionDefinition" ->
         let is_constructor = trans_isConstructor j in
         let fname = j |> value_of "name" |> to_string in
         let fname = if is_constructor then cid else if fname = "" then "@fallback" else fname in
         let params = j |> value_of "parameters" |> trans_parameterList in
         let ret_params = j |> value_of "returnParameters" |> trans_parameterList in
         let stmt =
           if j |> value_of "implemented" |> to_bool then j |> value_of "body" |> trans_block
           else Skip (* function without definitions *)
         in
         let modifiers = j |> value_of "modifiers" |> to_list in
         (* executed in the order of usual mod call => constructor mod call *)
         let mod_calls =
           List.fold_left (fun acc j' ->
             if is_usual_modifier cnames j' then acc @ [(trans_modifierInvocation j')]
             else acc
           ) [] modifiers
         in
         let cnstr_calls_mod =
           List.fold_left (fun acc j' ->
             if not (is_usual_modifier cnames j') then acc @ [(trans_modifierInvocation j')]
             else acc
           ) [] modifiers
         in
         let cnstr_calls = resolve_cnstr_calls cnstr_calls_inherit cnstr_calls_mod in
         let finfo =
           { is_constructor = is_constructor;
             is_payable = trans_payable j;
             is_modifier = false;
             mod_list = mod_calls;
             mod_list2 = if is_constructor then cnstr_calls else [];
             ret_param_loc = j |> value_of "returnParameters" |> get_loc;
             fvis = j |> value_of "visibility" |> trans_visibility;
             fid = j |> value_of "id" |> to_int;
             scope = cinfo.numid;
             scope_s = cid;
             org_scope_s = cid;
             cfg = empty_cfg
           }
         in
         let func = (fname, params, ret_params, stmt, finfo) in
         (cid, gvar_decls, structs, enums, func::func_defs, cinfo)
      | `String "ModifierDefinition" ->
         let fname = j |> value_of "name" |> to_string in
         let params = j |> value_of "parameters" |> trans_parameterList in
         let finfo =
           { is_constructor = false;
             is_payable = false;
             is_modifier = true;
             mod_list = []; (* no modifier invocations in modifier definition *)
             mod_list2 = []; (* same as above *)
             ret_param_loc = (-1);
             fvis = j |> value_of "visibility" |> trans_visibility;
             fid = j |> value_of "id" |> to_int;
             scope = cinfo.numid;
             scope_s = cid;
             org_scope_s = cid;
             cfg = empty_cfg
           } in
         let stmt = j |> value_of "body" |> trans_block in
         let func = (fname, params, [], stmt, finfo) in
         (cid, gvar_decls, structs, enums, func::func_defs, cinfo)
      | _ -> raise (Failure "Unsupported : trans_contractDefinition")
    ) (cid, [], [], [], [], cinfo) contract_parts in
  let (gvar_decls, func_defs) = (List.rev gvar_decls, List.rev func_defs) in 
  let b = List.exists (fun (_,_,_,_,finfo) -> finfo.is_constructor) func_defs in
    if b then (cid, gvar_decls, structs, enums, func_defs, cinfo)
    else
      (* make a new constructor if does not exist *)
      let fname = cid in
      let params = [] in
      let cnstr_calls = resolve_cnstr_calls cnstr_calls_inherit [] in
      let finfo =
        {is_constructor = true;
         is_payable = false;
         is_modifier = false;
         mod_list = []; mod_list2 = cnstr_calls; ret_param_loc = (-1);
         fvis = Public; fid = (-1);
         scope = cinfo.numid; scope_s = cid; org_scope_s = cid; cfg = empty_cfg}
      in
      let cnstr = (fname, params, [], Skip, finfo) in
      (cid, gvar_decls, structs, enums, cnstr::func_defs, cinfo) 

let translate : Yojson.Basic.t -> pgm
= fun json ->
  let _ = assert (value_of "nodeType" json = `String "SourceUnit") in
  let l = json |> value_of "nodes" |> to_list in (* 0 nodes => `List [] *)
  let l' = List.filter (fun j -> value_of "nodeType" j = `String "ContractDefinition") l in
  let cnames = List.map (fun json -> json |> value_of "name" |> to_string) l' in
  List.fold_left (fun acc j ->
    let node_typ = value_of "nodeType" j in
    (match node_typ with
     | `String "ContractDefinition" ->
       acc @ [trans_contractDefinition cnames j]
     | _ -> acc) (* Skip PragmaDirectve, and ImportDirective *)
  ) [] l

let run json = translate json
