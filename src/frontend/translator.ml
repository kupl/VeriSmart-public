open Lang
open Options

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
    if not set && byte < cur then (true,line) else 
    if set then (set,line)
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
  let (_, final) = BatString.replace str' "struct " "" in (* struct tmp.tmp1 => tmp.tmp1 *)
  let (left, right) = BatString.split final "." in (*tmp.tmp1 => (tmp, tmp1) || tmp1 => ("", tmp1) *)
  Struct right

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
          | ConstInt | EType Address ->
            let value = try BatBig_int.of_string str with _ -> BatBig_int.of_float (float_of_string str) in
            Int (BatBig_int.mul value (BatBig_int.of_float factor))
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
         let s = 
           try json |> value_of "value" |> to_string 
           with _ -> json |> value_of "hexValue" |> to_string in
         Str s
      | _ -> raise (Failure "Unsupported: trans_expression2"))
  | `String "FunctionCall" ->
     (match value_of "kind" json with
      | `String "typeConversion" ->
         let arg = json |> value_of "arguments" |> to_list in
         let _ = assert (List.length arg = 1) in
         let exp = trans_expression (List.hd arg)
         in Cast (typ, exp)
      | `String "functionCall" ->
         let exp = json |> value_of "expression" |> trans_expression in
         let args = json |> value_of "arguments" |> trans_functionCallArguments in
         CallTemp (exp,args,{eloc=loc; etyp=typ; eid=nid})
      | `String "structConstructorCall" ->
         let exp = json |> value_of "expression" |> trans_expression in
         let args = json |> value_of "arguments" |> trans_functionCallArguments in
         let names = json |> value_of "names" |> to_list in
         if List.length names = 0 then (* member names are not given *)
           CallTemp (Lv (Var ("struct_init",dummy_vinfo)), exp::args, {eloc=loc; etyp=typ; eid=nid})
         else
           let args_names = List.map (fun name -> Lv (Var (to_string name, dummy_vinfo))) names in
           CallTemp (Lv (Var ("struct_init2",dummy_vinfo)), exp::args_names@args, {eloc=loc; etyp=typ; eid=nid})
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
  | `String "Conditional" ->
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
    let etyp = json |> value_of "typeName" |> to_string |> trans_elementaryTypeName in
    ETypeName etyp
  | `String s -> raise (Failure ("trans_expression6-"^s))
  | _ -> raise (Failure "Unsupported: trans_expression7")

(* nodeType: X *)  
and trans_functionCallArguments : Yojson.Basic.t -> exp list
= fun json ->
  match json with 
  | `List l ->
     let reversed_args =
       List.fold_left (fun acc j ->
         (trans_expression j)::acc
       ) [] l
     in 
     List.rev (reversed_args)
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
              Seq (Assert (List.hd args, get_loc json'), If (List.hd args, Skip, Throw)))
           else Call (None, exp, args, get_loc json', json' |> value_of "id" |> to_int) (* normal case *) 
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
        Call (None, Lv lv, [sub], loc, nid)
     | `String s -> raise (Failure ("Unsupported Unary Op: " ^ s))
     | _ -> assert false)
  | `String "Identifier" -> Skip
  | `String "BinaryOperation" -> Skip
  | `String "IndexAccess" -> Skip
  | `String "Conditional" ->
     let cond = json' |> value_of "condition" |> trans_expression in
     (* since json generated by solc does not have proper structure,
      * this additional manipulation step should be forced. *)
     let t = `Assoc [("expression", value_of "trueExpression" json'); ("nodeType", `String "ExpressionStatement")] |> trans_expressionStatement in
     let f = `Assoc [("expression", value_of "falseExpression" json'); ("nodeType", `String "ExpressionStatement")] |> trans_expressionStatement in
     If (cond, t, f)
  | `String "TupleExpression" -> Skip
  | `String s -> raise (Failure ("Unsupported: trans_expressionStatement3 - " ^ s))
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
      storage = (try json |> value_of "storageLocation" |> to_string with _ -> assert false);
      flag = true; (* true only for variable declarations *)
      org = vname
    } in
  (vname,vinfo)

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
  | `String "PlaceholderStatement" -> Skip
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
     let lst = json |> value_of "externalReferences" |> to_list in
     let var_refid_pairs =
       List.map (fun j ->
         match j with
         | `Assoc ((s,j')::[]) -> (s, j' |> value_of "declaration" |> to_int)
         | _ -> raise (Failure "InlineAssembly")
       ) lst
     in
     Assembly (var_refid_pairs, get_loc json) 
  | `String s -> raise (Failure ("Unsupported: trans_statement- " ^ s))
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

(* nodeType: O *)
let trans_modifierInvocation : Yojson.Basic.t -> bool * stmt (* true if mod call, false if cnstr call *)
= fun json ->
  let _ = assert (value_of "nodeType" json = `String "ModifierInvocation") in
  let s = json |> value_of "modifierName" |> value_of "typeDescriptions" |> value_of "typeString" |> to_string in
  let b = BatString.starts_with s "modifier" in
  let exp = json |> value_of "modifierName" |> trans_expression in
  let args = json |> value_of "arguments" |> trans_functionCallArguments in
  (b, Call (None, exp, args, get_loc json, json |> value_of "id" |> to_int))

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

(* generate Constructor call *)
let trans_inheritanceSpecifier : Yojson.Basic.t -> stmt 
= fun json ->
  let _ = assert (value_of "nodeType" json = `String "InheritanceSpecifier") in 
  let name = json |> value_of "baseName" |> value_of "name" |> to_string in
  let args = json |> value_of "arguments" |> trans_functionCallArguments in
  Call (None, Lv (Var (name,dummy_vinfo)), args, get_loc json, json |> value_of "id" |> to_int)

let get_callee_name : stmt -> string
= fun stmt ->
  match stmt with
  | Call (_, Lv (Var (name,_)),_,_,_) -> name
  | _ -> raise (Failure "get_callee_name")

let resolve_cnstr_calls : stmt list -> stmt list -> stmt
= fun inherit_calls mod_calls ->
  (* In solc 0.4x, the latter has the priority over the former. *)
  (* In recent solc, specifying arguments for both places is an error. *)
  let mod_names = List.map get_callee_name mod_calls in
  List.fold_left (fun acc inherit_call ->
    let name = get_callee_name inherit_call in
    if List.mem name mod_names then
      let matching_mod = List.find (fun m -> name = get_callee_name m) mod_calls in
      Seq (acc, matching_mod)
    else
      Seq (acc, inherit_call)
  ) Skip inherit_calls

(* nodeType : O *)
let trans_contractDefinition : Yojson.Basic.t -> contract 
= fun json ->
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
      acc @ [cnstr_call] (* constructors are called starting from parents *)
    ) [] base_contracts in
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
             fvis = Internal;
             fid = j |> value_of "id" |> to_int;
             scope = cinfo.numid;
             scope_s = cid; (* to be filled by preprocessor *)
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
         let name = j |> value_of "name" |> to_string in 
         let decls = List.map trans_variable_declaration (j |> value_of "members" |> to_list) in
         let structure = (name,decls) in 
         (cid, gvar_decls, structure::structs, enums, func_defs, cinfo)
      | `String "UsingForDirective" -> 
         let lib_name = j |> value_of "libraryName" |> value_of "name" |> to_string in
         let typ = trans_typeName_Descriptions j in
         let cinfo = {cinfo with lib_typ_lst = (lib_name,typ)::cinfo.lib_typ_lst} in
         (cid, gvar_decls, structs, enums, func_defs, cinfo)
      | `String "FunctionDefinition" ->
         let finfo = 
           { is_constructor =
               (try j |> value_of "isConstructor" |> to_bool (* 0.4x version *)
                with _ -> (* 0.5x version *)
                  (match value_of "kind" j with
                   | `String "constructor" -> true
                   | `String "function" -> false
                   | `String "fallback" -> false
                   | _ -> failwith "translation error"));
             is_payable =
               (try j |> value_of "payable" |> to_bool (* 0.4x *)
                with _ -> (* 0.5x *)
                  (match value_of "stateMutability" j with
                   | `String "payable" -> true
                   | `String "nonpayable" -> false
                   | `String "view" -> false
                   | `String "pure" -> false
                   | _ -> failwith "stateMutability"));
             fvis = j |> value_of "visibility" |> trans_visibility;
             fid = j |> value_of "id" |> to_int;
             scope = cinfo.numid;
             scope_s = cid;
             cfg = empty_cfg
           } in
         let fname = if finfo.is_constructor then cid else j |> value_of "name" |> to_string in
         let params = j |> value_of "parameters" |> trans_parameterList in
         let ret_params = j |> value_of "returnParameters" |> trans_parameterList in 
         let stmt =
           if j |> value_of "implemented" |> to_bool then j |> value_of "body" |> trans_block
           else Skip (* function without definitions *) in
         let (mod_calls,cnstr_calls_mod) =
           let lst = j |> value_of "modifiers" |> to_list in
           List.fold_left (fun (acc1,acc2) j' ->
             let (is_modcall, call) = trans_modifierInvocation j' in
             if is_modcall then (Seq (acc1,call), acc2)
             else (acc1, acc2 @ [call])
           ) (Skip,[]) lst in
         let init_stmt =
           if not finfo.is_constructor then mod_calls
           else (* constructor case *)
             let cnstr_calls = resolve_cnstr_calls cnstr_calls_inherit cnstr_calls_mod in
             Seq (gvar_init, Seq (cnstr_calls, mod_calls))
         in
         let whole = Seq (init_stmt,stmt) in
         let func = (fname, params, ret_params, whole, finfo) in
         (cid, gvar_decls, structs, enums, func::func_defs, cinfo)
      | `String "ModifierDefinition" -> 
         let fname = j |> value_of "name" |> to_string in
         let params = j |> value_of "parameters" |> trans_parameterList in
         let finfo = 
           { is_constructor = false;
             is_payable = false;
             fvis = j |> value_of "visibility" |> trans_visibility;
             fid = j |> value_of "id" |> to_int;
             scope = cinfo.numid;
             scope_s = cid;
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
    else (* make a new constructor if does not exist *)
      let fname = cid in
      let params = [] in
      let finfo = { is_constructor = true; is_payable = false; fvis = Public; fid = (-1); scope = cinfo.numid; scope_s = cid; cfg = empty_cfg } in
      let stmt = resolve_cnstr_calls cnstr_calls_inherit [] in
      let cnstr = (fname, params, [], Seq (gvar_init,stmt), finfo) in
      (cid, gvar_decls, structs, enums, cnstr::func_defs, cinfo) 

let translate : Yojson.Basic.t -> pgm
= fun json ->
  let _ = assert (value_of "nodeType" json = `String "SourceUnit") in
  let l = json |> value_of "nodes" |> to_list in (* 0 nodes => `List [] *)
  List.fold_left (fun acc j ->
    let node_typ = value_of "nodeType" j in
    (match node_typ with 
     | `String "ContractDefinition" ->
       acc @ [trans_contractDefinition j]
     | _ -> acc) (* Skip PragmaDirectve, and ImportDirective *)
  ) [] l

let run json = translate json
