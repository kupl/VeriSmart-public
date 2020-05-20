open Lang
open Vlang
open Z3
open Z3Interface
open Options

type t = (var, Z3.Expr.expr) BatMap.t
and model = t

let empty = BatMap.empty
let add = BatMap.add
let find = BatMap.find

let to_string' : model -> string
= fun m -> 
  "  " ^ "[" ^ "\n" ^
   BatMap.foldi (fun (x,t) d acc ->
     acc ^
     "   " ^ x ^ " -> " ^ Z3.Expr.to_string d ^ "\n"
  ) m ""
  ^ "  " ^ "]"

let to_z3exp : model -> Z3.Expr.expr
= fun m ->
  let lst = BatMap.bindings m in
  let lst = List.map (fun ((x,t),e) -> Z3.Boolean.mk_eq !ctx (vexp_to_z3exp (VVar (x,t))) e) lst in
  Z3.Boolean.mk_and !ctx lst

module ModelMap = struct
  type t = (Node.t, model) BatMap.t 
  
  let add = BatMap.add
  let find x m = try BatMap.find x m with Not_found -> BatMap.empty
  let empty = BatMap.empty

  let to_string : t -> string
  = fun mm ->
    "[" ^ "\n" ^
    BatMap.foldi (fun n d acc ->
      acc ^ Node.to_string n ^ " ->\n" ^
      to_string' d ^ "\n"
    ) mm ""
    ^ "]"
end
