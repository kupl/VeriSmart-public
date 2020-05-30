open Vlang
open Lang
open Query
open Options

module QMap = struct                                                                        
  module BatMap = BatMap.Make (struct type t = Query.src let compare = Query.compare_src end)

  type t = v BatMap.t
  and k = Query.src
  and v = status * int
          
  let mk_key = Query.get_src
  
  let add = BatMap.add
  let find = BatMap.find
  let empty = BatMap.empty
  let bindings = BatMap.bindings
  let for_all = BatMap.for_all
  let map = BatMap.mapi
end

let get_proven : (QMap.k * QMap.v) list -> (QMap.k * QMap.v) list
= fun lst -> List.filter (fun (_,(stat,_)) -> stat = Proven) lst

let get_unproven : (QMap.k * QMap.v) list -> (QMap.k * QMap.v) list
= fun lst -> List.filter (fun (_,(stat,_)) -> stat = UnProven) lst

(******************************)
(*** Integer Over/Underflow ***)
(******************************)
let get_io : (QMap.k * QMap.v) list -> (QMap.k * QMap.v) list
= fun lst -> List.filter (fun ((kind,_,_),(stat,i)) -> kind = IO) lst

let get_io_proven : (QMap.k * QMap.v) list -> (QMap.k * QMap.v) list
= fun lst -> List.filter (fun ((kind,_,_),(stat,i)) -> kind = IO && stat = Proven) lst

let get_io_unproven : (QMap.k * QMap.v) list -> (QMap.k * QMap.v) list
= fun lst -> List.filter (fun ((kind,_,_),(stat,i)) -> kind = IO && stat = UnProven) lst

(************************)
(*** Division-by-zero ***)
(************************)
let get_dz : (QMap.k * QMap.v) list -> (QMap.k * QMap.v) list
= fun lst -> List.filter (fun ((kind,_,_),(stat,i)) -> kind = DZ) lst

let get_dz_proven : (QMap.k * QMap.v) list -> (QMap.k * QMap.v) list
= fun lst -> List.filter (fun ((kind,_,_),(stat,i)) -> kind = DZ && stat = Proven) lst

let get_dz_unproven : (QMap.k * QMap.v) list -> (QMap.k * QMap.v) list
= fun lst -> List.filter (fun ((kind,_,_),(stat,i)) -> kind = DZ && stat = UnProven) lst

(**************)
(*** Assert ***)
(**************)
let get_assert : (QMap.k * QMap.v) list -> (QMap.k * QMap.v) list
= fun lst -> List.filter (fun ((kind,_,_),(stat,i)) -> kind = ASSERT) lst

let get_assert_proven : (QMap.k * QMap.v) list -> (QMap.k * QMap.v) list
= fun lst -> List.filter (fun ((kind,_,_),(stat,i)) -> kind = ASSERT && stat = Proven) lst

let get_assert_unproven : (QMap.k * QMap.v) list -> (QMap.k * QMap.v) list
= fun lst -> List.filter (fun ((kind,_,_),(stat,i)) -> kind = ASSERT && stat = UnProven) lst

let print : QMap.t -> unit
= fun qmap ->
  let lst = QMap.bindings qmap in
  print_endline "=== Report ===";
  List.iteri (fun i ((k,l,s) as src, (stat,iter)) ->
    print_string ("[" ^ string_of_int (i+1) ^ "]" ^ " " ^ "[" ^ Query.to_string_kind_simple k ^ "]" ^ " ");
    print_endline (Query.to_string_src src ^ " : " ^ to_string_status stat)
  ) lst;
  print_endline "";
  print_endline "=== Result Summary ===";
  print_endline ("# Queries                : " ^ string_of_int (List.length lst));
  print_endline ("- integer over/underflow : " ^ string_of_int (List.length (get_io lst)));
  print_endline ("- division-by-zero       : " ^ string_of_int (List.length (get_dz lst)));
  print_endline ("- assertion              : " ^ string_of_int (List.length (get_assert lst)));

  print_endline "";
  print_endline ("# Alarms                 : " ^ string_of_int (List.length (get_unproven lst)));
  print_endline ("- integer over/underflow : " ^ string_of_int (List.length (get_io_unproven lst)));
  print_endline ("- division-by-zero       : " ^ string_of_int (List.length (get_dz_unproven lst)));
  print_endline ("- assertion              : " ^ string_of_int (List.length (get_assert_unproven lst)));

  print_endline "";
  print_endline ("# Proven                 : " ^ string_of_int (List.length (get_proven lst)));
  print_endline ("- integer over/underflow : " ^ string_of_int (List.length (get_io_proven lst)));
  print_endline ("- division-by-zero       : " ^ string_of_int (List.length (get_dz_proven lst)));
  print_endline ("- assertion              : " ^ string_of_int (List.length (get_assert_proven lst)))

let proved_nontrivially : (QMap.k * QMap.v) list -> int
= fun lst ->
  let lst' = List.filter (fun (_,(stat,i)) -> stat = Proven && i > 1) lst in
  List.length lst'
