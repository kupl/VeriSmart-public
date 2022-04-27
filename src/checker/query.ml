open Vlang
open Lang
open Options

type query = {
  vc: vformula;         (* safety propery of a query per path. *)
  vc2: vformula;        (* vc for generating lasting inputs.   *)
  kind: kind;
  qloc: int;
  org_q: origin;        (* original expression in the source code *)
  path: Path.t;         (* basic path wherein vc was generated *)
  src_f: fkey;          (* function signature where vc was generated *)
  sc_src: string;       (* safety condition at source-code level *)
  attacker_src: string; (* attacker (ether receiver) at source-code level; only valid for leaking detection *)
  eth_src: string       (* weis to be transferred to attacker at source-code level; only valid for leaking detection *)
}

and status = Proven | UnProven | Disproven
and kind =
  | IO | DZ | ASSERT | KILL
  | ETH_LEAK | ERC20
  | RE_EL | RE
  | TX_ORG

and origin = Org_Stmt of stmt | Org_Exp of exp | Org_Func of fkey

let code_transfer_sender_has_enough_money = -100
let code_transfer_sender_bal_dec = -99
let code_transfer_recipient_bal_inc = -98

let code_transferFrom_from_bal_enough = -97
let code_transferFrom_sender_allow_enough = -96
let code_transferFrom_from_bal_dec = -95
let code_transferFrom_to_bal_inc = -94
let code_transferFrom_sender_allow_dec = -93

let code_approve_set = -92

let code_balance_sum_no_overflow = -91
let code_total_ge_balance = -90

let code_public_getter = -10

let to_string_status status =
  match status with
  | Proven -> "proven"
  | UnProven -> "unproven"
  | Disproven -> "disproven"

let to_string_kind kind =
  match kind with
  | IO -> "integer over/underflow"
  | DZ -> "division-by-zero"
  | ASSERT -> "assertion"
  | KILL -> "kill-anyone"
  | ETH_LEAK -> "ether-leaking"
  | ERC20 -> "ERC20 standard"
  | RE_EL -> "reentrancy-leaking"
  | RE -> "reentrancy"
  | TX_ORG -> "tx origin"

let to_string_kind_simple kind =
  match kind with
  | IO -> "IO"
  | DZ -> "DZ"
  | ASSERT -> "ASSERT"
  | KILL -> "KA"
  | ETH_LEAK -> "ETH_LEAK"
  | ERC20 -> "ERC20"
  | RE_EL -> "RE_EL"
  | RE -> "RE"
  | TX_ORG -> "TX_ORG"

let to_string_origin ?(report=false) : origin -> string
= fun org ->
  match org with
  | Org_Stmt s -> to_string_stmt ~report s
  | Org_Exp e -> to_string_exp ~report e
  | Org_Func f -> to_string_fkey f

let compare_query : query -> query -> int
= fun q1 q2 ->
  if Stdlib.compare q1.kind q2.kind = 0 then
    if Stdlib.compare q1.qloc q2.qloc = 0 then
      BatString.compare (to_string_origin ~report:true q1.org_q) (to_string_origin ~report:true q2.org_q)
    else Stdlib.compare q1.qloc q2.qloc
  else Stdlib.compare q1.kind q2.kind

let sort : query list -> query list
= fun qs -> BatList.sort compare_query qs

(* group queries that have the same line numbers and same expressions in original source code *)
let group : query list -> query list list
= fun qs -> BatList.group compare_query qs

type src = kind * int * string (* line in the original source code *)

let compare_src : src -> src -> int
= fun (k1,l1,s1) (k2,l2,s2) ->
  if Stdlib.compare k1 k2 = 0 then
    if Stdlib.compare l1 l2 = 0 then
      BatString.compare s1 s2
    else Stdlib.compare l1 l2
  else Stdlib.compare k1 k2

let equal_src s1 s2 = (compare_src s1 s2 = 0)

let get_src : query -> src
= fun q -> (q.kind, q.qloc, to_string_origin ~report:true q.org_q)

let to_string_standard_src (k,l,s) =
  if l = code_transfer_sender_has_enough_money then      "[transfer] The message sender should have enough tokens"
  else if l = code_transfer_sender_bal_dec then          "[transfer] The sender's balance should decrease properly"
  else if l = code_transfer_recipient_bal_inc then       "[transfer] The recipient's balance should increase properly"
  else if l = code_transferFrom_from_bal_enough then     "[transferFrom] The from's balance should have enough tokens"
  else if l = code_transferFrom_sender_allow_enough then "[transferFrom] The sender's allowance should be enough"
  else if l = code_transferFrom_from_bal_dec then        "[transferFrom] The from's balance should decrease properly"
  else if l = code_transferFrom_to_bal_inc then          "[transferFrom] The recipient's balance should increase properly"
  else if l = code_transferFrom_sender_allow_dec then    "[transferFrom] The sender's allowance should decrease properly"
  else if l = code_approve_set then                      "[approve] The allowance should be set properly"
  else if l = code_balance_sum_no_overflow then          "[invariant] sum of balances should not overflow"
  else if l = code_total_ge_balance then                 "[invariant] totalSupply should be greater than or equal to any balances"
  else failwith ("Unexpected assertion code: " ^ to_string_kind_simple k ^ ", " ^ string_of_int l ^ ", " ^ s)

let to_string_src (k,l,s) =
  if l>0 then "line " ^ string_of_int l ^ ", " ^ s
  else to_string_standard_src (k,l,s)
