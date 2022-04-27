open Options
open Lang
open Vlang
open Query

let collect ?(extern_ctx=false) : Global.t -> cfg -> vformula -> Path.t -> Node.t -> query list
= fun global g vf path node ->
  let stmt = find_stmt node g in
  let re = if !check_re then ReEntrancy.collect_queries ~extern_ctx:extern_ctx global vf path g node else [] in
  let tx = if !check_tx then TxOrigin.collect_queries global vf path g node else [] in
  let leak = if !check_leak then Leaking.collect_queries vf path stmt else [] in
  let kill = if !check_kill then Destruct.collect_queries vf path (find_stmt node g) else [] in
  let assertion = if !check_assert || !check_erc20 then Assertion.collect_queries global vf path (find_stmt node g) else [] in
  let overflow = if !check_io || !check_dz then Overflow.collect_queries vf path (find_stmt node g) else [] in
  re @ tx @ leak @ kill @ assertion @ overflow
