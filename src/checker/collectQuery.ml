open Options
open Lang
open Vlang
open Query

let collect : Global.t -> cfg -> vformula -> Path.t -> Node.t -> query list
= fun global g vf path node ->
  let stmt = find_stmt node g in
  let leak = if !check_leak then Leaking.collect_queries vf path stmt else [] in
  let kill = if !check_kill then Destruct.collect_queries vf path (find_stmt node g) else [] in
  let assertion = if !check_assert || !check_erc20 then Assertion.collect_queries global vf path (find_stmt node g) else [] in
  let overflow = if !check_io || !check_dz then Overflow.collect_queries vf path (find_stmt node g) else [] in
  leak @ kill @ assertion @ overflow
