open Query
open Vlang
open Lang
open Options
open Semantics
open Z3Interface
open PreprocessExploit

let str_transfer_sender_has_enough_money () =
"  function smartest_transfer (address to, uint256 value) public {
    require ((msg.sender != to));
    uint pre_msg = " ^ !balance_name ^ "[msg.sender];
    uint pre_to = " ^ !balance_name ^ "[to];
    bool ret = transfer(to, value);
    require ((((ret == true) && (pre_msg >= value)) || (ret == false)), \"valismartest_falsified\");
  }"


let str_sender_transfer_sender_bal_dec () =
"  function smartest_transfer (address to, uint256 value) public {
    require ((msg.sender != to));
    uint pre_msg = " ^ !balance_name ^ "[msg.sender];
    uint pre_to = " ^ !balance_name ^ "[to];
    bool ret = transfer(to, value);
    require ((((ret == true) && (" ^ !balance_name ^ "[msg.sender] == (pre_msg - value))) || ((ret == false) && (" ^ !balance_name ^ "[msg.sender] == pre_msg))), \"valismartest_falsified\");
  }"


let str_transfer_recipient_bal_inc () =
"  function smartest_transfer (address to, uint256 value) public {
    require ((msg.sender != to));
    uint pre_msg = " ^ !balance_name ^ "[msg.sender];
    uint pre_to = " ^ !balance_name ^ "[to];
    bool ret = transfer(to, value);
    require ((((ret == true) && (" ^ !balance_name ^ "[to] == (pre_to + value))) || ((ret == false) && (" ^ !balance_name ^ "[to] == pre_to))),  \"valismartest_falsified\");
  }"


let str_transferFrom_bal_enough () =
"  function smartest_transferFrom (address from, address to, uint256 value) public {
    require (from != to);
    uint pre_from = " ^ !balance_name ^ "[from];
    uint pre_to = " ^ !balance_name ^ "[to];
    uint pre_msg = " ^ !allow_name ^ "[from][msg.sender];
    bool ret = transferFrom (from, to, value);
    require ((((ret == true) && (pre_from >= value)) || (ret == false)), \"valismartest_falsified\");
  }"


let str_transferFrom_sender_allow_enough () =
"  function smartest_transferFrom (address from, address to, uint256 value) public {
    require (from != to);
    uint pre_from = " ^ !balance_name ^ "[from];
    uint pre_to = " ^ !balance_name ^ "[to];
    uint pre_msg = " ^ !allow_name ^ "[from][msg.sender];
    bool ret = transferFrom (from, to, value);
    require ((((ret == true) && (pre_msg >= value)) || (ret == false)), \"valismartest_falsified\");
  }"


let str_transferFrom_from_bal_dec () =
"  function smartest_transferFrom (address from, address to, uint256 value) public {
    require (from != to);
    uint pre_from = " ^ !balance_name ^ "[from];
    uint pre_to = " ^ !balance_name ^ "[to];
    uint pre_msg = " ^ !allow_name ^ "[from][msg.sender];
    bool ret = transferFrom (from, to, value);
    require ((((ret == true) && (" ^ !balance_name ^ "[from] == (pre_from - value))) || ((ret == false) && (" ^ !balance_name ^ "[from] == pre_from))), \"valismartest_falsified\");
  }"


let str_transferFrom_to_bal_inc () =
"  function smartest_transferFrom (address from, address to, uint256 value) public {
    require (from != to);
    uint pre_from = " ^ !balance_name ^ "[from];
    uint pre_to = " ^ !balance_name ^ "[to];
    uint pre_msg = " ^ !allow_name ^ "[from][msg.sender];
    bool ret = transferFrom (from, to, value);
    require ((((ret == true) && (" ^ !balance_name ^ "[to] == (pre_to + value))) || ((ret == false) && (" ^ !balance_name ^ "[to] == pre_to))), \"valismartest_falsified\");
  }"


let str_transferFrom_sender_allow_dec () =
"  function smartest_transferFrom (address from, address to, uint256 value) public {
    require (from != to);
    uint pre_from = " ^ !balance_name ^ "[from];
    uint pre_to = " ^ !balance_name ^ "[to];
    uint pre_msg = " ^ !allow_name ^ "[from][msg.sender];
    bool ret = transferFrom (from, to, value);
    require ((((ret == true) && (" ^ !allow_name ^ "[from][msg.sender] == (pre_msg - value))) || ((ret == false) && (" ^ !allow_name ^ "[from][msg.sender] == pre_msg))), \"valismartest_falsified\");
  }"

let str_balance_sum_no_overflow () =
"  function smartest_sum_should_not_overflow (address addr1, address addr2) public {
    require (addr1 != address(0));
    require (addr2 != address(0));
    require ((addr1 != addr2));
    require (((" ^ !balance_name ^ "[addr1] + " ^ !balance_name ^ "[addr2]) >= " ^ !balance_name ^ "[addr1]), \"valismartest_falsified\");
  }"

let str_total_ge_balance () =
"  function smartest_balance_le_total (address addr) public {
    require (addr != address (0));
    require ((" ^ !total_name ^ " >= " ^ !balance_name ^ "[addr]), \"valismartest_falsified\");
  }"

let erc20_sc_src loc =
  if loc = code_transfer_sender_has_enough_money then str_transfer_sender_has_enough_money () else
  if loc = code_transfer_sender_bal_dec then str_sender_transfer_sender_bal_dec () else
      if loc = code_transfer_recipient_bal_inc then str_transfer_recipient_bal_inc () else
      if loc = code_transferFrom_from_bal_enough then str_transferFrom_bal_enough () else
      if loc = code_transferFrom_sender_allow_enough then str_transferFrom_sender_allow_enough () else
      if loc = code_transferFrom_from_bal_dec then str_transferFrom_from_bal_dec () else
      if loc = code_transferFrom_to_bal_inc then str_transferFrom_to_bal_inc () else
      if loc = code_transferFrom_sender_allow_dec then str_transferFrom_sender_allow_dec () else
      if loc = code_balance_sum_no_overflow then str_balance_sum_no_overflow () else
      if loc = code_total_ge_balance then str_total_ge_balance ()
  else failwith "assertion.ml : collect_queries"

let collect_queries : Global.t -> vformula -> Path.t -> stmt -> query list
= fun global vf path stmt ->
  match stmt with
  | Assert (e,"default",loc) when !check_assert ->
    let sc = convert_bexp e in
    let vc = Imply (vf, sc) in
    let sc_src = to_string_exp ~report:true e in
    [{vc=vc; vc2=sc; kind=ASSERT; loc=loc; org_q=Org_Exp e; path=path; src_f=Path.get_fkey path; sc_src=sc_src; attacker_src=""; eth_src=""}]
  | Assert (e,"erc20",loc) when !check_erc20 ->
    let sc = convert_bexp e in
    let vc = Imply (vf, sc) in
    let sc_src = erc20_sc_src loc in
    [{vc=vc; vc2=sc; kind=ERC20; loc=loc; org_q=Org_Exp e; path=path; src_f=Path.get_fkey path; sc_src=sc_src; attacker_src=""; eth_src=""}]
  | _ -> []
