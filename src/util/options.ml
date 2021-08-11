let inputfile = ref ""
let main_contract = ref ""
let il = ref false
let cfg = ref false
let verify_timeout = ref 300
let z3timeout = ref 30000
let solc_ver = ref ""
let debug = ref ""

let inline_depth = ref (-1)

let verbose = ref false
let json_report = ref false

let mode = ref "verify"
let intra = ref false
let bit = ref 0
let inline_enforce = ref false
let path = ref 1 (* experimental *)

let check_all = ref false

let check_io = ref false
let check_dz = ref false
let check_assert = ref false
let check_kill = ref false
let check_leak = ref false
let check_erc20 = ref false


(* exploit generation *)
let exploit_timeout = ref 600 (* default: 10 minutes *)
let transaction_depth = ref 1000000000000000 (* maximum transaction depth other than initial transaction (i.e., constructor call) *)
let ngram = ref 0

let validate = ref false
let infinite_ether = ref false
let contract_init_eth = ref BatBig_int.zero
let refined_vcgen = ref false

let outdir = ref ""

let activate_detector s =
  match s with
  | "all" -> (* all but invalid assignment *)
    (check_io:=true; check_dz:=true; check_assert:=true;
     check_kill:=true;
     check_erc20:=true; check_leak:=true)
  | "io" -> check_io:=true
  | "dz" -> check_dz:=true
  | "assert" -> check_assert:=true
  | "leak" -> check_leak:=true
  | "kill" -> check_kill:=true
  | "erc20" -> check_erc20:=true
  | _ -> invalid_arg ("invalid option in specifying bug types: " ^ s)

let activate_default_detector_if_unspecified () =
  let b =
    !check_io || !check_dz || !check_assert ||
    !check_kill ||
    !check_erc20 || !check_leak in
  if b=false then (check_io:=true; check_dz:=true)
  else ()

let print_detector_activation_status () =
  if !check_io             then prerr_endline "[CHECKER] Integer Over/Underflows";
  if !check_dz             then prerr_endline "[CHECKER] Division-by-zero";
  if !check_assert         then prerr_endline "[CHECKER] Assertion Violation";
  if !check_kill           then prerr_endline "[CHECKER] Suicidal";
  if !check_erc20          then prerr_endline "[CHECKER] ERC20 Violation";
  if !check_leak           then prerr_endline "[CHECKER] Ether-Leaking";
  prerr_endline ""

let set_mode s =
  match s with
  | "verify" | "exploit" -> mode:=s
  | _ -> invalid_arg "improper arguments for run mode. Should be one of {verify, exploit}"

let options =
  [
    ("-input", Arg.String (fun s -> inputfile := s), "inputfile containing your examples");
    ("-main", Arg.String (fun s -> main_contract := s), "name of main contract to be deployed");
    ("-il", Arg.Set il, "show intermediate representations of original program");
    ("-cfg", Arg.Set cfg, "show control flow graph");
    ("-verify_timeout", Arg.Int (fun n -> verify_timeout:=n), "time budget for verify mode");
    ("-z3timeout", Arg.Int (fun n -> z3timeout:=n), "z3 timebudget in miliseconds");
    ("-solc", Arg.String (fun s -> solc_ver := s), "specify solidity compiler version, e.g., 0.5.13");
    ("-debug", Arg.String (fun s -> debug := s), "debugging certain parts; not for public");
    ("-inline_depth", Arg.Int (fun n -> inline_depth := n), "the number of times being inlined");

    ("-verbose", Arg.Set verbose, "verbose mode");
    ("-json", Arg.Set json_report, "analysis report in json format");

    ("-mode", Arg.String (fun s -> set_mode s), "choose run mode");
    ("-intra", Arg.Set intra, "verify intra-transactionally");
    ("-bit", Arg.Int (fun n -> bit := n), "restrict the number of bits for 256-bit expressions");
    ("-inline_enforce", (Arg.Set inline_enforce), "enforce inlining, without inlining heuristics");
    ("-path", (Arg.Int (fun n -> path := n)), "path enumeration mode - experimental");

    (* exploit generation mode *)
    ("-exploit_timeout", (Arg.Int (fun n -> exploit_timeout:=n)), "time budget for exploit generation mode");
    ("-tdepth", Arg.Int (fun n -> transaction_depth:=n), "maximum transaction depth other than initial transaction (constructor call)");
    ("-ngram", Arg.Int (fun n -> assert (n>0); ngram := n), "set 'n' for n-gram");
    ("-validate", Arg.Set validate, "run concrete validator after the analysis is done.");
    ("-infinite_ether", Arg.Set infinite_ether, "if this option provided, we do not impose constraints on amounts of ethers (default: msg.vaule <= 10 ether).");
    ("-contract_init_eth", Arg.Int (fun n -> assert (n>0);
                           contract_init_eth := BatBig_int.mul (BatBig_int.of_int n) (BatBig_int.pow (BatBig_int.of_int 10) (BatBig_int.of_int 18))),
                           "the amount of Ethers given to a contract to be analyzed (default: 0 ether)");
    ("-refined_vcgen", Arg.Set refined_vcgen, "generate vcs that consider normal terminations of transactions.");

    ("-outdir", Arg.String (fun s -> outdir:= s), "directory where analysis outputs are stored");
  ]
