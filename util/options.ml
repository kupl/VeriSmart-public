let inputfile = ref ""
let main_contract = ref ""
let il = ref false
let cfg = ref false
let verify_timeout = ref 300
let z3timeout = ref 30000
let solc_ver = ref ""
let debug = ref ""

let inline_depth = ref (-1)

let intra = ref false
let bit = ref 0
let inline_enforce = ref false

let verify_io = ref false
let verify_dz = ref false
let verify_assert = ref false

let activate_detector s =
  match s with
  | "io" -> verify_io:=true
  | "dz" -> verify_dz:=true
  | "assertion" -> verify_assert:=true
  | _ -> invalid_arg "invalid option in specifying bug types"

let activate_default_detector_if_unspecified () =
  let b = !verify_io || !verify_dz || !verify_assert in
  if b=false then (verify_io:=true; verify_dz:=true)
  else ()

let print_detector_activation_status () =
  if !verify_io then prerr_endline  "ON: integer over/underflow";
  if !verify_dz then prerr_endline  "ON: division-by-zero";
  if !verify_assert then prerr_endline "ON: assertion";
  prerr_endline ""

let options =
  [
    ("-input", (Arg.String (fun s -> inputfile := s)), "inputfile containing your examples");
    ("-main", (Arg.String (fun s -> main_contract := s)), "name of main contract to be deployed");
    ("-il", (Arg.Set il), "show intermediate representations of original program");
    ("-cfg", (Arg.Set cfg), "show control flow graph");
    ("-verify_timeout", (Arg.Int (fun n -> verify_timeout:=n)), "timebudget for verification mode");
    ("-z3timeout", (Arg.Int (fun n -> z3timeout:=n)), "z3 timebudget in miliseconds");
    ("-solc", Arg.String (fun s -> solc_ver := s), "specify solidity compiler version, e.g., 0.5.13");
    ("-debug", (Arg.String (fun s -> debug := s)), "debugging certain parts; not for public");
  ]
