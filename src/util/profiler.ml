let local_start = ref 0.0

let start_time = ref (Sys.time ()) (* global start time *)
let end_time = ref 0.0 (* global end time *)

let start : string -> unit
= fun s ->
  local_start := Sys.time ();
  prerr_string ("* " ^ s); flush stderr

let finish : string -> unit
= fun s ->
  prerr_string ("took " ^ (string_of_float (Sys.time() -. !local_start)) ^ "s");
  prerr_endline "";
  local_start := 0.0

let print_log : string -> unit
= fun s -> prerr_endline s
