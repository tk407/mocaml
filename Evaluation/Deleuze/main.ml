
let print = ref true
let last  = ref 5000
let dont = ref false

let dbg s = print_string s; print_newline ()
let dbg s = ()

(* Unix based 

   Unix.times -> appel système en c unités = clock ticks (100/s sur ES0424) ...
   en Caml, unité = seconde
*)

let start_time = Unix.gettimeofday ()

let perf () =
  let wall_clock = Unix.gettimeofday () -. start_time in
  let { Unix.tms_utime  = user; Unix.tms_stime  = sys;
	Unix.tms_cutime = _;    Unix.tms_cstime = _   } = Unix.times ()
  in
  let gc = Gc.quick_stat () in
  Printf.printf "\nuser %f sys %f real %f mem %i\n" 
    user sys wall_clock (gc.Gc.top_heap_words*4)

(* Sys Based *)

(* perf : write performance data on stdout
   cpu = processor time (user+system) in ms
 *)

(*
let perf () =
  let time = int_of_float (Sys.time () *. 1000.) in
  let gc = Gc.quick_stat () in
  Printf.printf "\ncpu %i wallclock -- mem %i\n" time (gc.Gc.top_heap_words * 4)
*)

(* do_start : parses args and run sieve *)

let do_start sieve =
  Arg.parse [
  ("-n", Arg.Set_int last, "set last number to try");
  ("-q", Arg.Clear print, " quiet: dont display numbers");
  ("-d", Arg.Set dont, " for sorter: terminate after setting up the grid") ]
  (fun _ -> ()) "sieve";
  
  try sieve (); perf () with e -> (dbg "done"; perf ())
;;
