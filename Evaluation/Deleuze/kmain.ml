
let print = ref true
let slast = ref "2000"
let last = ref (Big_int.big_int_of_int 2000)

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

let do_start kpn =
  Arg.parse [("-n", Arg.Set_string slast, "set last number to include");
	     ("-q", Arg.Clear print, "dont display numbers") ]  
    (fun _ -> exit 1) "hhh";

  last := Big_int.big_int_of_string !slast;
  try kpn (); perf() with _ -> 
  perf ()
