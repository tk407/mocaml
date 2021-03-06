open Mconbase
open Sugarcube
open Mvars
open Main
open List



(* let tracer_erat () = printmvar f2 "f2"; printmvar f3 "f3"; printmvar f5 "f5"; printmvar m2 "m2"; printmvar m3 "m3"; printmvar m5 "m5";  printmvar m35 "m35"; printmvar m235 "m235" *)



let integers n out =  foreverbind (boxc (fun _ -> n:= !n +1; put_mvar out !n )) 1 2 

let filter_prime p i o = foreverbind ( boxe (map_mvar i (fun n -> if (n mod p) != 0 then  put_mvar o n else cunit))) 3 4

let output i =  foreverbind (boxc (fun _ -> map_mvar i (fun n -> if n > !last then stop () else ( (if !print then (print_int n; print_string"\n") else ()); cunit)) )) 5 6 

let rec sift i o = E_comp (( (fun _ -> map_mvar i (fun x -> let n_channel = make_mvar() in
                                                        let n_filter = filter_prime x i n_channel in
                             ((E_comp (fun _ ->  fork (boxe n_filter) (boxe (boxe (put_mvar o x) >>= (func 7 tunit (E_comp (fun _ ->  sift n_channel o))))))))))))


let sieve () = let q1 = make_mvar ()
                and q2 = make_mvar ()
                and integers_N = ref 1 in
  evalrandUnsafeForever (forkN (map boxe [  output q2; integers integers_N q1; sift q1 q2]));;

do_start sieve
