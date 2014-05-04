open Mconbase
open Sugarcube
open Big_int
open Mvars
open Kmain
open List

let (<) = lt_big_int
let (>) = gt_big_int
let ( * ) = mult_big_int





let rec merge35 m3 m5 m35 i j =  
      if i < j then ( (boxe (put_mvar m35 i) >>= (func 1351 tunit ( (  ( (E_comp (fun _ -> (map_mvar m3 (fun x -> ( merge35 m3 m5 m35 x j))))))))))) 
               else 
                if j < i 
                 then ( (boxe (put_mvar m35 j) >>= (func 1353 tunit ( (  ( (E_comp (fun _ -> (map_mvar m5 (fun y -> ( merge35 m3 m5 m35 i y)))))))))))             
                 else ( (boxe (put_mvar m35 j) >>= (func 1353 tunit ( (  ( (E_comp (( (fun _ -> (map_mvar m3 (fun x -> ((E_comp (fun _ -> (map_mvar m5 (fun y -> ( merge35 m3 m5 m35 x y))))))))))))))))))



let emerge35 m3 m5 m35 = E_comp (( (fun _ -> (map_mvar m3 (fun x -> ((E_comp (fun _ -> (map_mvar m5 (fun y -> ( merge35 m3 m5 m35 x y)))))))))))


let rec merge235 m2 m35 m235 i j =  
      if i < j then ( (boxe (put_mvar m235 i) >>= (func 2351 tunit ( (  ( (E_comp (fun _ -> (map_mvar m2 (fun x -> ( merge235 m2 m35 m235 x j))))))))))) 
               else 
                if j < i 
                 then ( (boxe (put_mvar m235 j) >>= (func 2353 tunit ( (  ( (E_comp (fun _ -> (map_mvar m35 (fun y -> ( merge235 m2 m35 m235 i y)))))))))))             
                 else ( (boxe (put_mvar m235 j) >>= (func 2353 tunit ( (  ( (E_comp (( (fun _ -> (map_mvar m2 (fun x -> ((E_comp (fun _ -> (map_mvar m35 (fun y -> ( merge235 m2 m35 m235 x y))))))))))))))))))


let emerge235 m2 m35 m235 = E_comp (( (fun _ -> (map_mvar m2 (fun x -> ((E_comp (fun _ -> (map_mvar m35 (fun y -> ( merge235 m2 m35 m235 x y)))))))))))


let rec printer f2 f3 f5 = fun i -> ((if i > !last then stop () else ());(if ( !print ) then (print_string (string_of_big_int i); print_string "\n")); ((boxe (put_fifo f2 i)) >>= func 1 tunit (boxe (put_fifo f3 i))) >>= func 2 tunit (boxe (put_fifo f5 i)) )

let eprinter f2 f3 f5 m235 = foreverbind (boxc (fun _ -> map_mvar m235 (printer f2 f3 f5))) 4 5


let main () = (let f2 = make_fifo ()
              and f3 = make_fifo ()
              and f5 = make_fifo ()
              and m2 = make_mvar ()
              and m3 = make_mvar ()
              and m5 = make_mvar ()
              and m235 = make_mvar ()
              and m35 = make_mvar () in
              let t2 i = ((put_mvar m2 ((big_int_of_int 2)*i))) 
              and t3 i = ((put_mvar m3 ((big_int_of_int 3)*i))) 
              and t5 i = ((put_mvar m5 ((big_int_of_int 5)*i))) in
              let te2 () =  foreverbind (boxe (map_fifo f2 t2)) 1021 1022 
              and te3 () =  foreverbind (boxe (map_fifo f3 t3)) 1031 1032 
              and te5 () =  foreverbind (boxe (map_fifo f5 t5)) 1051 1052 in
    (m235.v <- Some unit_big_int);evalrandUnsafeForever (forkN (map boxe [  (eprinter f2 f3 f5 m235);  (emerge235 m2 m35 m235); emerge35 m3 m5 m35 ;  te2 () ; te3 () ; te5 () ])) 1000)

(* let tracer_kpn () = printfifobi f2 "f2"; printfifobi f3 "f3"; printfifobi f5 "f5"; printmvarbi m2 "m2"; printmvarbi m3 "m3"; printmvarbi m5 "m5";  printmvarbi m35 "m35"; printmvarbi m235 "m235" *);;

do_start main


