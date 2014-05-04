let f2 : int m_fifo = make_fifo ()
let f3 : int m_fifo = make_fifo ()
let f5 : int m_fifo = make_fifo ()

let m2 : int mvar = make_mvar ()
let m3 : int mvar = make_mvar ()
let m5 : int mvar = make_mvar ()
	
let m235 : int mvar = make_mvar ()
let m35 : int mvar = make_mvar ()



let t2 i = (print_string "T2 out: "; print_int (2*i); print_string "\n";(put_mvar m2 (2*i)))
let te2 =  foreverbind (boxe (map_fifo f2 t2)) 1021 1022
let t3 i = (print_string "T3 out: "; print_int (3*i); print_string "\n";(put_mvar m3 (3*i)))
let te3 =  foreverbind (boxe (map_fifo f3 t3)) 1031 1032
let t5 i = (print_string "T5 out: "; print_int (5*i); print_string "\n";(put_mvar m5 (5*i)))
let te5 =  foreverbind (boxe (map_fifo f5 t5)) 1051 1052


(*let rec merge35 i j = E_comp (fun _ -> (if i < j then ( (put_mvar m35 i) >>= (func 1351 tunit ((map_mvar m3 (fun x -> merge35 x j)))) ) 
                                                 else (if j<i then ( (put_mvar m35 j) >>= (func 1352 tunit ((map_mvar m5 (fun y -> merge35 i y)))) ) 
                                                              else ( (put_mvar m35 i) >>= (func 1353 tunit ((map_mvar m3 (fun x -> map_mvar m5 (fun y -> merge35 x y))))) )))) *)

(* let mergeforever v1 v2 = fix ( func v1 tunit (func v2 tunit ( (id v2) >>= (id v1) ))) *)

let rec mrg35 i j =  
      let m35fPrint _ = (print_string "Merged 3 5 F: "; print_int i;print_string" <- "; print_int i; print_string " vs. ";print_int j; print_string "\n") in
      let m35sPrint _ = (print_string "Merged 3 5 S: "; print_int j;print_string" <- "; print_int i; print_string " vs. ";print_int j; print_string "\n") in
      let m35ePrint _ = (print_string "Merged 3 5 E: "; print_int j;print_string" <- "; print_int i; print_string " vs. ";print_int j; print_string "\n") in
      if i < j then ( (m35fPrint ());(boxe (put_mvar m35 i) >>= (func 1351 tunit ( (  ( (E_comp (fun _ -> ((print_string "Merged 3 5 F: Polling m3\n");map_mvar m3 (fun x -> ( mrg35 x j))))))))))) 
               else 
                if j < i then ( (m35sPrint ());(boxe (put_mvar m35 j) >>= (func 1353 tunit ( (  ( (E_comp (fun _ -> ((print_string "Merged 3 5 S: Polling m5\n");map_mvar m5 (fun y -> ( mrg35 i y)))))))))))             else ( (m35ePrint ());(boxe (put_mvar m35 j) >>= (func 1353 tunit ( (  ( (E_comp (( (fun _ -> (print_string "Merged 3 5 E\n");((print_string "Merged 3 5 E: Polling m3\n");map_mvar m3 (fun x -> ((E_comp (fun _ -> ((print_string "Merged 3 5 E: Polling m5\n");map_mvar m5 (fun y -> ( mrg35 x y))))))))))))))))))

let rec merge35 i j = if i <= j then ((fun a -> (print_string "Merged 3 5 F: "; print_int i;print_string" <- "; print_int i; print_string " vs. ";print_int j; print_string "\n";(boxe ((put_mvar m35 i) >>= (func 1351 tunit ( (  boxc (fun _ -> ((print_string "Merged 3 5 F: Polling m3\n");map_mvar m3 (fun x -> boxc( merge35 x j))))))))))) ) 
                               else ( ((fun a -> (print_string "Merged 3 5 S: "; print_int j; print_string" <- "; print_int i; print_string " vs. ";print_int j; print_string "\n"; (boxe (put_mvar m35 j) >>= (func 1353 tunit ( (   boxc (fun _ -> ((print_string "Merged 3 5 S: Polling m5\n");map_mvar m5 (fun y -> boxc (merge35 i y)))))))))) ) 
                                              ) 
(*  *)
(*   *)

let emerge35 = E_comp (( (fun _ -> (print_string "Merged 3 5 Start!\n");((print_string "Merged 3 5 Start: Polling m3\n");map_mvar m3 (fun x -> ((E_comp (fun _ -> ((print_string "Merged 3 5 Start: Polling m5\n");map_mvar m5 (fun y -> ( mrg35 x y)))))))))))

(*let emerge35 =   (print_string "Merged 3 5 Start: Polling m3\n");map_mvar m3 (fun x -> (print_string "Merged 3 5 Start: Polled m3, Polling m5\n");map_mvar m5 (fun y -> (print_string "Merged 3 5 Start: Polled m5\n");foreverbind (  (boxc ( merge35 x y)) ) 1354 1355) ) *)

let rec merge235 i j =  
      let m235fPrint _ = (print_string "Merged 2 3 5 F: "; print_int i;print_string" <- "; print_int i; print_string " vs. ";print_int j; print_string "\n") in
      let m235sPrint _ = (print_string "Merged 2 3 5 S: "; print_int j;print_string" <- "; print_int i; print_string " vs. ";print_int j; print_string "\n") in
      let m235ePrint _ = (print_string "Merged 2 3 5 E: "; print_int j;print_string" <- "; print_int i; print_string " vs. ";print_int j; print_string "\n") in
      if i < j then ( (m235fPrint ());(boxe (put_mvar m235 i) >>= (func 2351 tunit ( (  ( (E_comp (fun _ -> ((print_string "Merged 2 3 5 F: Polling m2\n");map_mvar m2 (fun x -> ( merge235 x j))))))))))) 
               else 
                if j < i then ( (m235sPrint ());(boxe (put_mvar m235 j) >>= (func 2353 tunit ( (  ( (E_comp (fun _ -> ((print_string "Merged 2 3 5 S: Polling m35\n");map_mvar m35 (fun y -> ( merge235 i y)))))))))))             else ( (m235ePrint ());(boxe (put_mvar m235 j) >>= (func 2353 tunit ( (  ( (E_comp (( (fun _ -> (print_string "Merged 2 3 5 E\n");((print_string "Merged 2 3 5 E: Polling m2\n");map_mvar m2 (fun x -> ((E_comp (fun _ -> ((print_string "Merged 2 3 5 E: Polling m35\n");map_mvar m35 (fun y -> ( merge235 x y))))))))))))))))))

(*let rec merge235 i j = if i <= j then ((fun a -> (print_string "Merged 2 3 5 F: "; print_int i;print_string" <- "; print_int i; print_string " vs. ";print_int j; print_string "\n";(boxe ((put_mvar m235 i) >>= (func 2351 tunit ( (  boxc (fun _ -> (map_mvar m2 (fun x -> boxc( merge235 x j))))))))))) ) 
                               else ( ((fun a -> (print_string "Merged 2 3 5 S: "; print_int j; print_string" <- "; print_int i; print_string " vs. ";print_int j; print_string "\n"; (boxe (put_mvar m235 j) >>= (func 2353 tunit ( (   boxc (fun _ -> (map_mvar m35 (fun y -> boxc (merge235 i y)))))))))) )  
                                             ) *)

(*let rec merge235 i j = E_comp (fun _ -> (if i < j then ( (put_mvar m235 i) >>= (func 2351 tunit ((map_mvar m2 (fun x -> merge235 x j)))) ) 
                                                 else (if j<i then ( (put_mvar m235 j) >>= (func 2352 tunit ((map_mvar m35 (fun y -> merge35 i y)))) ) 
                                                              else ( (put_mvar m235 i) >>= (func 2353 tunit ((map_mvar m2 (fun x -> map_mvar m35 (fun y -> merge235 x y))))) )))) *)

let emerge235 = E_comp (( (fun _ -> (print_string "Merged 2 3 5 Start!\n");((print_string "Merged 2 3 5 Start: Polling m3\n");map_mvar m2 (fun x -> ((E_comp (fun _ -> ((print_string "Merged 2 3 5 Start: Polling m35\n");map_mvar m35 (fun y -> ( merge235 x y)))))))))))
(* let emerge235 = foreverbind ( map_mvar m2 (fun x -> map_mvar m35 (fun y ->(boxc ( merge235 x y)) )) ) 2354 2355 *)
(* let emerge235 = boxe ( ( (map_mvar m2 (fun x -> map_mvar m35 (fun y -> merge235 x y))))) *)

(* E_comp (fun  -> (map_mvar i f)) *)

(* let rec printer = fun i -> (print_int i; print_string "\n"; ((boxe (put_mvar f2 i)) >>= func 1 tunit (boxe (put_mvar f3 i))) >>= func 2 tunit (boxe (put_mvar f5 i)) >>= func 3 tunit ((map_mvar m235 printer))) *)

let rec printer = fun i -> (print_int i; print_string "\n"; ((boxe (put_fifo f2 i)) >>= func 1 tunit (boxe (put_fifo f3 i))) >>= func 2 tunit (boxe (put_fifo f5 i)) )

let eprinter = foreverbind (boxc (fun _ -> map_mvar m235 printer)) 4 5


let kpn = forkN (map boxe [  eprinter;  emerge235; emerge35 ;  te2 ; te3 ; te5 ])

let tracer_kpn () = printfifo f2 "f2"; printfifo f3 "f3"; printfifo f5 "f5"; printmvar m2 "m2"; printmvar m3 "m3"; printmvar m5 "m5";  printmvar m35 "m35"; printmvar m235 "m235"


