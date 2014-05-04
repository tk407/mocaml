open Lwc
open Big_int
open Kmain

let (<) = lt_big_int
let (>) = gt_big_int
let ( * ) = mult_big_int

(* Merge thread *)

let rec mergeb q1 q2 qo v1 v2 =
  if v1 < v2 then begin
    put_mvar qo v1 >>= fun () ->
    take_mvar q1   >>= fun v1 ->
    mergeb q1 q2 qo v1 v2
  end 
  else if v1 > v2 then begin
    put_mvar qo v2 >>= fun () ->
    take_mvar q2   >>= fun v2 ->
    mergeb q1 q2 qo v1 v2
  end
  else begin
    put_mvar qo v1 >>= fun () ->
    take_mvar q1   >>= fun v1 ->
    take_mvar q2   >>= fun v2 ->
    mergeb q1 q2 qo v1 v2
  end

(* Initializer for merge thread *)

let merge q1 q2 qo () =
  take_mvar q1 >>= fun v1 ->
  take_mvar q2 >>= fun v2 ->
  mergeb q1 q2 qo v1 v2

(* Multiplier thread *)

let rec times a f qo () =
  take_fifo f   >>= fun v ->
  put_mvar qo (a*v) >>= 
  times a f qo

(* The x thread itself *)

let rec x mv f2 f3 f5 () =
  take_mvar mv >>= fun v ->
  if v > !last then stop ()
  else skip >>= fun () ->
    if !print then 
      Printf.printf "%s " (string_of_big_int v);
    put_fifo f2 v;
    put_fifo f3 v;
    put_fifo f5 v;
    x mv f2 f3 f5 ()

(* Set up and start *)

let main () =
  (* fifo + times = mult *)
  let make_mult a =
    let f  = make_fifo ()
    and mv = make_mvar () in
    let t  = times a f mv
    in
    spawn t; (f, mv)
  in
  let make_merge q1 q2 =
    let qo = make_mvar () in
    let m  = merge q1 q2 qo
    in
    spawn m; qo
  in
  let f2, m2 = make_mult (big_int_of_int 2)
  and f3, m3 = make_mult (big_int_of_int 3)
  and f5, m5 = make_mult (big_int_of_int 5) in
  let m35  = make_merge m3 m5 in
  let m235 = make_merge m2 m35
  in
  spawn (x m235 f2 f3 f5);
  spawn (fun () -> put_mvar m235 unit_big_int >>= 
                  halt);
  start ()
;;
  
do_start main
