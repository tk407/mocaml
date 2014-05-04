open Lwc
open Main

let rec integers out i () =
  put_mvar out i >>= integers out (i+1)

let rec output inp () =
  take_mvar inp >>= fun v -> 
  if !print then (Printf.printf "%i " v; flush stdout);
  if v < !last then output inp () else (stop (); halt())

let rec filter n inp out () =
  take_mvar inp >>= fun v ->
  (if v mod n <> 0 then put_mvar out v else skip) >>=
  filter n inp out

let rec sift inp out () =
  take_mvar inp >>= fun v ->
  put_mvar out v >>= fun () ->
  let mid = make_mvar () in
  spawn (filter v inp mid);
  sift mid out ()

let sieve () =
  let mi = make_mvar () in
  let mo = make_mvar () in
  spawn (integers mi 2);
  spawn (sift mi mo);
  spawn (output mo);
  start ();;

do_start sieve
