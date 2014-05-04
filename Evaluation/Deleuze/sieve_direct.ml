open Lwc
open Main

let rec integers out i () =
  put_mvar out i;
  integers out (i+1) ()

let rec output inp () =
  let v = take_mvar inp in
  if !print then (Printf.printf "%i " v; flush stdout);
  if v < !last then output inp () else stop ()

let rec filter n inp out () =
  let v = take_mvar inp in
  if v mod n <> 0 then put_mvar out v;
  filter n inp out ()

let rec sift inp out () =
  let v = take_mvar inp in
  put_mvar out v;
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
