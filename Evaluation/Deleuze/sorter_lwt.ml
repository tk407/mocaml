open Lwc
open Main

let minmax a b =
  if a<b then (a,b) else (b,a)

let rec comparator x y hi lo () =
  take_mvar x >>= fun a ->
  take_mvar y >>= fun b ->
  let (l,h) = minmax a b
  in
  put_mvar lo l >>= fun () ->
  put_mvar hi h >>=
  comparator x y hi lo

let make_list n fct =
  let rec loop n acc =
    if n=0 then acc
    else
      loop (n-1) (fct n ::acc)
  in
  loop n []

let make_n_mvars n =
  make_list n (fun _ -> make_mvar ())

let rec iter4 fct l1 l2 l3 l4 =
  match (l1,l2,l3,l4) with
  | [],[],[],[] -> []
  | l1::l1s,l2::l2s,l3::l3s,l4::l4s -> 
      fct (l1,l2,l3,l4);
      iter4 fct l1s l2s l3s l4s
  | _ -> failwith "iter4"    

let column (i::is) y =
  let n = List.length is in
  let ds = make_n_mvars (n-1) in
  let os = make_n_mvars n
  in
  iter4 
    (fun (i,di,o,od) ->
      spawn (comparator i di o od))
    is (i::ds) os (ds @ [y]);
  os

let sorter xs ys () =
  let rec help is ys n =
    if n>2 then
      let os = column is (List.hd ys) in
      help os (List.tl ys) (n-1)
    else
      spawn (comparator 
	  (List.hd (List.tl is)) (List.hd is)
	  (List.hd (List.tl ys)) (List.hd ys))
  in
  help xs ys (List.length xs)

let rec set_list mvs l () =
  match mvs,l with
  | [],[] -> halt ()
  | m::r,h::t -> put_mvar m h >>= set_list r t

let print_list mvs () =
  let rec loop mvs acc =
    match mvs with
    | [] -> return acc
    | h::t -> take_mvar h >>= fun v -> loop t (v::acc)
  in
  loop mvs [] >>= fun l -> 
    List.iter (fun n -> Printf.printf "%i " n) (List.rev l); stop ()

let sort l =
  let n = List.length l in
  let xs = make_n_mvars n
  and ys = make_n_mvars n
  in
  sorter xs ys ();
  spawn (set_list xs l);
  spawn (print_list ys);
  if not !dont then start ()

let doit () =
  let l = make_list !last (fun _ -> Random.int 999) in
  sort l
;;

do_start doit
