(* MVars *)

open Big_int
open Mconbase
open Sugarcube

type 'a mvar = { mutable v : 'a option }

let make_mvar () = { v = None}

let rec put_mvar out x =  match out.v with
                          | None -> ((out.v <- Some x); cunit)
                          | Some _ -> (E_comp (fun y -> (put_mvar out x)))
     

let rec map_mvar i f =  match i.v with 
      | None -> (E_comp (fun y -> (map_mvar i f)))
      | Some x -> ( i.v <- None; (f (x)))

let printmvar m n =  print_string n; print_string ": "; (match m.v with | None -> print_string"Empty" | Some a -> print_int a); print_string"\n"
let printmvarbi m n =  print_string n; print_string ": "; (match m.v with | None -> print_string"Empty" | Some a -> print_string (string_of_big_int a)); print_string"\n" 


type 'a m_fifo = { mutable q : 'a Queue.t }

let make_fifo () = { q = (Queue.create ())}

let rec put_fifo out x =  (Queue.add x (out.q); cunit)
     

let rec map_fifo i f =  match Queue.is_empty (i.q) with 
      | true -> (E_comp (fun y -> (map_fifo i f)))
      | false -> ( (f (Queue.take i.q)))

let printfifo m n =  print_string n; print_string ": [ "; Queue.iter (fun x -> print_int x; print_string " ") m.q; print_string"]\n"
let printfifobi m n =  print_string n; print_string ": [ "; Queue.iter (fun x -> print_string (string_of_big_int x); print_string " ") m.q; print_string"]\n"


