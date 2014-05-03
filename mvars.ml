(* MVars *)

type 'a mvar = { mutable v : 'a Queue.t }

let make_mvar () = { v = (Queue.create ())}

let rec put_mvar out x =  (Queue.add x (out.v); cunit)
     

let rec map_mvar i f =  match Queue.is_empty (i.v) with 
      | true -> (E_comp (fun y -> (map_mvar i f)))
      | false -> ( (f (Queue.take i.v)))

let printmvar m n =  print_string n; print_string ": [ "; Queue.iter (fun x -> print_int x; print_string " ") m.v; print_string"]\n"

