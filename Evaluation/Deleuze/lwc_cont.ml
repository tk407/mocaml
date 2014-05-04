type 'a t = ('a -> unit) -> unit

let runq = Queue.create ()
let enqueue t  = Queue.push t runq
let dequeue () = Queue.take runq

let return a : 'a t = fun k -> k a

let skip       = return ()
let yield () k = enqueue k
let halt  ()   = return ()


let (>>=) (t:'a t) (k2:'a -> 'b t) : 'b t = fun k -> t (fun r -> k2 r k)

let spawn (t:unit -> unit t) = enqueue (fun () -> t () (fun () -> ()))

exception Stop
let stop () = raise Stop

let start () =
  try
    while true do
      dequeue () ()
    done
  with Queue.Empty | Stop -> ()

type 'a mvar = { mutable v:'a option; 
		 mutable read: ('a -> unit) option;
		 mutable write: ((unit -> unit) * 'a) option }

let make_mvar () = { v=None; read=None; write=None }

let put_mvar out v k =
  match out with
  | { v=Some v'; read=_; write=None } -> out.write <- Some (k,v)

  | { v=None; read=Some r; write=None } -> 
        out.read <- None; enqueue (fun () -> r v); k ()

  | { v=None; read=None; write=None } -> out.v <- Some v; k ()

  | _ -> failwith "failed put_mvar"

let take_mvar inp k =
  match inp with
  | { v=Some v; read=None; write=None } -> inp.v <- None; k v

  | { v=Some v; read=None; write=Some(c,v') } -> 
      inp.v <- Some v'; inp.write <- None; enqueue c; k v

  | { v=None; read=None; write=_ } -> inp.read <- Some(k)

  | _ -> failwith "failed take_mvar"


type 'a fifo = { q : 'a Queue.t; mutable w: ('a -> unit) option }
let make_fifo () = { q=Queue.create (); w=None }

let take_fifo f k =
  if Queue.length f.q = 0 then
    f.w <- Some k
  else
    k (Queue.take f.q)

let put_fifo f v =
  Queue.add v f.q;
  match f.w with
  | Some k -> enqueue (fun () -> k (Queue.take f.q)); f.w <- None
  | None -> ()
