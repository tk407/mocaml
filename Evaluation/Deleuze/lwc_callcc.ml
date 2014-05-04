open Callcc

type 'a t = 'a -> unit

type queue_t = { mutable e:unit t; q:unit t Queue.t }

let q = { e = (fun()->()); q = Queue.create () }

let enqueue t  = Queue.push t q.q
let dequeue () = try Queue.take q.q with Queue.Empty -> q.e

let halt () = dequeue () ()

exception Stop
let stop () = raise Stop

let start () =
  try
    callcc (fun exitk ->
      q.e <- (fun () -> throw exitk ());
      dequeue () ())
  with Stop -> ()

let yield () = 
  callcc (fun k -> enqueue (fun () -> throw k ()); dequeue () ())

let spawn p = enqueue (fun () -> p (); halt ())

type 'a mvar = { mutable v:'a option; 
		 mutable read: 'a t option;
		 mutable write: (unit t * 'a) option }

let make_mvar () = { v=None; read=None; write=None }

let put_mvar out v =
    match out with
    | { v=Some v; read=_; write=None } ->
	callcc (fun k -> 
	  out.write <- Some ((fun () -> throw k ()),v); halt ())

    | { v=None; read=Some r; write=None } -> 
	out.read <- None; enqueue (fun () -> r v)
	  
    | { v=None; read=None; write=None } -> out.v <- Some v; ()
	  
    | _ -> failwith "failed put_mvar"
  
let take_mvar inp =
    match inp with
    | { v=Some v; read=None; write=None } -> inp.v <- None; v

    | { v=Some v; read=None; write=Some(c, v') } -> 
	inp.v <- Some v'; inp.write <- None; enqueue c; v
	  
    | { v=None; read=None; write=_ } -> 
	callcc (fun k ->
	  inp.read <- Some (fun v -> throw k v);
	  Obj.magic halt ())
	  
    | _ -> failwith "failed take_mvar"

type 'a fifo = { q : 'a Queue.t; mutable w: 'a t option }
let make_fifo () = { q=Queue.create (); w=None }

let take_fifo f =
  if Queue.length f.q = 0 then
    Callcc.callcc (fun k -> f.w <- Some (fun v -> Callcc.throw k v);
      Obj.magic halt ())
  else
    Queue.take f.q

let put_fifo f v =
  Queue.add v f.q;
  match f.w with
  | Some k -> enqueue (fun () -> k (Queue.take f.q)); f.w <- None
  | None -> ()
