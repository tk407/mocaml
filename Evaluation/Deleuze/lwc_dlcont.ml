open Delimcc

type 'a t = 'a -> unit

let runq = Queue.create ()
let enqueue t  = Queue.push t runq
let dequeue () = Queue.take runq

let prompt = new_prompt ()

(*i now defined in dlcont
 let shift0 p f = take_subcont p (fun sk () ->
  (f (fun c -> push_prompt_subcont p sk (fun () -> c))))
i*)

let yield () = shift0 prompt (fun f -> enqueue f)

(* could use abort in halt, we just want to remove the prompt *)
let halt  () = shift0 prompt (fun f -> ())

(* enqueue a new t *)
let spawn p = enqueue (fun () -> push_prompt prompt (fun () -> p (); halt ()))

exception Stop
let stop () = raise Stop

let start () =
  try
    while true do
      dequeue () ()
    done
  with Queue.Empty | Stop -> ()

type 'a mvar = { mutable v:'a option; 
		 mutable read: 'a t option;  (* t blocked on take *)
		 mutable write: (unit t * 'a) option } (* ... on put  *)

let make_mvar () = { v=None; read=None; write=None }

let put_mvar out v =
  match out with
  | { v=Some v'; read=_; write=None } -> 
      shift0 prompt (fun f -> out.write <- Some (f,v))

  | { v=None; read=Some r; write=None } -> 
      out.read <- None; enqueue (fun () -> r v)

  | { v=None; read=None; write=None } -> out.v <- Some v
	
  | _ -> failwith "failed put_mvar"

let take_mvar inp =
  match inp with
  | { v=Some v; read=None; write=None } -> inp.v <- None; v

  | { v=Some v; read=None; write=Some(c,v') } -> 
      inp.v <- Some v'; inp.write <- None; enqueue c; v

  | { v=None; read=None; write=_ } -> 
      shift0 prompt (fun f -> inp.read <- Some f)

  | _ -> failwith "failed take_mvar"


type 'a fifo = { q : 'a Queue.t; mutable w: 'a t option }
let make_fifo () = { q=Queue.create (); w=None }

let take_fifo f =
  if Queue.length f.q = 0 then
    shift0 prompt (fun k -> f.w <- Some k)
  else
    Queue.take f.q

let put_fifo f v =
  Queue.add v f.q;
  match f.w with
  | Some k -> enqueue (fun () -> k (Queue.take f.q)); f.w <- None
  | None -> ()
