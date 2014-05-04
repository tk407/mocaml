(* Author: Christophe Deleuze, 2012 *)

(* fair version *)

type 'a state =
  | Return of 'a
  | Sleep of ('a thread -> unit) list ref
  | Link of 'a thread

and 'a thread = { mutable st : 'a state }

let rec repr t =
  match t.st with
  | Link t' -> repr t'
  | _ -> t

let wait ()  = { st = Sleep (ref []) }
let return v = { st = Return v }

let runq = Queue.create ()
let enqueue t  = Queue.push t runq
let dequeue () = Queue.take runq

let wakeup t v =
  let t = repr t in
  match t.st with
  | Sleep w ->
      t.st <- Return v;
      List.iter (fun f -> f t) !w
  | _ -> failwith "wakeup"

let connect t t' =
  let t' = repr t' in
  match t'.st with
  | Return v -> wakeup t v
  | Sleep w' ->
      let t = repr t in
      match t.st with
      | Sleep w -> w := !w @ !w'; t'.st <- Link t
      | _ -> failwith "connect"

let rec (>>=) t f =
  match (repr t).st with
  | Return v -> f v
  | Sleep w -> let res = wait () in
    w := (fun t -> connect res (t >>= f)):: !w;
    res


let skip     = return ()
let yield () = let res = wait () in enqueue (fun () -> wakeup res ()); res
let halt  () = return ()

let wait_start = wait ()

let spawn t = wait_start >>= t; ()

exception Stop
let stop () = raise Stop

let start () =
  try
    wakeup wait_start ();
    while true do
      dequeue () ()
    done
  with Queue.Empty | Stop -> ()

type 'a mvar = { mutable v:'a option; 
		 mutable read: 'a thread option;
		 mutable write: (unit thread * 'a) option }

let make_mvar () = { v=None; read=None; write=None }

let put_mvar out v =
  match out with
  | { v=Some v'; read=_; write=None } -> 
      let w = wait () in out.write <- Some (w,v); w

  | { v=None; read=Some r; write=None } -> 
      out.read <- None; enqueue (fun () -> wakeup r v); return ()

  | { v=None; read=None; write=None } -> out.v <- Some v; return ()

  | _ -> failwith "failed put_mvar"

let take_mvar inp =
  match inp with
  | { v=Some v; read=None; write=None } -> 
      inp.v <- None; return v

  | { v=Some v; read=None; write=Some(c,v') } -> 
      inp.v <- Some v'; inp.write <- None; enqueue (fun () -> wakeup c ());
      return v

  | { v=None; read=None; write=_ } -> 
      let w = wait () in inp.read <- Some(w); w

  | _ -> failwith "failed take_mvar"

type 'a fifo = { q : 'a Queue.t; mutable w: 'a thread option }
let make_fifo () = { q=Queue.create (); w=None }

let take_fifo f =
  if Queue.length f.q = 0 then
    let k = wait () in (f.w <- Some k; k)
  else
    return (Queue.take f.q)

let put_fifo f v =
  Queue.add v f.q;
  match f.w with
  | Some k ->  f.w <- None; wakeup k (Queue.take f.q)
  | None -> ()
