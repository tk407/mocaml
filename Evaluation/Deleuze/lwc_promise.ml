type 'a state =
  | Ready of 'a
  | Blocked of ('a t -> unit) list ref
  | Link of 'a t

and 'a t = { mutable st : 'a state }

let rec repr t =
  match t.st with
  | Link t' -> repr t'
  | _ -> t

let blocked ()  = { st = Blocked (ref []) }
let ready   v   = { st = Ready v }
let return = ready

let runq = Queue.create ()
let enqueue t  = Queue.push t runq
let dequeue () = Queue.take runq

let fullfill t v =
  let t = repr t in
  match t.st with
  | Blocked w ->
      t.st <- Ready v;
      List.iter (fun f -> f t) !w
  | _ -> failwith "fullfill"

let connect t t' =
  let t' = repr t' in
  match t'.st with
  | Ready v -> fullfill t v
  | Blocked w' ->
      let t = repr t in
      match t.st with
      | Blocked w -> w := !w @ !w'; t'.st <- Link t
      | _ -> failwith "connect"

let (>>=) t f =
  match (repr t).st with
  | Ready v -> f v
  | Blocked w -> let res = blocked () in
    w := (fun t -> let Ready v = t.st in connect res (f v)):: !w;
    res


let skip     = ready ()
let halt  () = ready ()

let yield () = let p = blocked () in enqueue (fun () -> fullfill p ()); p

let wait_start = blocked ()

let spawn t = wait_start >>= t; ()

exception Stop
let stop () = raise Stop

let start () =
  try
    fullfill wait_start ();
    while true do
      dequeue () ()
    done
  with Queue.Empty | Stop -> ()

type 'a mvar = { mutable v:'a option; 
		 mutable read: 'a t option;
		 mutable write: (unit t * 'a) option }

let make_mvar () = { v=None; read=None; write=None }

let put_mvar out v =
  match out with
  | { v=Some v'; read=_; write=None } -> 
      let w = blocked () in out.write <- Some (w,v); w

  | { v=None; read=Some r; write=None } -> 
      out.read <- None; enqueue (fun () -> fullfill r v); ready ()

  | { v=None; read=None; write=None } -> out.v <- Some v; ready ()

  | _ -> failwith "failed put_mvar"

let take_mvar inp =
  match inp with
  | { v=Some v; read=None; write=None } -> 
      inp.v <- None; ready v

  | { v=Some v; read=None; write=Some(c,v') } -> 
      inp.v <- Some v'; inp.write <- None; enqueue (fun () -> fullfill c ());
      ready v

  | { v=None; read=None; write=_ } -> 
      let w = blocked () in inp.read <- Some(w); w

  | _ -> failwith "failed take_mvar"

type 'a fifo = { q : 'a Queue.t; mutable w: 'a t option }
let make_fifo () = { q=Queue.create (); w=None }

let take_fifo f =
  if Queue.length f.q = 0 then
    let k = blocked () in (f.w <- Some k; k)
  else
    ready (Queue.take f.q)

let put_fifo f v =
  Queue.add v f.q;
  match f.w with
  | Some k ->  f.w <- None; fullfill k (Queue.take f.q)
  | None -> ()
