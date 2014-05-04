(* Author: Christophe Deleuze, 2012 *)

let skip k  = k ()

let (>>=) inst k = inst k

type eventid = unit ref
type 'a event = Written of eventid | Read of eventid * 'a | Go of eventid

let make_eventid () = ref ()

let esys : int event Equeue.t = Equeue.create (fun _ -> ())

let yield k = 
  let id = make_eventid () in
  Equeue.add_handler esys (fun esys e ->
    match e with
    | Go id' when id' == id -> k ()
    | _ -> raise Equeue.Reject);
  Equeue.add_event esys (Go id);
  raise Equeue.Terminate

let spawn t = 
  let id = make_eventid () in
  Equeue.add_handler esys (fun esys e ->
    match e with
    | Go id' when id' == id -> t ()
    | _ -> raise Equeue.Reject);
  Equeue.add_event esys (Go id)

let halt () = raise Equeue.Terminate

exception Stop
let stop () = raise Stop

let start () =
  try
    Equeue.run esys
  with Stop -> ()

type 'a mvar = { mutable v:'a option; 
		 mutable read:eventid option;
		 mutable write:(eventid * 'a) option }

let make_mvar () = { v=None; read=None; write=None }

let put_mvar out v k =
  match out with
  | { v=Some v'; read=_; write=None } -> 
      let id = make_eventid () in out.write <- Some (id, v);
      Equeue.add_handler esys (fun esys e ->
	match e with
	| Written id' when id' == id -> k ()
	| _ -> raise Equeue.Reject);
      raise Equeue.Terminate
	
  | { v=None; read=Some id; write=None } -> 
      out.read <- None;
      Equeue.add_event esys (Read(id, v));
      k ()

  | { v=None; read=None; write=None } -> out.v <- Some v; k ()

  | _ -> failwith "failed put_mvar"

let take_mvar inp k =
  match inp with
  | { v=Some v; read=None; write=None } -> inp.v <- None; k v

  | { v=Some v; read=None; write=Some(id, v') } -> 
      inp.v <- Some v'; inp.write <- None;
      Equeue.add_event esys (Written id); k v

  | { v=None; read=None; write=_ } ->
      let id = make_eventid () in
      inp.read <- Some id;
      Equeue.add_handler esys (fun esys e ->
	match e with
	| Read(id', arg) when id' == id -> k arg
	| _ -> raise Equeue.Reject);
      raise Equeue.Terminate
	    
  | _ -> failwith "failed take_mvar"

type 'a fifo = { q:'a Queue.t; mutable w:eventid  option }
let make_fifo () = { q=Queue.create (); w=None }

let take_fifo f k =
  if Queue.length f.q = 0 then
    let id = make_eventid () in
    f.w <- Some id;
    Equeue.add_handler esys (fun esys e ->
      match e with
      | Read(id', arg) when id' == id -> k arg
      | _ -> raise Equeue.Reject);
    raise Equeue.Terminate      
  else
    k (Queue.take f.q)

let put_fifo f v =
  Queue.add v f.q;
  match f.w with
  | Some id -> Equeue.add_event esys (Read(id, Queue.take f.q)); f.w <- None
  | None -> ()

