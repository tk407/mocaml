type 'a thread = 'a -> unit
(*let spawn t = ignore (Thread.create t ()); ()*)
let dbg t = print_string t; print_newline()
let l = Mutex.create ()

let spawn t = ignore (Thread.create (fun () -> Mutex.lock l; 
Mutex.unlock l; t ()) (); ())

let stop_event = Event.new_channel ()
let start () = Mutex.unlock l; Event.sync (Event.receive stop_event)
let stop  () = Event.sync (Event.send stop_event ())

let halt  = Thread.exit
let yield = Thread.yield

type 'a mvar = 
    { mutable v:'a option; ch:'a Event.channel; mutable read:bool; mutable write:bool }

let make_mvar () = 
  { v = None; ch = Event.new_channel (); read=false; write=false }

let ml = Mutex.create ()

let mvl () = Mutex.lock ml
let mvu () = Mutex.unlock ml

let put_mvar out v =
  mvl ();
  match out with
  | { v=Some v'; ch=c; read=_; write=false  } -> out.write <- true; mvu ();
      Event.sync (Event.send c v)

  | { v=None; ch=c; read=true;  write=false } -> mvu (); out.read <- false; Event.sync (Event.send c v)

  | { v=None; ch=c; read=false; write=false } -> out.v <- Some v; mvu ()

  | _ -> failwith "failed put_mvar"

let take_mvar inp =
  mvl ();
  match inp with
  | { v=Some v; ch=c; read=false; write=false } -> inp.v <- None; mvu (); v

  | { v=Some v; ch=c; read=false; write=true } -> 
      inp.write <- false; mvu (); let v' = Event.sync (Event.receive c) in
      mvl (); inp.v <- Some v'; mvu (); v

  | { v=None; ch=c; read=false; write=_ } -> 
      inp.read <- true; mvu (); Event.sync (Event.receive c)

  | { v=None; ch=_; read=true; write=_ } -> failwith "take_mvar2"

  | _ -> failwith "failed take_mvar"

type 'a fifo = { q : 'a Queue.t; mutable w: 'a Event.channel option }
let make_fifo () = { q=Queue.create (); w=None }

let take_fifo f =
   if Queue.length f.q = 0 then
     let e = Event.new_channel () in
     f.w <- Some e;
     Event.sync (Event.receive e)
   else
     Queue.take f.q

let put_fifo f v =
   match f.w with
   | None -> Queue.add v f.q
   | Some e -> f.w <- None; Event.sync (Event.send e v)
;;

Mutex.lock l
