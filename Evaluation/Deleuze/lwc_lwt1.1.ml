(*ilet dbg s = print_string s; print_newline ()
let dbg s = ()i*)

type 'a thread = 'a Lwt.t

let (>>=) = Lwt.bind

let wait_start = Lwt.wait ()

exception Stop
let do_stop = ref false

let spawn t  = (wait_start >>= t); ()
let finish   = Lwt.wait () >>= fun () -> Lwt.fail Stop
let start () = Lwt.wakeup wait_start (); Lwt_unix.run finish
let stop  () = do_stop := true; Lwt.wakeup finish (); Lwt.return ()
let halt  () = Lwt.return ()
let return a = Lwt.return a
let skip     = Lwt.return ()
let yield    = Lwt_unix.yield

type 'a mvar = { mutable v:'a option; 
		 mutable read: 'a Lwt.t option;
		 mutable write: (unit Lwt.t * 'a) option }

let make_mvar () = { v=None; read=None; write=None }

let put_mvar out v =
  if !do_stop then Lwt.fail Stop else
  match out with
  | { v=Some v'; read=_; write=None } -> 
      let w = Lwt.wait () in out.write <- Some (w,v); w

  | { v=None; read=Some r; write=None } -> 
      out.read <- None; Lwt.wakeup r v; Lwt.return ()

  | { v=None; read=None; write=None } -> out.v <- Some v; Lwt.return ()

  | _ -> failwith "failed put_mvar"

let take_mvar inp =
  if !do_stop then Lwt.fail Stop else
  match inp with
  | { v=Some v; read=None; write=None } -> 
      inp.v <- None; Lwt.return v

  | { v=Some v; read=None; write=Some(c,v') } -> 
      inp.v <- Some v'; inp.write <- None; Lwt.wakeup c ();
      Lwt.return v

  | { v=None; read=None; write=_ } -> 
      let w = Lwt.wait () in inp.read <- Some(w); w

  | _ -> failwith "failed take_mvar"

type 'a fifo = { q : 'a Queue.t; mutable w: 'a thread option }
let make_fifo () = { q=Queue.create (); w=None }

let take_fifo f =
  if !do_stop then Lwt.fail Stop else
  if Queue.length f.q = 0 then
    let k = Lwt.wait () in (f.w <- Some k; k)
  else
    Lwt.return (Queue.take f.q)

let put_fifo f v =
  Queue.add v f.q;
  match f.w with
  | Some k ->  f.w <- None; Lwt.wakeup k (Queue.take f.q)
  | None -> ()

