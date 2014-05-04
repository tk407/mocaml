(*ilet dbg s = print_string s; print_newline ()
let dbg s = ()i*)

type 'a thread = 'a Lwt.t

let (>>=) = Lwt.bind

let wait_start, wu_wait_start = Lwt.wait ()

exception Stop
let do_stop = ref false

let spawn t  = (wait_start >>= t); ()
let finish, wu_finish  = let f, w = Lwt.wait () in f >>= fun () -> Lwt.fail Stop, w
let start () = Lwt.wakeup wu_wait_start (); Lwt_unix.run finish
let stop  () = do_stop := true; Lwt.wakeup wu_finish (); Lwt.return ()
let halt  () = Lwt.return ()
let return a = Lwt.return a
let skip     = Lwt.return ()
let yield    = Lwt_unix.yield

type 'a mvar = 'a Lwt_mvar.t

let make_mvar () = Lwt_mvar.create_empty ()

let put_mvar out v = Lwt_mvar.put out v

let take_mvar inp = Lwt_mvar.take inp

type 'a fifo = { q : 'a Queue.t; mutable w: 'a thread option }
let make_fifo () = { q=Queue.create (); w=None }

let take_fifo f =
  if !do_stop then Lwt.fail Stop else
  if Queue.length f.q = 0 then
    let k,wk = Lwt.wait () in (f.w <- Some wk; k)
  else
    Lwt.return (Queue.take f.q)

let put_fifo f v =
  Queue.add v f.q;
  match f.w with
  | Some k ->  f.w <- None; Lwt.wakeup k (Queue.take f.q)
  | None -> ()

