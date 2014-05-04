type 'a thread

val yield : unit -> unit thread
val spawn : (unit -> unit thread) -> unit
val halt : unit -> unit thread
val return : 'a -> 'a thread

val start : unit -> unit
val stop : unit -> unit thread

val skip : unit thread
val ( >>= ) : 'a thread -> ('a -> 'b thread) -> 'b thread

(*i i*)

type 'a fifo
val make_fifo : unit -> 'a fifo
val take_fifo : 'a fifo -> 'a thread
val put_fifo : 'a fifo -> 'a -> unit
