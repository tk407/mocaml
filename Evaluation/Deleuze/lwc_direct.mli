(*type 'a thread = 'a -> unit*)

val yield : unit -> unit
val spawn : (unit -> unit) -> unit
val halt  : unit -> unit

val start : unit -> unit
val stop : unit -> unit

(*i mvar i*)
type 'a mvar
val make_mvar : unit -> 'a mvar
val take_mvar : 'a mvar -> 'a
val put_mvar : 'a mvar -> 'a -> unit

(*i fifo i*)
type 'a fifo
val make_fifo : unit -> 'a fifo
val take_fifo : 'a fifo -> 'a
val put_fifo : 'a fifo -> 'a -> unit
