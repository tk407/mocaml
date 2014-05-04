val skip :  (unit -> unit) -> unit
val ( >>= ) : (('a -> unit) -> unit) -> ('a -> unit) -> unit

val yield : (unit -> unit) -> unit
val spawn : ((unit -> unit) -> unit -> unit) -> unit
val halt  : unit -> unit

val start : unit -> unit
val stop : unit -> unit

(*i i*)
type 'a mvar
val make_mvar : unit -> 'a mvar
val take_mvar : 'a mvar -> ('a -> unit) -> unit
val put_mvar : 'a mvar -> 'a -> (unit -> unit) -> unit

(*i fifo i*)
type 'a fifo
val make_fifo : unit -> 'a fifo
val take_fifo : 'a fifo -> ('a -> unit) -> unit
val put_fifo : 'a fifo -> 'a -> unit
