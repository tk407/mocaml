val skip :  (unit -> unit) -> unit
val ( >>= ) : (('a -> unit) -> unit) -> ('a -> unit) -> unit

val yield : (unit -> unit) -> unit
val spawn : (unit -> unit) -> unit
val halt  : unit -> unit

val start : unit -> unit
val stop : unit -> unit

(*i i*)
type 'a mvar
val make_mvar : unit -> 'a mvar
val take_mvar : Big_int.big_int mvar -> (Big_int.big_int -> unit) -> unit
val put_mvar : Big_int.big_int mvar -> Big_int.big_int -> (unit -> unit) -> unit

(*i fifo i*)
type 'a fifo
val make_fifo : unit -> 'a fifo
val take_fifo : Big_int.big_int fifo -> (Big_int.big_int -> unit) -> unit
val put_fifo : Big_int.big_int fifo -> Big_int.big_int -> unit
