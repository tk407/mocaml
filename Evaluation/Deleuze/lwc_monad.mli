(* Author: Christophe Deleuze, 2012 *)

type 'a t
val return : 'a -> 'a t
val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t

val spawn : (unit -> unit t) -> unit
val skip : unit t
val yield : unit -> unit t
val halt : unit -> unit t
val stop : unit -> unit t
val start : unit -> unit

(*i mvar i*)
type 'a mvar
val make_mvar : unit -> 'a mvar
val put_mvar : 'a mvar -> 'a -> unit t
val take_mvar : 'a mvar -> 'a t

(*i fifo i*)
type 'a fifo
val make_fifo : unit -> 'a fifo
val take_fifo : 'a fifo -> 'a t
val put_fifo : 'a fifo -> 'a -> unit
