(* Author: Christophe Deleuze, 2012 *)
(* Modified by Tamás Kispéter, 2014 *)

* library files

Each implementation is in lwc_xxx.ml.

The two interfaces for the Lwc module are in

lwc_direct.mli
lwc_indirect.mli

plus lwc_monad.mli (for cont and promise)

preempt, callcc, and dlcont are in direct style so they are built with
lwc.mli as a link to lwc_direct.mli

tramp is built with lwc_indirect.mli

equeue is built with lwc_equeue.mli which is generated by sed from
lwc_indirect.mli.  This is necessary because equeue mvars are
monomorphic.  lwc_equeue.mli is built either with int mvars or
Big_int.big_int mvars (for the kpn app).

lwt's interface differs slightly from lwc_indirect.mli and is in
lwc_lwt.mli

When compiling an implementation, soft links are set from lwc.mli and
lwc.ml to the appropriate files except for equeue:

since some apps (sieve and many) use int mvars while others (kpn) use
Big_int.big_int mvars, lwc.ml is generated from lwc_equeue.ml by
substituting the appropriate type.


* example files

** direct style

for each app,

app_xxx.ml for xxx=callcc, dlcont, and preempt are soft links to
app_direct.ml

** indirect style

for each app,

app_tramp.ml and app_equeue are soft links to app_indirect.ml
app_lwt.ml is different.

(lwt needs try/with and has no () args ZZZ)
