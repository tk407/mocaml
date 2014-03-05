(* Fibonacci *) 

let n =  ref 0

let k = ref 1

let m = ref 0

let f () = let a = !n in ( let b = !k in (let c = !m in (n:=b; k:=a+b; m:=(c+1); ())) )

let bf = boxc f

let p () = (print_int(!m); print_string " ";print_int (!k) ; print_string "\n" ; () )

let bp = boxc p

let funbf = func (vname 0) (tunit) ( ((bf)  >>= (func (vname 1) (tunit) (id 0)) ))
(* (unit -> unit) -> (unit -> unit) *)

let funbp = func (vname 2) (tunit) ( ((bp)  >>= (func (vname 3) (tunit) (id 2)) ))

let fixfunbf = fix funbf

let fixfunbp = fix funbp

let armf = boxe ( app fixfunbf cunit )
let armp = boxe ( app fixfunbp cunit )

let fib = fork armf armp




