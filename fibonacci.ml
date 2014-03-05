(* Fibonacci *) 

let n =  ref 0

let k = ref 1

let m = ref 0

let f () = let a = !n in ( let b = !k in (let c = !m in (n:=b; k:=a+b; m:=(c+1); ())) )

let bf = boxc f

let p () = (print_int(!m); print_string " ";print_int (!k) ; print_string "\n" ; () )

let bp = boxc p


