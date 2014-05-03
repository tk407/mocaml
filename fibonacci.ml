(* Fibonacci *) 

let n =  ref 0

let k = ref 1

let m = ref 0

let f () = let a = !n in ( let b = !k in (let c = !m in (n:=b; k:=a+b; m:=(c+1); (E_constant CONST_unit))) )

let rec f2 () = let a = !n in ( let b = !k in (let c = !m in (n:=b; k:=a+b; m:=(c+1); (E_comp f2))) )

let wat = boxc f2

let bf = boxc f

let p () = (print_int(!m); print_string " ";print_int (!k) ; print_string "\n" ; (E_constant CONST_unit) )

let rec p2 () = (print_int(!m); print_string " ";print_int (!k) ; print_string "\n" ; (E_comp p2) )

let bp = boxc p

let funbf = func (0) (tunit) ( ((bf)  >>= (func (1) (tunit) (id 0)) ))
(* (unit -> unit) -> (unit -> unit) *)

let funbp = func (2) (tunit) ( ((bp)  >>= (func (3) (tunit) (id 2)) ))

let fixfunbf = fix funbf

let fixfunbp = fix funbp

let armf = boxe ( app fixfunbf cunit )
let armp = boxe ( app fixfunbp cunit )

let fib = fork armf armp

let fib2 = fork (boxc f2) (boxc p2)

let rec randex1 () = (print_string "First!\n"; (E_comp randex1))
let rec randex2 () = (print_string "Second!\n"; (E_comp randex2))
let randex = fork (boxc randex1)(boxc randex2)

let forktest n = 
     let rec  ilist k b = match k with 
                          | 0 -> b
                          | l -> ilist (l-1) (k::b)
         in let rec f k = ((fun x ->  (print_string "This is thread #";print_int (k);print_string "\n";(if (read_int ()) == 1 then (E_constant CONST_unit) else (E_comp (f k)))) )) in
            let funlist = map boxc (map f (ilist n [])) in 
            let j = forkN funlist in 
            let x = (newvar j) in j

let jointest n = 
     let rec  ilist k b = match k with 
                          | 0 -> b
                          | l -> ilist (l-1) (k::b)
         in let rec f k = ((fun x ->  (print_string "This is thread #";print_int (k);print_string "\n";(if (read_int ()) == 1 then (E_constant CONST_unit) else (E_comp (f k)))) )) in
            let funlist = map boxc (map f (ilist n [])) in 
            let j = joinN funlist in 
            let x = (newvar j) in j



