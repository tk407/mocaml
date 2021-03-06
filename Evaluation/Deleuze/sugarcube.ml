(* sugarcube *)

open List
open Mconbase

let boxc f = E_live_expr (E_comp f)

let boxe e = E_live_expr ( e)

let ( >>= ) a b = E_bind (a, b)

let app a b = E_apply (a, b)

let fork a b = E_fork (a, b)

let func v t e = E_function (v, t, e)

let case e1 x1 e2 x2 e3 = E_case (e1, x1, e2, x2, e3)

let fix e = E_fix e

let pair a b = E_inpair (a, b)

let ret a = E_ret a

let proj1 a = E_proj1 a
let proj2 a = E_proj2 a

let rec v_expr = function
| E_ident value_name5 -> value_name5::[]
| E_unit -> []
| E_apply (expr5, expr') -> append (v_expr expr5) (v_expr expr')
| E_bind (expr5, expr') -> append (v_expr expr5) (v_expr expr')
| E_function (value_name5, typexpr5, expr5) -> append (v_expr expr5) (value_name5::[])
| E_fix e -> v_expr e
| E_comp e -> []
| E_live_expr e -> v_expr e
| E_pair (e, e') -> append (v_expr e) (v_expr e')
| E_inpair (e, e') -> append (v_expr e) (v_expr e')
| E_proj1 e -> v_expr e
| E_proj2 e -> v_expr e
| E_fork (e, e') -> append (v_expr e) (v_expr e')
| E_ret e -> (v_expr e)
| E_taggingleft e -> v_expr e
| E_taggingright e -> v_expr e
| E_case (e1, x1, e2, x2, e3) ->
  append (v_expr e1) (append (v_expr e2) (v_expr e3))



let cunit = E_unit

let tunit = TE_unit

let tfun a b = TE_arrow(a,b)

let id n = E_ident (n) 

let rec newvar_h l n =
     (match l with
     | [] -> n
     | h::t -> newvar_h t (if h == n then n+1 else n))

let newvar e = newvar_h (v_expr e) 0

(* a # b >>= fun x0 case (ident x0) x1 (pair (ret (proj1 (ident x1))) ((proj2 (ident x1)) >>= fun x3. ret (ident x3))) x2 (pair ((proj1 (ident x1)) >>= fun x3. ret (ident x3)) (ret (proj2 (ident x1)))) *)

let join a b = let basefork = fork a b in
               let basevars = v_expr basefork in
               let x0 = newvar_h basevars 0 in
               let x1 = newvar_h basevars (x0+1) in
               let x2 = newvar_h basevars (x1+1) in
               let x3 = newvar_h basevars (x2+1) in
               let x4 = newvar_h basevars (x3+1) in
               let b = func x0 tunit (case (id x0) 
                               x1 (pair (ret (proj1 (id x1))) ((proj2 (id x1)) >>= (func x3 tunit (ret (id x3))))) 
                               x2 (pair ((proj1 (id x2)) >>= (func x4 tunit (ret (id x4)))) (ret (proj2 (id x2)))) ) in
                basefork >>= b

let joinDiscardRight a b = let basefork = fork a b in
               let basevars = v_expr basefork in
               let x0 = newvar_h basevars 0 in
               let x1 = newvar_h basevars (x0+1) in
               let x2 = newvar_h basevars (x1+1) in
               let x3 = newvar_h basevars (x2+1) in
               let x4 = newvar_h basevars (x3+1) in
               let b = func x0 tunit (case (id x0) 
                               x1 ((proj2 (id x1)) >>= (func x3 tunit (((ret (proj1 (id x1))) ) ))) 
                               x2 (((proj1 (id x2)) >>= (func x4 tunit (ret (id x4)))) ) ) in
                basefork >>= b                  

let split_list_at xs k = let rec split_list_at_h l n (fh, sh) =  match n with 
                                     | 0 -> (rev fh, sh)
                                     | n -> match sh with 
                                            | [] -> (rev fh, sh)
                                            | h::t -> split_list_at_h l (n-1) (h::fh, t)
                                  in split_list_at_h xs k ([], xs)

let rec joinN l = match l with 
                  | a::b::c::[] -> join (boxe (join a b)) c
                  | a::b::[] -> join a b
                  | a::[] -> assert false
                  | [] -> assert false
                  | t -> let n = length t in
                         let f_half = n / 2 in
                         let (j1, j2) = split_list_at l f_half in
                         join (boxe (joinN j1)) (boxe (joinN j2))
                         

let rec joinNDiscardRight l = match l with 
                  | a::b::[] -> joinDiscardRight a b
                  | a::[] -> assert false
                  | [] -> assert false
                  | h::t -> joinDiscardRight h (boxe (joinN t))


let rec forkN l = match l with 
                  | a::b::c::[] -> fork (boxe (fork a b)) c
                  | a::b::[] -> fork a b
                  | a::[] -> assert false
                  | [] -> assert false
                  | t -> let n = length t in
                         let f_half = n / 2 in
                         let (j1, j2) = split_list_at l f_half in
                         fork (boxe (forkN j1)) (boxe (forkN j2))


let rec foreverbind e v1 v2 = fix (func v1 tunit (e >>= (func v2 tunit (id v1))))

let rec rrpredef l n k () = if k==n then rrpredef l n 0 () else Seq(nth l k, rrpredef l n (k+1))




let rec makerr1 () = Seq(S_First, makerr2) 
and makerr2 () = Seq(S_Second, makerr1) 

let _ = Random.self_init()

let rec make_random_predef_list n acc = if n == 0 then acc else make_random_predef_list (n-1) ((if Random.bool() then S_First else S_Second) ::acc)

let rec makerand () = if Random.bool() then Seq(S_First, makerand) else Seq(S_Second, makerand)

let rec makerandWithPrefix pr () = match pr with 
                                   | [] -> (makerand ())
                                   | h::t -> Seq(h, (makerandWithPrefix t))

let evalrandFTT ftt e = let rec evalrandFTT_h hft hftt e' = 
                              match hft with 
                              | [] -> evalrandFTT_h (!hftt) hftt e'
                              | h::t -> evalrandFTT_h (t) hftt (xJO_red12 e' (makerandWithPrefix h ()))
                        in evalrandFTT_h !ftt ftt e

let rec evalrr1 e n = (match n with 
                       | 0 -> e
                       | m -> evalrr2 (xJO_red12 e (makerr1 ())) (m-1))
and evalrr2 e n = (match n with 
                       | 0 -> e
                       | m -> evalrr1 (xJO_red12 e (makerr2 ())) (m-1))

let rec evalrrUnsafeForever1 e = evalrrUnsafeForever2 (xJO_red12 e (makerr1 ()))
and evalrrUnsafeForever2 e = evalrrUnsafeForever1 (xJO_red12 e (makerr2 ())) 

let rec evalrand e n = (match n with 
                       | 0 -> e
                       | m -> evalrand (xJO_red12 e (makerand ())) (m-1))

let rec evalrandSafe e n = (match n with 
                       | 0 -> e
                       | m -> if xis_value_of_expr e then e else evalrandSafe (xJO_red12 e (makerand ())) (m-1))

let rec evalrandSafeForever e = (if xis_value_of_expr e then e else evalrandSafeForever (xJO_red12 e (makerand ())))
let rec evalrandUnsafeForever e = (evalrandUnsafeForever (xJO_red12 e (makerand ())))

let evalsemirandUnsafeForever e l =
                             let predeflist =  make_random_predef_list l [] in
                             let rec evalsemirandUnsafeForever j k = if k==l then evalsemirandUnsafeForever j 0 else evalsemirandUnsafeForever (xJO_red12 j (rrpredef predeflist l k ())) (k+1)
                             in evalsemirandUnsafeForever e 0

let rec evalrandSafeDebug e n d = (match n with 
                       | 0 -> e
                       | m -> if xis_value_of_expr e then e else (d () ;evalrandSafeDebug (xJO_red12 e (makerand ())) (m-1) d))

let rec evalrr1Safe e n = (match n with 
                       | 0 -> e
                       | m -> if xis_value_of_expr e then e else evalrr2Safe (xJO_red12 e (makerr1 ())) (m-1))
and evalrr2Safe e n = (match n with 
                       | 0 -> e
                       | m -> if xis_value_of_expr e then e else evalrr1Safe (xJO_red12 e (makerr2 ())) (m-1))

let rec evalrr1SafeDebug e n d = (match n with 
                       | 0 -> e
                       | m -> if xis_value_of_expr e then e else (d () ; evalrr2SafeDebug (xJO_red12 e (makerr1 ())) (m-1) d))
and evalrr2SafeDebug e n d = (match n with 
                       | 0 -> e
                       | m -> if xis_value_of_expr e then e else (d () ; evalrr1SafeDebug (xJO_red12 e (makerr2 ())) (m-1) d))

exception Stop
let stop () = raise Stop
