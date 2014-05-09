let e1 = (fun x -> (print_string "First!\n"; () ));;
let e2 = (fun x -> (print_string "Second!\n"; () ));;

let r = E_apply (E_apply (E_constant CONST_fork, E_live_expr (Comp e1)), E_live_expr (Comp e2));;

(**

# let e1 = (fun x -> (print_string "First!\n"; () ));;
val e1 : 'a -> unit = <fun>
# let e2 = (fun x -> (print_string "Second!\n"; () ));;
val e2 : 'a -> unit = <fun>
# let r = E_apply (E_apply (E_constant CONST_fork, E_live_expr (Comp e1)), E_live_expr (Comp e2));;
val r : expr =
  E_apply (E_apply (E_constant CONST_fork, E_live_expr (Comp <fun>)),
   E_live_expr (Comp <fun>))
# let b1 = xJO_red1 r First;;
First!
val b1 : expr =
  E_apply (E_apply (E_constant CONST_fork, E_live_expr None),
   E_live_expr (Comp <fun>))
# let b2 = xJO_red1 r Second;;
Second!
val b2 : expr =
  E_apply (E_apply (E_constant CONST_fork, E_live_expr (Comp <fun>)),
   E_live_expr None)


**)

let e3 = (fun x -> (print_string "Third!\n"; () ));;

let r2 = E_apply (E_apply (E_constant CONST_fork, E_bind (E_live_expr (Comp e1), (E_function (O, TE_constants(TC_unit), E_ident(O)))) ), E_live_expr (Comp e2));;
let r3 = E_apply (E_apply (E_constant CONST_fork, E_bind (E_live_expr (Comp e1), (E_function (O, TE_constants(TC_unit), E_live_expr (Comp e3)))) ), E_live_expr (Comp e2));;
let y =
(E_function (O,
             TE_constants(TC_unit),
             E_apply(
                     (E_function (S(O),
                                  TE_constants(TC_unit),
                                  E_apply(E_ident(O), 
                                          (E_apply(E_ident(S(O)),
                                                   E_ident(S(O))
                                                  )
                                          )
                                         )
                                 )
                     ), 
                     (E_function (S(S(O)),
                                  TE_constants(TC_unit),
                                  E_apply(E_ident(O), 
                                          (E_apply(E_ident(S(S(O))),
                                                   E_ident(S(S(O)))
                                                  )
                                          )
                                         )
                                 )
                     )
                    )
             )
);;

let rec evalRR e = 


# let r = ref 1;;
val r : int ref = {contents = 1}
# let f () = () ;;
val f : unit -> unit = <fun>
# let n = ref 10;;
val n : int ref = {contents = 10}
# let f () = if !n = 0 then () else (r := !r * !n ; n := !n - 1 ; () );;


let fib1 =  E_function (S(S(S(O))),
                TE_constants(TC_unit),
                 E_bind( E_ident(S(S(S(O)))),
                         E_function 
