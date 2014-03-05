(* sugarcube *)
let boxc f = E_live_expr (LM_comp f)

let boxe e = E_live_expr (LM_expr e)

let ( >>= ) a b = E_bind (a, b)

let app a b = E_apply (a, b)

let fork a b = app ( app (E_constant CONST_fork) a ) b

let func v t e = E_function (v, t, e)

let fix e = E_fix e

let rec vname n = if n = 0 then O else S(vname (n-1))

let cunit = E_constant CONST_unit

let tunit = TE_constants TC_unit

let tfun a b = TE_arrow(a,b)

let id n = E_ident (vname n) 

let rec makerr1 () = Seq(S_First, makerr2) 
and makerr2 () = Seq(S_Second, makerr1) 

let _ = Random.self_init()

let rec makerand () = if Random.bool() then Seq(S_First, makerand) else Seq(S_Second, makerand)

let rec evalrr1 e n = (match n with 
                       | 0 -> e
                       | m -> evalrr2 (xJO_red12 e (makerr1 ())) (m-1))
and evalrr2 e n = (match n with 
                       | 0 -> e
                       | m -> evalrr1 (xJO_red12 e (makerr2 ())) (m-1))

let rec evalrand e n = (match n with 
                       | 0 -> e
                       | m -> evalrand (xJO_red12 e (makerand ())) (m-1))
