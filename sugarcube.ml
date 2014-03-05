(* sugarcube *)
let boxc f = E_live_expr (LM_comp f)

let boxe e = E_live_expr (LM_expr e)

let ( >>= ) a b = E_bind (a, b)

let app a b = E_apply (a, b)

let fork a b = app ( app (E_constant CONST_fork) a ) b

let func v t e = E_function (v, t, e)

let fix e = E_fix e

let rec vname n = if n = 0 then O else S(vname (n-1))

let tunit = TE_constants TC_unit

let tfun a b = TE_arrow(a,b)

let id n = E_ident (vname n) 
