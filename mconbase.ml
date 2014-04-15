type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

type sumbool =
| Left
| Right

type value_name = nat

(** val eq_value_name : value_name -> value_name -> sumbool **)

let rec eq_value_name n y0 =
  match n with
  | O ->
    (match y0 with
     | O -> Left
     | S n0 -> Right)
  | S n0 ->
    (match y0 with
     | O -> Right
     | S n1 -> eq_value_name n0 n1)

type ident = nat

type typvar =
  ident
  (* singleton inductive, whose constructor was TV_ident *)

type typconst =
| TC_unit

type typexpr =
| TE_constants of typconst
| TE_var of typvar
| TE_arrow of typexpr * typexpr
| TE_prod of typexpr * typexpr
| TE_concurrent of typexpr
| TE_sum of typexpr * typexpr

type constant =
| CONST_ret
| CONST_fork
| CONST_unit

type expr =
| E_ident of value_name
| E_constant of constant
| E_apply of expr * expr
| E_bind of expr * expr
| E_function of value_name * typexpr * expr
| E_live_expr of outstanding_comp
| E_pair of expr * expr
| E_taggingleft of expr
| E_taggingright of expr
| E_case of expr * value_name * expr * value_name * expr
and outstanding_comp = 
| None
| Comp of ( unit -> unit)
| Expr of expr

(** val list_mem : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 list -> bool **)

let rec list_mem eq x = function
| Nil -> false
| Cons (h, t) ->
  (match eq h x with
   | Left -> true
   | Right -> list_mem eq x t)

(** val subst_expr : expr -> value_name -> expr -> expr **)

let rec subst_expr e_5 x_5 = function
| E_ident value_name5 ->
  (match eq_value_name value_name5 x_5 with
   | Left -> e_5
   | Right -> E_ident value_name5)
| E_constant constant5 -> E_constant constant5
| E_apply (expr5, expr') ->
  E_apply ((subst_expr e_5 x_5 expr5), (subst_expr e_5 x_5 expr'))
| E_bind (expr5, expr') ->
  E_bind ((subst_expr e_5 x_5 expr5), (subst_expr e_5 x_5 expr'))
| E_function (value_name5, typexpr5, expr5) ->
  E_function (value_name5, typexpr5,
    (match list_mem eq_value_name x_5 (Cons (value_name5, Nil)) with
     | true -> expr5
     | false -> subst_expr e_5 x_5 expr5))
| E_live_expr oc -> 
     (match oc with
       | None -> E_live_expr None
       | Comp c -> E_live_expr (Comp c)
       | Expr expr5 -> E_live_expr (Expr (subst_expr e_5 x_5 expr5)))
| E_pair (e, e') -> E_pair ((subst_expr e_5 x_5 e), (subst_expr e_5 x_5 e'))
| E_taggingleft e -> E_taggingleft (subst_expr e_5 x_5 e)
| E_taggingright e -> E_taggingright (subst_expr e_5 x_5 e)
| E_case (e1, x1, e2, x2, e3) ->
  E_case ((subst_expr e_5 x_5 e1), x1, (subst_expr e_5 x_5 e2), x2,
    (subst_expr e_5 x_5 e3))

type selectSet =
| First
| Second
| Both

(** val select : selectSet **)

let selectBranch = First

(*let select = (selectBranch) *)
(** val xis_value_of_expr : expr -> bool **)

let rec xis_value_of_expr = function
| E_constant constant5 -> true
| E_apply (expr5, expr') ->
  (match expr5 with
   | E_constant constant5 ->
     (match constant5 with
      | CONST_fork -> xis_value_of_expr expr'
      | _ -> false)
   | _ -> false)
| E_function (value_name5, typexpr5, expr5) -> true
| E_live_expr expr5 -> true
| E_pair (e, e') ->
  (match xis_value_of_expr e with
   | true -> xis_value_of_expr e'
   | false -> false)
| E_taggingleft e -> xis_value_of_expr e
| E_taggingright e -> xis_value_of_expr e
| _ -> false

(** val xis_forkvalue : expr -> bool **)

let rec xis_forkvalue = function
| E_constant constant5 ->
  (match constant5 with
   | CONST_unit -> false
   | _ -> true)
| E_apply (expr5, expr') ->
  (match expr5 with
   | E_constant constant5 ->
     (match constant5 with
      | CONST_fork -> xis_value_of_expr expr'
      | _ -> false)
   | _ -> false)
| _ -> false

let rec live_val = function
| None -> true
| Comp f -> false
| Expr e -> (xis_value_of_expr e)


(** val xJO_red1 : expr -> expr **)

let rec xJO_red1 p1 select =
  match p1 with
  | E_apply (E_function (x, t, e), v) ->
    (match xis_value_of_expr v with
     | true -> subst_expr v x e
     | _ -> assert false (*  *))
  | E_apply (E_constant CONST_ret, v) ->
    (match xis_value_of_expr v with
     | true -> E_live_expr (Expr v)
     | _ -> assert false (*  *))
  | E_bind ((E_live_expr oc), e'') ->
    (match oc with 
    | None -> e''
    | Comp f ->  (f () ; E_apply (e'', E_constant(CONST_unit))) 
    | Expr e -> 
    ((match xis_value_of_expr e with
     | false ->
       (match xJO_red1 e select with
        | e' -> E_bind ((E_live_expr (Expr e')), e'')
        | _ -> assert false (*  *))
     | true -> E_apply (e'', e)
     | _ -> assert false (*  *))))
  | E_bind (e, e'') ->
    (match xJO_red1 e select with
     | e' -> E_bind (e', e'')
     | _ -> assert false (*  *))
  | E_apply (E_apply (E_constant CONST_fork, E_live_expr e), E_live_expr e') ->
    (match live_val e' with
     | false ->
       (match live_val e with
        | false ->
          (match select with
           | First ->
             (match e with
              | Comp f -> (f () ; E_apply ((E_apply ((E_constant CONST_fork), (E_live_expr
                  None))), (E_live_expr e')))
              | Expr e''' -> let e'' = xJO_red1 e''' select in E_apply ((E_apply ((E_constant CONST_fork), (E_live_expr
                  (Expr e'')))), (E_live_expr e'))
              | _ -> assert false (*  *))
           | Second ->
             (match e' with
              | Comp f -> ( f () ; E_apply ((E_apply ((E_constant CONST_fork), (E_live_expr
                  e))), (E_live_expr None)))
              | Expr e''' -> let e'' = xJO_red1 e''' select in E_apply ((E_apply ((E_constant CONST_fork), (E_live_expr
                  e))), (E_live_expr (Expr e'')))
              | _ -> assert false (*  *))
           | _ -> assert false (*  *))
        | true -> 
             (match e with
              | None -> E_live_expr (Expr (E_pair ( E_constant CONST_unit , (E_live_expr e'))))
              | Expr d -> E_live_expr (Expr (E_pair (d, (E_live_expr e')))))
        | _ -> assert false (*  *))
     | true ->
       match e with
        | None -> E_live_expr (Expr (E_pair ( E_constant CONST_unit , (E_live_expr e'))))
        | Comp f -> ( f () ; E_apply ((E_apply ((E_constant CONST_fork), (E_live_expr
                  e))), (E_live_expr None)))
        | Expr d -> (match xis_value_of_expr d with
         | false -> E_live_expr (Expr (E_pair (d, E_live_expr e')))
         | _ -> assert false (*  *))
     | _ -> assert false (*  *))
  | E_apply (E_apply (E_constant CONST_fork, v), v') ->
    (match xis_value_of_expr v' with
     | false ->
       (match xJO_red1 v' select with
        | e' -> E_apply ((E_apply ((E_constant CONST_fork), v)), e')
        | _ -> assert false (*  *))
     | true ->
       (match xis_value_of_expr v with
        | false ->
          (match xJO_red1 v select with
           | e' -> E_apply ((E_apply ((E_constant CONST_fork), e')), v')
           | _ -> assert false (*  *))
        | true ->
          (match xis_forkvalue v' with
           | false ->
             (match xis_value_of_expr v with
              | true -> E_live_expr (Expr (E_pair (v, v')))
              | _ -> assert false (*  *))
           | true ->
             (match xis_forkvalue v with
              | false -> E_live_expr (Expr (E_pair (v, v')))
              | true -> E_live_expr (Expr (E_pair (v, v')))
              | _ -> assert false (*  *))
           | _ -> assert false (*  *))
        | _ -> assert false (*  *))
     | _ -> assert false (*  *))
  | E_apply (e, e') ->
    (match xis_value_of_expr e' with
     | false ->
       (match xJO_red1 e' select with
        | e'' -> E_apply (e, e'')
        | _ -> assert false (*  *))
     | true ->
       (match xJO_red1 e select with
        | e'0 -> E_apply (e'0, e'0)
        | _ -> assert false (*  *))
     | _ -> assert false (*  *))
  | E_pair (e, e'') ->
    (match xis_value_of_expr e with
     | false ->
       (match xJO_red1 e select with
        | e' -> E_pair (e', e'')
        | _ -> assert false (*  *))
     | true ->
       (match xJO_red1 e'' select with
        | e' -> E_pair (e, e')
        | _ -> assert false (*  *))
     | _ -> assert false (*  *))
  | E_taggingleft e ->
    (match xJO_red1 e select with
     | e' -> E_taggingleft e'
     | _ -> assert false (*  *))
  | E_taggingright e ->
    (match xJO_red1 e select with
     | e' -> E_taggingright e'
     | _ -> assert false (*  *))
  | E_case (E_taggingleft v, x, e, x', e') ->
    (match xis_value_of_expr v with
     | true -> subst_expr v x e
     | _ -> assert false (*  *))
  | E_case (E_taggingright v, x, e, x', e') ->
    (match xis_value_of_expr v with
     | true -> subst_expr v x' e'
     | _ -> assert false (*  *))
  | E_case (e, x, e'', x', e''') ->
    (match xJO_red1 e select with
     | e' ->
       (match xis_value_of_expr e with
        | false -> E_case (e', x, e'', x', e''')
        | _ -> assert false (*  *))
     | _ -> assert false (*  *))
  | _ -> assert false (*  *)

