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

type typexpr =
| TE_var of typvar
| TE_arrow of typexpr * typexpr
| TE_prod of typexpr * typexpr
| TE_concurrent of typexpr
| TE_sum of typexpr * typexpr

type constant =
| CONST_ret
| CONST_fork

type expr =
| E_ident of value_name
| E_constant of constant
| E_apply of expr * expr
| E_bind of expr * expr
| E_function of value_name * typexpr * expr
| E_live_expr of expr
| E_pair of expr * expr
| E_taggingleft of expr
| E_taggingright of expr
| E_case of expr * value_name * expr * value_name * expr

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
| E_live_expr expr5 -> E_live_expr (subst_expr e_5 x_5 expr5)
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

let select = (selectBranch)

(** val xis_value_of_expr : expr -> bool **)

let rec xis_value_of_expr = function
| E_constant constant5 -> true
| E_function (value_name5, typexpr5, expr5) -> false
| E_live_expr expr5 -> true
| E_pair (e, e') ->
  (match xis_value_of_expr e with
   | true -> xis_value_of_expr e'
   | false -> false)
| E_taggingleft e -> xis_value_of_expr e
| E_taggingright e -> xis_value_of_expr e
| _ -> false


(** val xJO_red1 : expr -> expr **)

let rec xJO_red1 p1 =
  match p1 with
  | E_apply (E_function (x, t, e), v) ->
    (match xis_value_of_expr v with
     | true -> subst_expr v x e
     | _ -> assert false (*  *))
  | E_apply (E_apply (E_constant CONST_fork, E_live_expr e), E_live_expr e') ->
    (match xis_value_of_expr e' with
     | false ->
       (match xis_value_of_expr e with
        | false ->
          (match select with
           | First ->
             (match xJO_red1 e with
              | e'' ->
                E_apply ((E_apply ((E_constant CONST_fork), (E_live_expr
                  e''))), (E_live_expr e'))
              | _ -> assert false (*  *))
           | Second ->
             (match xJO_red1 e' with
              | e'' ->
                E_apply ((E_apply ((E_constant CONST_fork), (E_live_expr
                  e))), (E_live_expr e''))
              | _ -> assert false (*  *))
           | _ -> assert false (*  *))
        | true -> E_live_expr (E_pair (e, (E_live_expr e')))
        | _ -> assert false (*  *))
     | true ->
       (match xis_value_of_expr e with
        | false -> E_live_expr (E_pair ((E_live_expr e), e'))
        | true -> E_live_expr (E_pair (e, e'))
        | _ -> assert false (*  *))
     | _ -> assert false (*  *))
  | E_apply (E_constant CONST_ret, v) ->
    (match xis_value_of_expr v with
     | true -> E_live_expr v
     | _ -> assert false (*  *))
  | E_bind (E_live_expr e, e'') ->
    (match xis_value_of_expr e with
     | false ->
       (match xJO_red1 e with
        | e' -> E_bind ((E_live_expr e'), e'')
        | _ -> assert false (*  *))
     | true -> E_apply (e'', e)
     | _ -> assert false (*  *))
  | E_bind (e, e'') ->
    (match xJO_red1 e with
     | e' -> E_bind (e', e'')
     | _ -> assert false (*  *))
  | E_apply (e, e') ->
    (match xis_value_of_expr e' with
     | false ->
       (match xJO_red1 e' with
        | e'' -> E_apply (e, e'')
        | _ -> assert false (*  *))
     | true ->
       (match xJO_red1 e with
        | e'0 -> E_apply (e'0, e'0)
        | _ -> assert false (*  *))
     | _ -> assert false (*  *))
  | E_pair (e, e'') ->
    (match xis_value_of_expr e with
     | false ->
       (match xJO_red1 e with
        | e' -> E_pair (e', e'')
        | _ -> assert false (*  *))
     | true ->
       (match xJO_red1 e'' with
        | e' -> E_pair (e, e')
        | _ -> assert false (*  *))
     | _ -> assert false (*  *))
  | E_taggingleft e ->
    (match xJO_red1 e with
     | e' -> E_taggingleft e'
     | _ -> assert false (*  *))
  | E_taggingright e ->
    (match xJO_red1 e with
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
    (match xJO_red1 e with
     | e' ->
       (match xis_value_of_expr e with
        | false -> E_case (e', x, e'', x', e''')
        | _ -> assert false (*  *))
     | _ -> assert false (*  *))
  | _ -> assert false (*  *)
