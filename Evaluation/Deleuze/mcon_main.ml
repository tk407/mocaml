Open Lwc

(* Combined pieces: 2014 May 3 *)

(** commons:  **)
type value_name = int

(** val eq_value_name : value_name -> value_name -> bool **)

let rec eq_value_name n y0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      true)
      (fun n0 ->
      false)
      y0)
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      false)
      (fun n1 ->
      eq_value_name n0 n1)
      y0)
    n

type ident = int

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
| CONST_pair
| CONST_proj1
| CONST_proj2

type expr =
| E_ident of value_name
| E_constant of constant
| E_apply of expr * expr
| E_bind of expr * expr
| E_function of value_name * typexpr * expr
| E_fix of expr
| E_comp of (unit -> expr)
| E_live_expr of expr
| E_pair of expr * expr
| E_taggingleft of expr
| E_taggingright of expr
| E_case of expr * value_name * expr * value_name * expr

type select =
| S_First
| S_Second

(** val list_mem : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec list_mem eq x = function
| [] -> false
| h::t -> if eq h x then true else list_mem eq x t

(** val subst_expr : expr -> value_name -> expr -> expr **)

let rec subst_expr e_5 x_5 = function
| E_ident value_name5 ->
  if eq_value_name value_name5 x_5 then e_5 else E_ident value_name5
| E_constant constant5 -> E_constant constant5
| E_apply (expr5, expr') ->
  E_apply ((subst_expr e_5 x_5 expr5), (subst_expr e_5 x_5 expr'))
| E_bind (expr5, expr') ->
  E_bind ((subst_expr e_5 x_5 expr5), (subst_expr e_5 x_5 expr'))
| E_function (value_name5, typexpr5, expr5) ->
  E_function (value_name5, typexpr5,
    (if list_mem eq_value_name x_5 (value_name5::[])
     then expr5
     else subst_expr e_5 x_5 expr5))
| E_fix e -> E_fix (subst_expr e_5 x_5 e)
| E_comp e -> E_comp (e)                                                    (* By no means should substitution happen here *)
| E_live_expr e -> E_live_expr (subst_expr e_5 x_5 e)
| E_pair (e, e') -> E_pair ((subst_expr e_5 x_5 e), (subst_expr e_5 x_5 e'))
| E_taggingleft e -> E_taggingleft (subst_expr e_5 x_5 e)
| E_taggingright e -> E_taggingright (subst_expr e_5 x_5 e)
| E_case (e1, x1, e2, x2, e3) ->
  E_case ((subst_expr e_5 x_5 e1), x1, (subst_expr e_5 x_5 e2), x2,
    (subst_expr e_5 x_5 e3))

(** val xis_value_of_expr : expr -> bool **)

let rec xis_value_of_expr = function
| E_constant constant5 -> true
| E_apply (expr5, expr') ->
  (match expr5 with
   | E_constant constant5 ->
     (match constant5 with
      | CONST_fork -> xis_value_of_expr expr'
      | CONST_pair -> xis_value_of_expr expr'
      | _ ->
        (match expr5 with
         | E_constant constant6 ->
           (match constant6 with
            | CONST_fork -> xis_value_of_expr expr'
            | CONST_pair -> xis_value_of_expr expr'
            | _ -> false)
         | _ -> false))
   | _ ->
     (match expr5 with
      | E_constant constant5 ->
        (match constant5 with
         | CONST_fork -> xis_value_of_expr expr'
         | CONST_pair -> xis_value_of_expr expr'
         | _ -> false)
      | _ -> false))
| E_function (value_name5, typexpr5, expr5) -> true
| E_live_expr expr5 -> true
| E_pair (e, e') ->
  if xis_value_of_expr e then xis_value_of_expr e' else false
| E_taggingleft e -> xis_value_of_expr e
| E_taggingright e -> xis_value_of_expr e
| _ -> false


(** val xJO_red12 : expr -> selectstar -> expr **)

type selectstar = | Seq of select * (unit -> selectstar)  (* modified coinductive datatype to be lazy *)


(** val xJO_red12 : expr -> selectstar -> expr **)

let rec xJO_red12 p1 p2 =
  match (p1, p2) with
  | (E_apply (E_function (x, t, e), v), s) ->
    (match xis_value_of_expr v with
     | true -> subst_expr v x e
     | false -> E_apply (E_function (x, t, e), (xJO_red12 v s)))                        (* plugin did not detect the combination of two cases *)
  | (E_apply (E_constant CONST_ret, v), s) ->
    (match xis_value_of_expr v with
     | true -> E_live_expr v
     | false -> E_apply (E_constant CONST_ret, (xJO_red12 v s)))                        (* plugin did not detect the combination of two cases *)
  | (E_bind (E_live_expr e, e''), s) ->
    (match xis_value_of_expr e with
     | false ->
       (match xJO_red12 e s with                                                        (* the logical inductive assumption xJO_red12 e s e' converts to this, but this can just be folded in *)
        | e' -> E_bind ((E_live_expr e'), e'')
        | _ -> assert false (*  *))
     | true -> E_apply (e'', e)
     | _ -> assert false (*  *))
  | (E_bind (e, e''), s) ->
    (match xis_value_of_expr e with                                                     (* I had to change the order of the value check and the internal reduction to make sense *)                                                                                                
     | false ->
       (match xJO_red12 e s with                                                        (* the logical inductive assumption xJO_red12 e s e' converts to this, but this can just be folded in *)
        | e' -> E_bind (e', e'')
        | _ -> assert false (*  *))
     | true -> assert false (*  *))                                                     (* Technically this is needed: if e is a value and is not caught by earlier cases, it should fail (it cannot move ahead is it is not a live expression *)
  | (E_apply (E_apply (E_constant CONST_pair, v), v'), s) ->
    (match xis_value_of_expr v with
     | true ->
       (match xis_value_of_expr v' with
        | true -> E_pair (v, v')
        | false -> E_apply (E_apply (E_constant CONST_pair, v), (xJO_red12 v' s)) )   (* plugin did not detect the combination of two cases *)
     | false -> E_apply (E_apply (E_constant CONST_pair, (xJO_red12 v s)), v'))             (* plugin did not detect the combination of two cases *)
  | (E_comp e, s) -> (e ())
  | (E_apply (E_constant CONST_proj1, E_pair (v, v')), s) ->
    (match xis_value_of_expr v with
     | true ->
       (match xis_value_of_expr v' with
        | true -> v
        | false -> E_apply (E_constant CONST_proj1, E_pair (v, (xJO_red12 v' s))))        (* plugin did not detect the combination of two cases *)
     | false -> E_apply (E_constant CONST_proj1, E_pair ((xJO_red12 v s), v')))           (* plugin did not detect the combination of two cases *)
  | (E_apply (E_constant CONST_proj2, E_pair (v, v')), s) ->
    (match xis_value_of_expr v with
     | true ->
       (match xis_value_of_expr v' with
        | true -> v'
        | false -> E_apply (E_constant CONST_proj2, E_pair (v, (xJO_red12 v' s))))           (* plugin did not detect the combination of two cases *)
     | false -> E_apply (E_constant CONST_proj2, E_pair ((xJO_red12 v s), v')))              (* plugin did not detect the combination of two cases *)
  | (E_apply (E_apply (E_constant CONST_fork, E_live_expr e), E_live_expr e'),               (* A combination of issues: reorder of unsafe assumption, no fold *)
     Seq (S_First, s)) ->
    (match xis_value_of_expr e with
     | false ->
       (match xis_value_of_expr e' with
        | false ->
          (match (xJO_red12 e (s () )) with                                                         (* added code to use selectstar *) (* reorder unsafe assumption *)
           | e'' ->
             E_apply ((E_apply ((E_constant CONST_fork), (E_live_expr e''))),
               (E_live_expr e'))
           | _ -> assert false (*  *))
        | true -> E_live_expr (E_taggingright (E_pair ((E_live_expr e), e'))))              (* fold in forkdeath2 *)
     | true -> E_live_expr (E_taggingleft (E_pair (e, (E_live_expr e')))))                  (* fold in forkdeath1 *)     
  | (E_apply (E_apply (E_constant CONST_fork, E_live_expr e), E_live_expr e'),
     Seq (S_Second, s)) ->
    (match xis_value_of_expr e' with
     | false ->
       (match xis_value_of_expr e  with                                                   (* added code to use selectstar *) (* reorder unsafe assumption *)
        | false ->
          (match (xJO_red12 e' (s () )) with
           | e'' ->
             E_apply ((E_apply ((E_constant CONST_fork), (E_live_expr e))),
               (E_live_expr e''))
           | _ -> assert false (*  *))            (* fold in forkdeath1 *)
        | true -> E_live_expr (E_taggingleft (E_pair (e, (E_live_expr e')))))
     | true -> E_live_expr (E_taggingright (E_pair ((E_live_expr e), e'))))                 (* fold in forkdeath2 *)
(*  | (E_apply (E_apply (E_constant CONST_fork, E_live_expr v), E_live_expr e),               (* the death cases are not actually needed: the folds above cover them *)
     s) ->
    (match xis_value_of_expr e with
     | true -> E_live_expr (E_taggingleft (E_pair (v, (E_live_expr e))))
     | _ -> assert false (*  *))
  | (E_apply (E_apply (E_constant CONST_fork, E_live_expr e), E_live_expr v'),
     s) ->
    (match xis_value_of_expr v' with
     | true -> E_live_expr (E_taggingright (E_pair ((E_live_expr e), v')))
     | _ -> assert false (*  *)) *)
  | (E_apply (e, e'), s) ->
    (match xis_value_of_expr e with
     | false ->
       (match xJO_red12 e s with
        | e'' -> E_apply (e'', e')
        | _ -> assert false (*  *))
     | true ->
       (match xJO_red12 e' s with
        | e'' -> E_apply (e, e'')
        | _ -> assert false (*  *))
     | _ -> assert false (*  *))
  | (E_fix E_function (x, t, e), s) ->
    subst_expr (E_fix (E_function (x, t, e))) x e
  | (E_fix e, s) ->
    (match xJO_red12 e s with
     | e' -> E_fix e'
     | _ -> assert false (*  *))
  | (E_pair (e, e''), s) ->
    (match xis_value_of_expr e with
     | false ->
       (match xJO_red12 e s with
        | e' -> E_pair (e', e'')
        | _ -> assert false (*  *))
     | true ->
       (match xJO_red12 e'' s with
        | e' -> E_pair (e, e')
        | _ -> assert false (*  *))
     | _ -> assert false (*  *))
  | (E_taggingleft e, s) ->
    (match xJO_red12 e s with
     | e' -> E_taggingleft e'
     | _ -> assert false (*  *))
  | (E_taggingright e, s) ->
    (match xJO_red12 e s with
     | e' -> E_taggingright e'
     | _ -> assert false (*  *))
  | (E_case (E_taggingleft v, x, e, x', e'), s) ->
    (match xis_value_of_expr v with
     | true -> subst_expr v x e
     | _ -> assert false (*  *))
  | (E_case (E_taggingright v, x, e, x', e'), s) ->
    (match xis_value_of_expr v with
     | true -> subst_expr v x' e'
     | _ -> assert false (*  *))
  | (E_case (e, x, e'', x', e'''), s) ->                                                            (* reorder unsafe assumption *)
    (match xis_value_of_expr e with                                                                 (*  *)
     | false ->
       (match xJO_red12 e s with
        | e' -> E_case (e', x, e'', x', e''')
        | _ -> assert false (*  *))
     | _ -> assert false (*  *))
  | _ -> assert false (*  *)


(* sugarcube: 2014 May 3 *)
