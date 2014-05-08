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

type typexpr =
| TE_unit
| TE_arrow of typexpr * typexpr
| TE_prod of typexpr * typexpr
| TE_concurrent of typexpr
| TE_sum of typexpr * typexpr

type expr =
| E_ident of value_name
| E_unit
| E_apply of expr * expr
| E_bind of expr * expr
| E_function of value_name * typexpr * expr
| E_fix of expr
| E_comp of (unit -> expr)                                                   (* modified placeholder *)
| E_live_expr of expr
| E_pair of expr * expr
| E_inpair of expr * expr
| E_proj1 of expr
| E_proj2 of expr
| E_fork of expr * expr
| E_ret of expr
| E_taggingleft of expr
| E_taggingright of expr
| E_case of expr * value_name * expr * value_name * expr

(** val list_mem : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec list_mem eq x = function
| [] -> false
| h::t -> if eq h x then true else list_mem eq x t

(** val subst_expr : expr -> value_name -> expr -> expr **)

let rec subst_expr e_5 x_5 = function
| E_ident value_name5 ->
  if eq_value_name value_name5 x_5 then e_5 else E_ident value_name5
| E_unit -> E_unit
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
| E_comp e -> E_comp (subst_expr e_5 x_5 e)                                      (* this substitution should not occur! *)
| E_live_expr e -> E_live_expr (subst_expr e_5 x_5 e)
| E_pair (e, e') -> E_pair ((subst_expr e_5 x_5 e), (subst_expr e_5 x_5 e'))
| E_inpair (e, e') ->
  E_inpair ((subst_expr e_5 x_5 e), (subst_expr e_5 x_5 e'))
| E_proj1 e -> E_proj1 (subst_expr e_5 x_5 e)
| E_proj2 e -> E_proj2 (subst_expr e_5 x_5 e)
| E_fork (e, e') -> E_fork ((subst_expr e_5 x_5 e), (subst_expr e_5 x_5 e'))
| E_ret e -> E_ret (subst_expr e_5 x_5 e)
| E_taggingleft e -> E_taggingleft (subst_expr e_5 x_5 e)
| E_taggingright e -> E_taggingright (subst_expr e_5 x_5 e)
| E_case (e1, x1, e2, x2, e3) ->
  E_case ((subst_expr e_5 x_5 e1), x1, (subst_expr e_5 x_5 e2), x2,
    (subst_expr e_5 x_5 e3))

(** val xis_value_of_expr : expr -> bool **)

let rec xis_value_of_expr = function
| E_unit -> true
| E_function (value_name5, typexpr5, expr5) -> true
| E_live_expr e -> true
| E_pair (e, e') ->
  if xis_value_of_expr e then xis_value_of_expr e' else false
| E_taggingleft e -> xis_value_of_expr e
| E_taggingright e -> xis_value_of_expr e
| _ -> false

(** val xJO_red12 : expr -> selectstar -> expr **)

type selectstar = | Seq of select * (unit -> selectstar)  (* modified coinductive datatype to be lazy *)


let rec xJO_red12 p1 p2 =
  match (p1, p2) with
  | (E_apply (E_function (x, t, e), v), s) ->
    (match xis_value_of_expr v with
     | true -> subst_expr v x e
     | false -> E_apply (E_function (x, t, e), (xJO_red12 v s)))
  | (E_ret v, s) ->
    (match xis_value_of_expr v with
     | true -> E_live_expr v
     | false ->
       (match xJO_red12 v s with
        | v' -> E_ret v'
        | _ -> assert false (*  *))
    (* | _ -> assert false (*  *) *))
  | (E_bind (E_live_expr e, e''), s) ->
    (match xis_value_of_expr e with
     | false ->
       (match xJO_red12 e s with
        | e' -> E_bind ((E_live_expr e'), e'')
        | _ -> assert false (*  *))
     | true -> E_apply (e'', e)
     | _ -> assert false (*  *))
  | (E_bind (e, e''), s) ->
    (match xis_value_of_expr e with
     | false ->
       (match xJO_red12 e s with
        | e' -> E_bind (e', e'')
        | _ -> assert false (*  *))
     | _ -> assert false (*  *))
  | (E_inpair (v, v'), s) ->
    (match xis_value_of_expr v with
     | true ->
       (match xis_value_of_expr v' with
        | true -> E_pair (v, v')
        | false ->
          (match xJO_red12 v' s with
           | v'' -> E_inpair (v, v'')
           | _ -> assert false (*  *))
        | _ -> assert false (*  *))
     | false ->
       (match xJO_red12 v s with
        | v'' -> E_inpair (v'', v')
        | _ -> assert false (*  *))
     | _ -> assert false (*  *))
  | (E_comp e, s) -> (e ())
  | (E_proj1 E_pair (v, v'), s) ->
    (match xis_value_of_expr v' with
     | true ->
       (match xis_value_of_expr v with
        | true -> v
        | _ -> assert false (*  *))
     | false -> E_proj1 (xJO_red12 (E_pair (v, v')) s))            (* combine the reduce and do *)
  | (E_proj2 E_pair (v, v'), s) ->
    (match xis_value_of_expr v' with
     | true ->
       (match xis_value_of_expr v with
        | true -> v'
        | _ -> assert false (*  *))
     | false -> E_proj2 (xJO_red12 (E_pair (v, v')) s))             (* combine the reduce and do *)
 | (E_fork (E_live_expr e, E_live_expr e'), Seq (S_First, s)) ->
    (match xis_value_of_expr e with                                       (* reordered unsafe assumption *)
     | false ->
       (match xis_value_of_expr e' with
        | false ->
          (match xJO_red12 e (s ()) with                                          (* Added code to use selecstar *)
           | e'' -> E_fork ((E_live_expr e''), (E_live_expr e'))
           | _ -> assert false (*  *))
        | true -> E_live_expr (E_taggingright (E_pair ((E_live_expr e), e'))))                                       (* Fold in forkdeath 2 *)
     | true -> E_live_expr (E_taggingleft (E_pair (e, (E_live_expr e')))))                                          (* Fold in forkdeath 1 *)
  | (E_fork (E_live_expr e, E_live_expr e'), Seq (S_Second, s)) ->
    (match xis_value_of_expr e'  with                                                        (* reordered unsafe assumption *)
     | false ->
       (match xis_value_of_expr e with
        | false ->
          (match xJO_red12 e' (s ()) with                                        (* Added code to use selecstar *)
           | e'' -> E_fork ((E_live_expr e), (E_live_expr e''))
           | _ -> assert false (*  *))
        | true -> E_live_expr (E_taggingleft (E_pair (e, (E_live_expr e')))))                                 (* Fold in forkdeath 1 *)
     | true -> E_live_expr (E_taggingright (E_pair ((E_live_expr e), e'))))                                   (* Fold in forkdeath 2 *)
 (* | (E_fork (E_live_expr v, E_live_expr e), s) ->
    (match xis_value_of_expr e with
     | true -> E_live_expr (E_taggingleft (E_pair (v, (E_live_expr e))))                       (* Folded *)
     | _ -> assert false (*  *)) *)
  | (E_fork (e, e'), s) ->
    (match xis_value_of_expr e with
     | false ->
       (match xJO_red12 e s with
        | e'' -> E_fork (e'', e')
        | _ -> assert false (*  *))
     | true ->
       (match xis_value_of_expr e' with                                                          (* reordered unsafe assumption *)
        | false ->
          (match xJO_red12 e' s with
           | e'' -> E_fork (e, e'')
           | _ -> assert false (*  *))
        | _ -> assert false (*  *))
     | _ -> assert false (*  *))
 (*  | (E_fork (E_live_expr e, E_live_expr v'), s) ->
    (match xis_value_of_expr v' with
     | true -> E_live_expr (E_taggingright (E_pair ((E_live_expr e), v')))                      (* Folded *)
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
  | (E_case (e, x, e'', x', e'''), s) ->
    (match xJO_red12 e s with
     | e' ->
       (match xis_value_of_expr e with
        | false -> E_case (e', x, e'', x', e''')
        | _ -> assert false (*  *))
     | _ -> assert false (*  *))
  | _ -> assert false (*   *))


(*
type value_name = int

type typexpr =
| TE_unit
| TE_arrow of typexpr * typexpr
| TE_prod of typexpr * typexpr
| TE_concurrent of typexpr
| TE_sum of typexpr * typexpr

type expr =
| E_ident of value_name
| E_unit
| E_apply of expr * expr
| E_bind of expr * expr
| E_function of value_name * typexpr * expr
| E_fix of expr
| E_comp of expr
| E_live_expr of expr
| E_pair of expr * expr
| E_inpair of expr * expr
| E_proj1 of expr
| E_proj2 of expr
| E_fork of expr * expr
| E_ret of expr
| E_taggingleft of expr
| E_taggingright of expr
| E_case of expr * value_name * expr * value_name * expr

(** val xis_value_of_expr : expr -> bool **)

let rec xis_value_of_expr = function
| E_unit -> true
| E_function (value_name5, typexpr5, expr5) -> true
| E_live_expr e -> true
| E_pair (e, e') ->
  if xis_value_of_expr e then xis_value_of_expr e' else false
| E_taggingleft e -> xis_value_of_expr e
| E_taggingright e -> xis_value_of_expr e
| _ -> false

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
| E_unit -> E_unit
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
| E_comp e -> E_comp (subst_expr e_5 x_5 e)
| E_live_expr e -> E_live_expr (subst_expr e_5 x_5 e)
| E_pair (e, e') -> E_pair ((subst_expr e_5 x_5 e), (subst_expr e_5 x_5 e'))
| E_inpair (e, e') ->
  E_inpair ((subst_expr e_5 x_5 e), (subst_expr e_5 x_5 e'))
| E_proj1 e -> E_proj1 (subst_expr e_5 x_5 e)
| E_proj2 e -> E_proj2 (subst_expr e_5 x_5 e)
| E_fork (e, e') -> E_fork ((subst_expr e_5 x_5 e), (subst_expr e_5 x_5 e'))
| E_ret e -> E_ret (subst_expr e_5 x_5 e)
| E_taggingleft e -> E_taggingleft (subst_expr e_5 x_5 e)
| E_taggingright e -> E_taggingright (subst_expr e_5 x_5 e)
| E_case (e1, x1, e2, x2, e3) ->
  E_case ((subst_expr e_5 x_5 e1), x1, (subst_expr e_5 x_5 e2), x2,
    (subst_expr e_5 x_5 e3))



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

*)
(*
let rec xJO_red12 p1 p2 =
  match (p1, p2) with
  | (E_apply (E_function (x, t, e), v), s) ->
    (match xis_value_of_expr v with
     | true -> subst_expr v x e
     | false -> E_apply (E_function (x, t, e), (xJO_red12 v s)))    (* if v is not a value, reduce it. Reason Coq and OCaml pattern matches differ, plugin did not detect *)
  | (E_apply (E_constant CONST_ret, v), s) ->
    (match xis_value_of_expr v with
     | true -> E_live_expr (LM_expr v)
     | false -> E_apply (E_constant CONST_ret, (xJO_red12 v s))) (* if v is not a value, reduce it. Reason Coq and OCaml pattern matches differ, plugin did not detect *)
  | (E_bind (E_live_expr LM_expr e, e''), s) ->
    (match xis_value_of_expr e with
     | false ->
       (match xJO_red12 e s with
        | e' -> E_bind ((E_live_expr (LM_expr e')), e'')
       (* | _ -> assert false (*  *) *))   (* No such possibility *)
     | true -> E_apply (e'', e)
 (*    | _ -> assert false (*  *) *) )      (* No such possibility *)
  | (E_bind (E_live_expr (LM_comp f), e''), s) -> ( f () ; E_apply (e'', (E_constant CONST_unit)))   (* !!!!!! computation and bind has not been handled *)    
  | (E_bind (e, e''), s) ->
    (match xJO_red12 e s with
     | e' -> E_bind (e', e'')
  (*   | _ -> assert false (*  *) *) )    (* No such possibility *)
  | (E_apply (E_apply (E_constant CONST_fork, E_live_expr LM_expr v),
              E_live_expr LM_expr v'), Seq (S_First, s)) ->
    (match xis_value_of_expr v with 
     | false ->
       (match xis_value_of_expr v' with
        | false ->
          (match  xJO_red12 v (s () ) with
           | e'' ->
             E_apply ((E_apply ((E_constant CONST_fork), (E_live_expr
               (LM_expr e'')))), (E_live_expr (LM_expr v'))))
      (*     | _ -> assert false (*  *))  *)  (* No such possibility *)
        | true -> (match xis_value_of_expr v with   (* the second one is a value: return *)
                   | true -> E_live_expr (LM_expr (E_taggingleft (E_taggingleft (E_pair ((v), (v')))))) (* Both are values, return both *)
                   | false -> E_live_expr (LM_expr (E_taggingright (E_pair ((E_live_expr (LM_expr v)), (v')))))  ))  (* Only the second element is a value, return that way *) 
     | true -> (match xis_value_of_expr v' with   (* the first one is a value: return *)
                   | true -> E_live_expr (LM_expr (E_taggingleft (E_taggingleft (E_pair ((v), (v')))))) (* Both are values, return both *)
                   | false -> E_live_expr (LM_expr (E_taggingleft (E_taggingright (E_pair ((v), (E_live_expr (LM_expr v'))))))) (* Only the first one is a value *) ))   
  | (E_apply (E_apply (E_constant CONST_fork, E_live_expr LM_expr e),
              E_live_expr LM_expr e'), Seq (S_Second, s)) ->
    (match xis_value_of_expr e' with   
     | false -> 
       (match xJO_red12 e' (s ()) with
        | e'' ->
          (match xis_value_of_expr e with  
           | false ->
               E_apply ((E_apply ((E_constant CONST_fork), (E_live_expr (LM_expr e)))), (E_live_expr (LM_expr e'')))
           | true -> (match xis_value_of_expr e' with   (* the first one is a value: return *)
                      | true -> E_live_expr (LM_expr (E_taggingleft (E_taggingleft (E_pair ((e), (e')))))) (* Both are values, return both *)
                      | false -> E_live_expr (LM_expr (E_taggingleft (E_taggingright (E_pair ((e), (E_live_expr (LM_expr e'))))))) (* Only the first one is a value *) ))  )
     | true -> (match xis_value_of_expr e with   (* the second one is a value: return *)
                | true -> E_live_expr (LM_expr (E_taggingleft (E_taggingleft (E_pair ((e), (e')))))) (* Both are values, return both *)
                | false -> E_live_expr (LM_expr (E_taggingright (E_pair ((E_live_expr (LM_expr e)), (e')))))  )  
    (* | _ -> assert false (*  *) *) )  (* No such possibility *)
  | (E_apply (E_apply (E_constant CONST_fork, E_live_expr (LM_comp f)),     (* Do comp inserted *)
              E_live_expr LM_expr e), s) ->                                  (* Added the actual OCaml function to the placeholder *)
   ( f () ; E_live_expr (LM_expr (E_taggingleft (E_taggingright (E_pair ((E_constant
      CONST_unit), (E_live_expr (LM_expr e))))))) )
  | (E_apply (E_apply (E_constant CONST_fork, E_live_expr LM_expr e),
              E_live_expr (LM_comp f)), s) ->                                 (* Added the actual OCaml function to the placeholder *)
   ( f () ; E_live_expr (LM_expr (E_taggingright (E_pair ((E_live_expr (LM_expr e)),
      (E_constant CONST_unit))))) )
  | (E_apply (E_apply (E_constant CONST_fork, E_live_expr ( LM_comp f )),
              E_live_expr ( LM_comp g )), s) ->                               (* Added the actual OCaml function to the placeholder *)
  (f () ; g () ;  E_live_expr (LM_expr (E_taggingleft (E_taggingleft (E_pair ((E_constant
      CONST_unit), (E_constant CONST_unit)))))))
(*  | (E_apply (E_apply (E_constant CONST_fork, E_live_expr LM_expr v),   (* Technically this clause is redundant, as the above manual changes incorporate it *)
              E_live_expr LM_expr v'), s) ->
    (match xis_value_of_expr v' with
     | true ->
       (match xis_value_of_expr v with
        | true -> E_live_expr (LM_expr (E_taggingleft (E_taggingleft (E_pair ((v), (v'))))))  (* Appearantly missing tags *)
        | false ->
          E_live_expr (LM_expr (E_taggingright (E_pair ((E_live_expr (LM_expr v)), (v')))))
       (* | _ -> assert false (*  *) *) )   (* No such possibility *)
     | false ->
       (match xis_value_of_expr v with
        | true ->
          E_live_expr (LM_expr (E_pair (v, (E_live_expr (LM_expr v')))))
        | _ -> assert false (*  *))
     | _ -> assert false (*  *)) *)
  | (E_apply (E_apply (E_constant CONST_fork, v), E_live_expr lm), s) ->   
    (match xis_value_of_expr v with                               (* Reorder clauses as they make no sense this way around *)
     | false ->
       (match  xJO_red12 v s with
        | e' ->
          E_apply ((E_apply ((E_constant CONST_fork), e')), (E_live_expr lm))
       (* | _ -> assert false (*  *) *) )            (* No such possibility *)
     | true -> assert false (*  *))                  (* This clause have been handled *)
  | (E_apply (E_apply (E_constant CONST_fork, v), v'), s) ->
    (match xis_value_of_expr v' with                                    (* Reorder clauses as they make no sense this way around *)
     | false ->
       (match  xJO_red12 v' s with
        | e' -> E_apply ((E_apply ((E_constant CONST_fork), v)), e')
       (* | _ -> assert false (*  *) *) )                        (* No such possibility *)
     | true -> assert false (*  *))                       (* There are no other possibilities *)
  | (E_fix e, s) ->                                       (* inserted fix_move -> fix_app *)
    (match xJO_red12 e s with
     | e' -> E_fix e'
    (* | _ -> assert false (*  *) *) )                    (* There are no other possibilities *)
  | (E_apply (E_fix v, v'), s) ->
    (match xis_value_of_expr v' with
     | true ->
       (match xis_value_of_expr v with
        | true -> E_apply ((E_fix v), (E_apply (v, v')))
        | false -> E_apply ((xJO_red12 (E_fix v) s), v') )     (* it can only be true or false *)
     | false -> E_apply (E_fix v, (xJO_red12 v' s)) )
  | (E_apply (e, e'), s) ->
    (match xis_value_of_expr e' with
     | false ->
       (match xJO_red12 e' s with
        | e'' -> E_apply (e, e'')
       (* | _ -> assert false (*  *) *) )                 (* No such possibility *)
     | true ->
       (match xJO_red12 e s with
        | e'0 -> E_apply (e'0, e')                        (* !!!! There must be a typo here! *)
       (* | _ -> assert false (*  *) *) )                  (* No  such possibility *)
    (* | _ -> assert false (*  *) *) )                     (* No such possibility *)
  | (E_pair (e, e''), s) ->                                (* pair to case inserted *)
    (match xis_value_of_expr e with
     | false ->
       (match xJO_red12 e s with
        | e' -> E_pair (e', e'')
       (* | _ -> assert false (*  *) *) )     (* No other possibilities *)
     | true ->
       (match xJO_red12 e'' s with
        | e' -> E_pair (e, e')
      (*  | _ -> assert false (*  *) *) )     (* No other possibilities *)
    (* | _ -> assert false (*  *) *) )        (* No other possibilities *)
  | (E_taggingleft e, s) ->
    (match xJO_red12 e s with
     | e' -> E_taggingleft e'
   (*  | _ -> assert false (*  *) *))         (* No other possibilities *)
  | (E_taggingright e, s) ->
    (match xJO_red12 e s with
     | e' -> E_taggingright e'
   (*  | _ -> assert false (*  *) *) )        (* No other possibilities *)
  | (E_case (E_taggingleft v, x, e, x', e'), s) ->
    (match xis_value_of_expr v with
     | true -> subst_expr v x e
     | false -> (match xJO_red12 v s with       (* adding reduction so that we preserve semantics *)
                 | v' -> (E_case (E_taggingleft v', x, e, x', e'))
             (*  | _ -> assert false (*  *) *) )        (* No other possibilities *))
  | (E_case (E_taggingright v, x, e, x', e'), s) ->
    (match xis_value_of_expr v with
     | true -> subst_expr v x' e'
     | false -> (match xJO_red12 v s with       (* adding reduction so that we preserve semantics *)
                 | v' -> (E_case (E_taggingright v', x, e, x', e'))
             (*  | _ -> assert false (*  *) *) ))
  | (E_case (e, x, e'', x', e'''), s) ->
    (match xis_value_of_expr e with                      (* Technically makes no difference, but reorder these clauses, so that we first check and then reduce *)
     | false ->
       (match xJO_red12 e s with
        | e' -> E_case (e', x, e'', x', e''')
       (* | _ -> assert false (*  *) *) )                (* No such possibility *)
     | true -> assert false (*  *))                     (* There are no other possibilities *)
  | _ -> assert false (*  *)


(*


forkdocomp1 -> forkdocomp12

let rec xJO_red12 p1 p2 =
  match (p1, p2) with
  | (E_apply (E_apply (E_constant CONST_fork, E_live_expr LM_comp),
              E_live_expr LM_expr e), s) ->
    E_live_expr (LM_expr (E_taggingleft (E_taggingright (E_pair ((E_constant
      CONST_unit), (E_live_expr (LM_expr e)))))))
  | (E_apply (E_apply (E_constant CONST_fork, E_live_expr LM_expr e),
              E_live_expr LM_comp), s) ->
    E_live_expr (LM_expr (E_taggingright (E_pair ((E_live_expr (LM_expr e)),
      (E_constant CONST_unit)))))
  | (E_apply (E_apply (E_constant CONST_fork, E_live_expr LM_comp),
              E_live_expr LM_comp), s) ->
    E_live_expr (LM_expr (E_taggingleft (E_taggingleft (E_pair ((E_constant
      CONST_unit), (E_constant CONST_unit))))))
  | _ -> assert false (*  *)


pair1 -> evalcase

let rec xJO_red12 p1 p2 =
  match (p1, p2) with
  | (E_pair (e, e''), s) ->
    (match xis_value_of_expr e with
     | false ->
       (match xJO_red12 e s with
        | e' -> E_pair (e', e'')
       (* | _ -> assert false (*  *) *) )     (* No other possibilities *)
     | true ->
       (match xJO_red12 e'' s with
        | e' -> E_pair (e, e')
      (*  | _ -> assert false (*  *) *) )     (* No other possibilities *)
    (* | _ -> assert false (*  *) *) )        (* No other possibilities *)
  | (E_taggingleft e, s) ->
    (match xJO_red12 e s with
     | e' -> E_taggingleft e'
   (*  | _ -> assert false (*  *) *))         (* No other possibilities *)
  | (E_taggingright e, s) ->
    (match xJO_red12 e s with
     | e' -> E_taggingright e'
   (*  | _ -> assert false (*  *) *) )        (* No other possibilities *)
  | (E_case (E_taggingleft v, x, e, x', e'), s) ->
    (match xis_value_of_expr v with
     | true -> subst_expr v x e
     | false -> (match xJO_red12 v s with       (* adding reduction so that we preserve semantics *)
                 | v' -> (E_case (E_taggingleft v', x, e, x', e'), s)
             (*  | _ -> assert false (*  *) *) )        (* No other possibilities *))
  | (E_case (E_taggingright v, x, e, x', e'), s) ->
    (match xis_value_of_expr v with
     | true -> subst_expr v x' e'
     | false -> (match xJO_red12 v s with       (* adding reduction so that we preserve semantics *)
                 | v' -> (E_case (E_taggingright v', x, e, x', e'), s)
             (*  | _ -> assert false (*  *) *) ))
  | (E_case (e, x, e'', x', e'''), s) ->
    (match xis_value_of_expr e with                      (* Technically makes no difference, but reorder these clauses, so that we first check and then reduce *)
     | false ->
       (match xJO_red12 e s with
        | e' -> E_case (e', x, e'', x', e''')
       (* | _ -> assert false (*  *) *) )                (* No such possibility *)
     | true -> assert false (*  *))                     (* There are no other possibilities *)
  | _ -> assert false (*  *)



forkdocomp1 -> evalcase

let rec xJO_red12 p1 p2 =
  match (p1, p2) with
  | (E_apply (E_apply (E_constant CONST_fork, E_live_expr LM_comp),
              E_live_expr LM_expr e), s) ->
    E_live_expr (LM_expr (E_taggingleft (E_taggingright (E_pair ((E_constant
      CONST_unit), (E_live_expr (LM_expr e)))))))
  | (E_apply (E_apply (E_constant CONST_fork, E_live_expr LM_expr e),
              E_live_expr LM_comp), s) ->
    E_live_expr (LM_expr (E_taggingright (E_pair ((E_live_expr (LM_expr e)),
      (E_constant CONST_unit)))))
  | (E_apply (E_apply (E_constant CONST_fork, E_live_expr LM_comp),
              E_live_expr LM_comp), s) ->
    E_live_expr (LM_expr (E_taggingleft (E_taggingleft (E_pair ((E_constant
      CONST_unit), (E_constant CONST_unit))))))
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
  | (E_case (e, x, e'', x', e'''), s) ->
    (match xJO_red12 e s with
     | e' ->
       (match xis_value_of_expr e with
        | false -> E_case (e', x, e'', x', e''')
        | _ -> assert false (*  *))
     | _ -> assert false (*  *))
  | _ -> assert false (*  *)



fix_move -> fix_app

let rec xJO_red12 p1 p2 =
  match (p1, p2) with
  | (E_fix e, s) ->
    (match xJO_red12 e s with
     | e' -> E_fix e'
     | _ -> assert false (*  *))
  | (E_apply (E_fix v, v'), s) ->
    (match xis_value_of_expr v' with
     | true ->
       (match xis_value_of_expr v with
        | true -> E_apply ((E_fix v), (E_apply (v, v')))
        | _ -> assert false (*  *))
     | _ -> assert false (*  *))
  | _ -> assert false (*  *)


*)
*)
