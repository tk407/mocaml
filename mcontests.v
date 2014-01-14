Load mconbase.

(*Check E_ident(0).*)
Check JO_red (E_ident(0)) (E_ident(1)).


Theorem identisexpr : forall (n : nat), is_expr_of_expr (E_ident(n)) = True.
Proof.
 intros n.
 simpl.
 trivial.
Qed.

Extraction Language Ocaml.

Notation "A >>= F" := (E_bind A F) (at level 42, left associativity).

Example valuepair : is_value_of_expr (E_pair (E_constant(CONST_ret)) (E_constant(CONST_fork))).
Proof.
 simpl.
 auto.
Qed.

Ltac caseEq f :=
  generalize (refl_equal f); pattern f at -1; case f. 

Inductive JO_red_star : expr -> expr -> Prop :=
| JO_red_star_step: forall e e' f,
    JO_red e e' ->
    JO_red_star e' f ->
    JO_red_star e f
| JO_red_star_refl: forall e,
    JO_red_star e e.

Example simplred : forall (x:value_name) (e v:expr),
     is_value_of_expr v ->
     JO_red (E_apply  (E_function x e)  v)  (subst_expr  v   x   e ).
Proof.
  intros.
  Check JO_red_app.
  apply JO_red_app.
  apply H.
Qed.

Lemma mon_left_id : forall (x:value_name) (a e:expr),
    is_value_of_expr a ->
    JO_red_star ((E_apply(E_constant (CONST_ret)) a) >>= (E_function x e)) (E_apply (E_function x e) a).
Proof.
 intros.
 apply JO_red_star_step with (e' := (E_bind (E_live_expr a) (E_function x e))).
 apply JO_red_evalbind.
 apply JO_red_ret.
 apply H.
 apply JO_red_star_step with (e' := (E_apply (E_function x e) a)).
 apply JO_red_dobind.
 apply H.
 apply JO_red_star_refl.
Qed.

(*
Lemma mon_right_id : forall (a:expr),
   is_value_of_expr a ->
   JO_red_star (E_bind (a)  (E_constant (CONST_ret))) (a).
*)