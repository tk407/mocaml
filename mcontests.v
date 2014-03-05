Require Import Arith.
Require Import Bool.
Require Import List.

Load mconbase2.

(*Check E_ident(0).*)
Check JO_red (E_ident(0)) S_First RL_tau (E_ident(1)).


Notation "A >>= F" := (E_bind A F) (at level 42, left associativity).
Notation "A [ C ] --> [ D ] B" := (JO_red A C D B) (at level 54, no associativity).


Example valuepair : is_value_of_expr (E_pair (E_constant(CONST_ret)) (E_constant(CONST_fork))).
Proof.
 simpl.
 auto.
Qed.

Ltac caseEq f :=
  generalize (refl_equal f); pattern f at -1; case f. 

Inductive JO_red_star : expr -> expr -> Prop :=
| JO_red_star_step: forall (e e' f : expr) (s : select) (rl : redlabel),
    e [ s ] --> [ rl ] e' ->
    JO_red_star e' f ->
    JO_red_star e f
| JO_red_star_refl: forall e,
    JO_red_star e e.

Notation "A -->* B" := (JO_red_star A B) (at level 54, no associativity).

(*
Example simplred : forall (x:value_name) (e v:expr),
     is_value_of_expr v ->
     E_apply  (E_function x e)  v -->  subst_expr  v   x   e.
Proof.
  intros.
  Check JO_red_app.
  apply JO_red_app.
  apply H.
Qed.

*)

Lemma mon_left_id : forall (x:value_name) (t : typexpr) (a e:expr) (s s' : select),
    is_value_of_expr a ->
    ((E_apply(E_constant (CONST_ret)) a) >>= (E_function x t e)) -->* (E_apply (E_function x t e) a).
Proof.
 intros.
 apply JO_red_star_step with (e' := (E_live_expr (LM_expr a) >>= E_function x t e))(s:=s)(rl:=RL_tau).
 apply JO_red_evalbind.
 apply JO_red_ret.
 apply H.
 apply JO_red_star_step with (e' := (E_apply (E_function x t e) a))(s:=s')(rl:=RL_tau).
 apply JO_red_dobind.
 apply H.
 apply JO_red_star_refl.
Qed.


Lemma mon_right_id : forall (a:expr) (s s' : select),
   is_value_of_expr a ->
   E_live_expr (LM_expr a) >>= E_constant CONST_ret -->* E_live_expr (LM_expr a).
Proof.
 intros.
 apply JO_red_star_step with (e' := (E_apply (E_constant CONST_ret) a))(s:= s)(rl:=RL_tau).
 apply JO_red_dobind.
 trivial.
 apply JO_red_star_step with (e' := (E_live_expr (LM_expr a)))(s:=s')(rl:=RL_tau).
 apply JO_red_ret.
 trivial.
 apply JO_red_star_refl.
Qed.

Lemma mon_assoc : forall (v v' v'' : value_name) (t t' : typexpr) (a e e' :expr)(s s' s'':select),  
    is_value_of_expr a ->
    v <> v'' ->
    v' <> v'' ->
    ((subst_expr a v'' e') = e') ->
    ((subst_expr a v'' e) = e) ->
    exists (b :expr), (E_live_expr (LM_expr a) >>= (E_function v t e) >>= (E_function v' t' e') -->* b) /\ (E_live_expr (LM_expr a) >>= (E_function v'' t (E_apply (E_function v t e) (E_ident v'') >>= (E_function v' t' e'))) -->* b).
Proof.
 intros.
 exists (E_apply (E_function v t e) a >>= E_function v' t' e' ).
 split.
 Show 1.
  apply JO_red_star_step with (e' := ((E_apply (E_function v t e) a) >>= E_function v' t' e'))(s:=s)(rl:=RL_tau).
  apply JO_red_evalbind with (e' := ((E_apply (E_function v t e) a))).
  apply JO_red_dobind.
  trivial.
  apply JO_red_star_refl.
 apply JO_red_star_step with (e' := (E_apply (E_function v'' t (E_apply (E_function v t e) (E_ident v'') >>= E_function v' t' e')) a))(s:=s')(rl:=RL_tau).
 apply JO_red_dobind.
 trivial.
 apply JO_red_star_step with  (e' := (subst_expr a v'' (E_apply (E_function v t e) (E_ident v'') >>= E_function v' t' e')))(s:=s'')(rl:=RL_tau).
 apply JO_red_app with (x:=v'') (v:=a) (e := (E_apply (E_function v t e) (E_ident v'') >>= E_function v' t' e')).
 trivial.
 auto.
 cut ((subst_expr a v''  (E_apply (E_function v t e) (E_ident v'') >>= E_function v' t' e') = (E_apply (E_function v t e) a >>= E_function v' t' e'))). 
 intros.
 rewrite H4.
 apply JO_red_star_refl.
 simpl.
 rewrite H2.
 rewrite H3.
 cut ((if eq_value_name v v'' then true else false) = false).
 intros.
 rewrite H4.
 cut ((if eq_value_name v'' v'' then a else E_ident v'') = a).
 intros.
 rewrite H5.
 cut ((if eq_value_name v' v'' then true else false) = false).
 intros.
 rewrite H6.
 trivial.
 Check eq_value_name v v''.
 destruct (eq_value_name v v'').
 contradiction.
 destruct (eq_value_name v' v'').
 contradiction.
 trivial.
 destruct (eq_value_name v'' v'').
 trivial.
 contradiction n.
 trivial.
 destruct (eq_value_name v v'').
 contradiction e0.
 trivial.
Qed.