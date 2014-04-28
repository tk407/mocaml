Require Import Classical_Prop.
Load weakBisimulations.

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


(* Proof that if a term reduces, it is not a value *)

Lemma red_not_value : forall (e : expr) (e' : expr)(s : select) (rl : redlabel), (JO_red e s rl e') -> (~(is_value_of_expr e)).
Proof.
 intro e.
 induction e.
 intros.
 inversion H.
 intros.
 inversion H.
 intros.
 inversion H.
 simpl.
 congruence.
 simpl.
 congruence.
 simpl.
 congruence.
 simpl.
 congruence.
 simpl.
 congruence.
 simpl.
 congruence.
 simpl.
 congruence.
 simpl; congruence.
 subst.
 assert (L:=H6).
 apply IHe2 in H6.
 intuition.
 simpl in H0.
 induction e1.
 auto.
 induction constant5.
 auto.
 auto.
 auto.
 auto.
 auto.
 auto.
 auto.
 auto.
 auto.
 auto.
 auto.
 auto.
 auto.
 auto.
 auto.
 auto.
 apply IHe1 in H5.
 intuition.
 induction e1.
 auto.
 induction constant5.
 auto.
 simpl in H5.
 auto.
 simpl in H5; auto.
 simpl in H5; auto.
 simpl in H5.
 auto.
 simpl in H5; auto.
 simpl in H5; auto.
 simpl in H5; auto.
 simpl in H5; auto.
 simpl in H5; auto.
 simpl in H5; auto.
 simpl in H5; auto.
 simpl in H5; auto.
 simpl in H5.
 auto.
 simpl in H5.
 auto.
 simpl in H6.
 apply H6.
 simpl.
 auto.
 simpl; auto.
 simpl; auto.
 simpl; auto.
 simpl; auto.
 intros.
 inversion H.
 intros.
 simpl; auto.
 intros.
 inversion H.
 intros; inversion H.
 simpl.
 apply IHe1 in H5.
 intuition.
 apply IHe2 in H6; intuition.
 simpl in H7.
 intuition.
 intros.
 inversion H.
 simpl.
 apply IHe in H1; intuition.
 intros.
 simpl; inversion H.
 apply IHe in H1; intuition.
 simpl; intuition.
Qed.

Lemma is_value_of_expr_dec : forall (e : expr), ((is_value_of_expr e) \/ (~(is_value_of_expr e))).
 Proof.
 intros.
 apply classic.
Qed.

(*
Theorem type_preservation: forall (e e' : expr) (rl : redlabel) (s : select) (t : typexpr),
                     Get G_em e t -> JO_red e s rl e' -> Get G_em e' t.
Proof.
Hint Constructors JO_red.
Hint Constructors Get.
Hint Constructors G_constant.
Hint Constructors G.
intros.
induction H0.
inversion H.
substs.
inversion H0.
apply red_not_value in H0; simpl in H0; intuition.
inversion H.
substs.
admit.
inversion H.
substs.
admit.
apply red_not_value in H0; simpl in H0; intuition.
inversion H0.
substs.
inversion H4.
inversion H0.
substs.
apply IHe1.
inversion H.
substs.
inversion H4.
intuition.
*)