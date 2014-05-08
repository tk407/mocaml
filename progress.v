Require Import Classical_Prop.
Load weakBisimulations.


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
 simpl; auto.
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
 intros.
 inversion H.
 intros.
 simpl; auto.
 intros; simpl; auto.
 intros; inversion H.
 intros.
 inversion H.
 simpl.
 substs; intuition.
 apply IHe1 in H5.
 assumption.
 apply IHe1 in H5.
 assumption.
 assumption.
 substs.
 apply IHe2 in H6.
 simpl; intuition.
 intros; simpl; auto.
 intros; simpl; auto.
 intros; simpl; auto.
 intros; simpl; auto.
 intros; simpl; auto.
 intros.
 inversion H.
 substs.
 simpl.
 apply IHe in H1.
 assumption.
 intros.
 inversion H.
 substs.
 simpl.
 apply IHe in H1.
 assumption.
 intros; simpl; auto.
Qed.


Lemma is_value_of_expr_dec : forall (e : expr), ((is_value_of_expr e) \/ (~(is_value_of_expr e))).
 Proof.
 intros.
 apply classic.
Qed.

Lemma ts_not_val : forall (e e' : expr), tauStep e e' -> (~(is_value_of_expr e)).
Proof.
 intros.
 inversion H.
 apply red_not_value in H0; assumption.
Qed.

Lemma tts_not_val : forall (e e' : expr), totalDetTauStep e e' -> (~(is_value_of_expr e)).
Proof.
 intros.
 apply tau_step_incl_totalTau_step in H. apply ts_not_val in H; assumption.
Qed.

(*

Lemma subst_type_preservation : forall (e v : expr) (x : value_name) (t t' : typexpr), Get (G_vn G_em x t) e t' -> Get G_em v t -> Get G_em (subst_expr v x e) t'.
Proof.
 Hint Constructors Get.
intros e v x.
 induction e.
 simpl.
 destruct (eq_value_name value_name5 x).
 substs.
 intros.
 inversion H.
 substs.
 inversion H3.
 substs.
 assumption.
 intuition.
 intros.
 inversion H.
 substs.
 inversion H3.
 intuition.
 substs.
 inversion H6.
 simpl.
 intros.
 inversion H.
 substs.
 auto.
 simpl.
 intros.
 inversion H.
 substs.
 apply IHe1 in H4.
 apply IHe2 in H6.
 apply Get_apply with (t1:=t1); intuition.
 auto.
 auto.
 intros.
 simpl.
 inversion H.
 substs.
 apply IHe1 in H4; intuition;
 apply IHe2 in H6; intuition;
 apply Get_bind with (t:=t0); intuition.
 simpl.
 intros.
 destruct (eq_value_name value_name5 x).
 substs.
 apply IHe in H.
 intuition.
 inversion H3.
 substs.
 Hint Constructors G_constant.
 Hint Constructors Get.
 
 auto. auto. jauto.
 auto.
 auto.
 auto.
 auto.
 intros.
 simpl.
 inversion H.
 substs.
 apply Get_apply with (t1:=t1).
 apply IHe1 in H4.
 assumption.
 assumption.
 apply IHe2 in H6.
 assumption.
 assumption.
 simpl.
 intros.
 inversion H.
 substs. 
 apply Get_bind with (t:=t0).
 apply IHe1 in H4; intuition.
 apply IHe2 in H6; intuition.
 simpl.
 destruct (eq_value_name value_name5 x).
 admit.
 intros.
 inversion H.
 substs.
 apply Get_lambda.
 inversion H6.
 substs.
 inversion H1.
 substs.
 simpl.
 destruct (eq_value_name value_name5 x).
 contradiction.
 apply Get_value_name.
 apply VTSin_vn1.
 substs.
 inversion H7.
 substs.
 simpl.
 destruct (eq_value_name x x);intuition.
 substs. 
 intuition.
 intuition.
 auto.
 specialize eq_value_name with (x:=value_name5)(y:=x).
 intros.
 intuition.
 substs.
 simpl.
 assert (eq_value_name x x).
 assert ((if eq_value_name x x then v else E_ident x) = v).
 unfold eq_value_name.
 intuition.
 auto with ott_coq_equality arith.
 simpl.
 simpl.
 intuition.
 simpl;
 intros.

Theorem type_preservation: forall (e e' : expr) (rl : redlabel) (s : select) (t : typexpr),
                     Get G_em e t -> JO_red e s rl e' -> Get G_em e' t.
Proof.
Hint Constructors JO_red.
Hint Constructors Get.
Hint Constructors G_constant.
Hint Constructors G.
intros.
induction H.
inversion H0.
apply red_not_value in H0; simpl in H0.
intuition.
inversion 
induction H0.
inversion H.
substs.
inversion H4.
substs.
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
Qed.
*)
