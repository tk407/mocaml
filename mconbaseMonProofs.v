Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Classical_Prop.

Load weakBisimulations.

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
 simpl; congruence.
 simpl; congruence.
 simpl; congruence.
 simpl; congruence.
 simpl.
 congruence.
 apply IHe2 in H5.
 simpl.
 intuition.
 induction e1.
 auto.
 induction constant5.
 auto.
 contradiction.
 auto.
 auto.
 auto. auto. auto. auto.
 auto.
 auto.
 auto.
 auto.
 auto.
 auto.
 auto.
 auto.
 apply IHe1 in H6.
 intuition.
 induction e1.
 auto.
 induction constant5.
 auto.
 simpl in H6.
 auto.
 simpl in H6; auto.
 simpl in H6; auto.
 simpl in H7.
 auto.
 simpl in H7; auto.
 simpl in H7; auto.
 simpl in H7; auto.
 simpl in H7; auto.
 simpl in H7; auto.
 simpl in H7; auto.
 simpl in H7; auto.
 simpl in H7; auto.
 simpl.
 apply H6.
 simpl.
 auto.
 apply H6.
 simpl; auto.
 apply H6; simpl; auto.
 simpl in H7.
 auto.
 simpl in H7; auto.
 simpl in H7; auto.
 simpl in H7; auto.
 simpl in H6; auto.
 simpl in H7; auto.
 simpl in H7; auto.
 simpl in H7; auto.
 simpl in H7; auto.
 simpl; auto.
 simpl;
 congruence.
 simpl.
 intros; congruence.
 intros.
 simpl; congruence.
 intros.
 simpl; auto.
 intros.
 inversion H.
 intros; inversion H.
 simpl.
 auto.
 apply IHe in H1; auto.
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


Lemma empty_VTSin_false : forall  (v : value_name)  (ts : typscheme), ~ (VTSin v ts G_em).
Proof.
 intros.
 unfold not.
 intros.
 inversion H.
Qed.

Lemma is_value_of_expr_dec : forall (e : expr), ((is_value_of_expr e) \/ (~(is_value_of_expr e))).
 Proof.
 intros.
 apply classic.
Qed.

Lemma JO_red_ret_td : forall (v:expr) (s:select),
     is_value_of_expr v -> totalDetTauStep (E_apply (E_constant CONST_ret) v) (E_live_expr (LM_expr v)).
Proof. 
  intros.
  apply ttStep.
  split.
  apply tStep with (s:= S_First).
  apply JO_red_ret.
  trivial.
  split.
  intros.
  inversion H0.
  apply red_not_value in H6.
  contradiction.
  apply red_not_value in H7.
  simpl in H7.
  intuition.
  intros.
  inversion H0.
  inversion H1.
  reflexivity.
  apply red_not_value in H9; contradiction.
  apply red_not_value in H10; simpl in H10; intuition.
Qed.






Lemma JO_red_evalbind_td : forall (e e'':expr) (e':expr),
     totalDetTauStep e e' ->
     (forall (s : select), JO_red (E_bind e e'') s RL_tau (E_bind e' e'')) ->       (* This is technically not necessary, but the proof of it is rather complex, I'll do it later *)
     totalDetTauStep (E_bind e e'') (E_bind e' e'').
Proof.
 intros.
 apply ttStep.
 split.
 apply tStep with (s:=S_First).
 apply H0.
 split.
 inversion H.
 elim H1.
 intros.
 elim H5; intros.
 inversion H6.
 apply H7 in H14.
 trivial.
 inversion H4.
 rewrite <- H9 in H15.
 inversion H15.
 inversion H4.
 rewrite <- H10 in H14; inversion H14.
 intros.
 inversion H1.
 inversion H.
 elim H5; intros.
 inversion H8.
 apply red_not_value in H10.
 inversion H2.
 cut (tauStep e e'3).
 intros.
 elim H9.
 intros.
 apply H21 in H19.
 rewrite <- H19; reflexivity.
 apply tStep with (s:=s); trivial.
 rewrite <- H13 in H10; simpl in H10; intuition.
 subst.
 simpl in H10; intuition.
Qed.


Lemma JO_red_dobind_td : forall (v e:expr) (s:select),
     is_value_of_expr v ->
     totalDetTauStep (E_bind  (E_live_expr (LM_expr v))  e) (E_apply e v).
Proof. 
  intros.
  apply ttStep.
  split.
  apply tStep with (s:= S_First).
  apply JO_red_dobind.
  trivial.
  split.
  intros.
  inversion H0.
  apply red_not_value in H6.
  simpl in H6.
  intuition.
  apply red_not_value in H6.
  contradiction.
  intros.
  inversion H0.
  inversion H1.
  apply red_not_value in H9; simpl in H9; intuition.
  apply red_not_value in H9; contradiction.
  reflexivity.
Qed.


Lemma JO_red_app_td : forall (x:value_name) (t:typexpr) (e:expr) (v:expr),
     is_value_of_expr v -> 
     totalDetTauStep (E_apply  (E_function x t e)  v) (subst_expr  v   x   e ).
Proof.
 intros.
 apply ttStep.
 split.
 apply tStep with (s:=S_First).
 apply JO_red_app.
 trivial.
 split.
 intros.
 inversion H0.
 apply red_not_value in H6; contradiction.
 apply red_not_value in H7; simpl in H7; intuition.
 intros.
 inversion H0.
 inversion H1.
 reflexivity.
 apply red_not_value in H9; contradiction.
 apply red_not_value in H10; simpl in H10; intuition.
Qed.


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

Lemma mon_left_id_wbsm : forall (x:value_name) (t : typexpr) (a e:expr),
    is_value_of_expr a ->
    weakbisim ((E_apply(E_constant (CONST_ret)) a) >>= (E_function x t e)) (E_apply (E_function x t e) a).
Proof.
 intros.
 cut (totalTauRed ((E_apply(E_constant (CONST_ret)) a) >>= (E_function x t e)) (E_apply (E_function x t e) a)).
 intros.
 apply bisimsymm.
 apply ttau_weakbisim_incl.
 trivial.
 intros.
 apply S_star with (y:=((E_live_expr (LM_expr a) >>= E_function x t e))).
 apply JO_red_evalbind_td.
 apply JO_red_ret_td.
 apply S_First.
 trivial.
 intros.
 apply JO_red_evalbind.
 apply JO_red_ret.
 trivial.
 apply S_star with (y:=(E_apply (E_function x t e) a)).
 apply JO_red_dobind_td.
 apply S_First.
 trivial.
 apply star_refl.
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

Lemma mon_right_id_wbsm : forall (a:expr) (s s' : select),
   is_value_of_expr a ->
   weakbisim (E_live_expr (LM_expr a) >>= E_constant CONST_ret) (E_live_expr (LM_expr a)).
Proof.
  intros.
  cut (totalTauRed (E_live_expr (LM_expr a) >>= E_constant CONST_ret) (E_live_expr (LM_expr a))).
  intros.
  apply bisimsymm.
  apply ttau_weakbisim_incl.
  trivial.
  apply S_star with (y:=(E_apply (E_constant CONST_ret) a)).
  apply JO_red_dobind_td.
  trivial.
  trivial.
  apply S_star with (y:=(E_live_expr (LM_expr a))).
  apply JO_red_ret_td.
  trivial. trivial.
  apply star_refl.
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



Lemma mon_assoc_wbsm : forall (v v' v'' : value_name) (t t' : typexpr) (a e e' :expr)(s s' s'':select),  
    is_value_of_expr a ->
    v <> v'' ->
    v' <> v'' ->
    ((subst_expr a v'' e') = e') ->
    ((subst_expr a v'' e) = e) ->
    weakbisim (E_live_expr (LM_expr a) >>= (E_function v t e) >>= (E_function v' t' e')) (E_live_expr (LM_expr a) >>= (E_function v'' t (E_apply (E_function v t e) (E_ident v'') >>= (E_function v' t' e')))).
Proof.
 intros.
 cut (exists (b :expr), (weakbisim (E_live_expr (LM_expr a) >>= (E_function v t e) >>= (E_function v' t' e')) b) /\ (weakbisim (E_live_expr (LM_expr a) >>= (E_function v'' t (E_apply (E_function v t e) (E_ident v'') >>= (E_function v' t' e')))) b)).
 intros.
 elim H4.
 intros.
 elim H5; intros.
 apply bisimsymm in H7.
 apply bisimtrans with (e':=x).
 auto.
 intros.
 exists (E_apply (E_function v t e) a >>= E_function v' t' e' ).
 split.
 Show 1.
  cut (totalTauRed (E_live_expr (LM_expr a) >>= E_function v t e >>= E_function v' t' e') (E_apply (E_function v t e) a >>= E_function v' t' e')).
  intros.
  apply bisimsymm.
  apply ttau_weakbisim_incl.
  trivial.
  apply S_star with (y := ((E_apply (E_function v t e) a) >>= E_function v' t' e')).
  apply JO_red_evalbind_td.
  apply JO_red_dobind_td.
  trivial.
  trivial.
  intros.
  apply JO_red_evalbind.
  apply JO_red_dobind.
  trivial.
  apply star_refl.
 Show 1.
 cut (totalTauRed (E_live_expr (LM_expr a) >>=   E_function v'' t (E_apply (E_function v t e) (E_ident v'') >>= E_function v' t' e')) (E_apply (E_function v t e) a >>= E_function v' t' e')).
 intros.
 apply bisimsymm.
 apply ttau_weakbisim_incl.
 trivial.
 apply S_star with (y := (E_apply (E_function v'' t (E_apply (E_function v t e) (E_ident v'') >>= E_function v' t' e')) a)).
 apply JO_red_dobind_td.
 trivial.
 trivial.
 apply S_star with  (y := (subst_expr a v'' (E_apply (E_function v t e) (E_ident v'') >>= E_function v' t' e'))).
 apply JO_red_app_td.
 trivial.
 cut ((subst_expr a v''  (E_apply (E_function v t e) (E_ident v'') >>= E_function v' t' e') = (E_apply (E_function v t e) a >>= E_function v' t' e'))). 
 intros.
 rewrite H4.
 apply star_refl.
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

