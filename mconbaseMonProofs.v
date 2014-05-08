Require Import Arith.
Require Import Bool.
Require Import List.

Load redTotalDetProp.


Lemma mon_left_id : forall (x:value_name) (t : typexpr) (a e:expr) (s s' : select),
    is_value_of_expr a ->
    ((E_ret a) >>= (E_function x t e)) -->* (E_apply (E_function x t e) a).
Proof.
 intros.
 apply JO_red_star_step with (e' := (E_live_expr ( a) >>= E_function x t e))(s:=s)(rl:=RL_tau).
 apply JO_red_evalbind.
 apply JO_red_ret.
 apply H.
 apply JO_red_star_step with (e' := (E_apply (E_function x t e) a))(s:=s')(rl:=RL_tau).
 apply JO_red_dobind.
 apply H.
 apply JO_red_star_refl.
Qed.


Inductive mon_left_id_rel : relation expr :=
| mon_left_id_bound : forall (e e' : expr), is_value_of_expr e' -> mon_left_id_rel ((E_ret e) >>= e') (E_apply e' e)
| mon_left_id_inbound : forall (e e' : expr), is_value_of_expr e' -> mon_left_id_rel ((E_live_expr e) >>= e') (E_apply e' e)
| mon_left_id_unbound : forall (e : expr), mon_left_id_rel (e) (e).


Theorem mon_left_id_wbsm : isExprRelationStepWeakBisimilarity mon_left_id_rel.
Proof.
 unfold isExprRelationStepWeakBisimilarity.
 intuition.
 inversion H.
 substs.
 inversion H0.
 substs.
 inversion H7.
 substs.
 exists (E_apply e' e).
 Hint Constructors mon_left_id_rel.
 intuition.
 apply weakred_T.
 apply star_refl.
 substs.
 exists (E_apply e' e'1).
 intuition.
 induction rl.
 apply weakred_T.
 apply star1.
 apply tStep with (s:=s).
 apply JO_red_context_app2.
 assumption.
 assumption.
 apply weakred_L.
 apply lab_r with (e1:=(E_apply e' e))(e2:=(E_apply e' e'1))(s:=s).
 splits.
 apply star_refl.
 apply JO_red_context_app2; auto.
 apply star_refl.
 substs.
 inversion H0.
 apply red_not_value in H7; simpl in H7; intuition.
 substs.
 exists ((E_apply e' e'0)).
 intuition.
 induction rl.
 apply weakred_T.
 apply star1.
 apply tStep with (s:=s).
 apply JO_red_context_app2.
 assumption.
 assumption.
 apply weakred_L.
 apply lab_r with (e1:=(E_apply e' e))(e2:=(E_apply e' e'0))(s:=s).
 intuition.
 apply star_refl.
 apply JO_red_context_app2.
 assumption.
 assumption.
 apply star_refl.
 substs.
 exists ((E_apply e' e) ).
 Hint Constructors weakred.
 intuition.
 apply weakred_T.
 apply star_refl.
 substs.
 exists p'.
 intuition.
 induction rl.
 apply weakred_T.
 apply star1.
 apply simpTau in H0.
 assumption.
 apply weakred_L.
 apply lab_r with (e1:=q)(e2:=p')(s:=s).
 intuition.
 apply star_refl.
 apply star_refl.
 inversion H.
 substs.
 inversion H0.
 substs.
 exists (subst_expr e x e0).
 intuition.
 apply weakred_T.
 apply S_star with (y:=((E_live_expr e)) >>= E_function x t e0).
 apply tStep with (s:=S_First).
 apply JO_red_evalbind.
 apply JO_red_ret.
 assumption.
 apply S_star with (y:=(E_apply (E_function x t e0) e)).
 apply tStep with (s:=S_First).
 apply JO_red_dobind.
 assumption.
 apply star1.
 apply tStep with (s:=S_First).
 apply JO_red_app.
 assumption.
 substs.
 exists (E_ret e'' >>= e').
 intuition.
 induction rl.
 apply weakred_T.
 apply star1.
 apply tStep with (s:=s).
 apply JO_red_evalbind.
 apply JO_red_evalret.
 assumption.
 apply weakred_L.
 apply lab_r with (e1:=(E_ret e >>= e') )(e2:=(E_ret e'' >>= e'))(s:=s); intuition.
 apply star_refl.
 apply JO_red_evalbind.
 apply JO_red_evalret.
 assumption.
 apply star_refl.
 substs.
 apply red_not_value in H7; contradiction.
 substs.
 inversion H0.
 substs.
 exists (subst_expr e x e0).
 intuition.
 apply weakred_T.
 apply S_star with (y:=(E_apply (E_function x t e0) e)).
 apply tStep with (s:=S_First).
 apply JO_red_dobind.
 assumption.
 apply star1.
 apply tStep with (s:=S_First).
 apply JO_red_app.
 assumption.
 substs.
 exists ((E_live_expr e'' >>= e')); intuition.
 induction rl.
 apply weakred_T.
 apply star1.
 apply tStep with (s:=s).
 apply JO_red_movebind.
 assumption.
 apply weakred_L.
 apply lab_r with (e1:=(E_live_expr e >>= e'))(e2:=(E_live_expr e'' >>= e'))(s:=s).
 splits.
 apply star_refl.
 apply JO_red_movebind.
 assumption.
 apply star_refl.
 substs.
 apply red_not_value in H7; contradiction.
 substs.
 exists q'.
 intuition.
 induction rl.
 apply weakred_T.
 apply star1.
 apply tStep in H0; assumption.
 apply weakred_L.
 apply lab_r with (e1:=q)(e2:=q')(s:=s).
 splits.
 apply star_refl.
 assumption.
 apply star_refl.
Qed.
 
Inductive mon_right_id_rel : relation expr :=
| mon_right_id_bound : forall (a : expr) (x : value_name) (t : typexpr), is_value_of_expr a -> mon_right_id_rel (E_live_expr (a) >>= (E_function x t (E_ret (E_ident x))))  (E_live_expr ( a))
| mon_right_id_inbound : forall (a : expr) (x : value_name) (t : typexpr), is_value_of_expr a -> mon_right_id_rel (E_apply (E_function x t (E_ret (E_ident x))) ( (a)))  (E_live_expr ( a))
| mon_right_id_unbound : forall (a : expr), is_value_of_expr a -> mon_right_id_rel ( ( (E_ret (a))) )  (E_live_expr ( a))
| mon_right_id_ret : forall (a : expr), mon_right_id_rel (E_live_expr ( a))  (E_live_expr ( a)).


Theorem mon_right_id_wbsm : isExprRelationStepWeakBisimilarity mon_right_id_rel.
Proof.
 unfold isExprRelationStepWeakBisimilarity.
 intros.
 inversion H.
 substs.
 splits.
 intros.
 exists (E_live_expr a).
 inversion H1.
 apply red_not_value in H7; simpl in H7; intuition.
 apply red_not_value in H7; simpl in H7; intuition.
 substs.
 Hint Constructors mon_right_id_rel.
 intuition.
 apply weakred_T.
 apply star_refl.
 intros.
 apply red_not_value in H1; simpl in H1; intuition.
 substs.
 splits.
 intros.
 exists (E_live_expr a).
 inversion H1.
 substs.
 simpl.
 destruct (eq_value_name x x).
 intuition.
 apply weakred_T.
 apply star_refl.
 intuition.
 substs.
 apply red_not_value in H8; simpl in H8; intuition.
 substs.
 apply red_not_value in H7; simpl in H7; intuition.
 intros.
 apply red_not_value in H1; simpl in H1; intuition.
 substs.
 splits.
 intros.
 exists (E_live_expr a).
 inversion H1.
 substs.
 splits.
 apply weakred_T.
 apply star_refl.
 auto.
 substs.
 apply red_not_value in H3; simpl in H3; intuition.
 intros.
 apply red_not_value in H1; simpl in H1; intuition.
 substs.
 splits.
 intros.
 apply red_not_value in H0; simpl in H0; intuition.
 intros.
 apply red_not_value in H0; simpl in H0; intuition.
Qed.

Definition exprClosedOnVariable : expr -> value_name -> Prop := fun e v => 
     ( forall (e' : expr), (subst_expr e' v e) = e ).

Inductive mon_assoc_rel : relation expr :=
| mon_assoc_start : forall (e e' e'' : expr) (v v' v'' : value_name) (t t' : typexpr), v <> v'' -> v' <> v'' -> exprClosedOnVariable e' v'' -> exprClosedOnVariable e'' v'' ->
    mon_assoc_rel (e >>= (E_function v t e') >>= (E_function v' t' e'')) (e >>= (E_function v'' t (E_apply (E_function v t e') (E_ident v'') >>= (E_function v' t' e''))))
| mon_assoc_s1 : forall (e e' e'' : expr) (v v' v'' : value_name) (t t' : typexpr), v <> v'' -> v' <> v'' -> is_value_of_expr e ->  exprClosedOnVariable e' v'' -> exprClosedOnVariable e'' v'' ->
    mon_assoc_rel ( (E_apply (E_function v t e') e ) >>= (E_function v' t' e'')) (E_apply (E_function v'' t (E_apply (E_function v t e') (E_ident v'') >>= (E_function v' t' e''))) e)
| mon_assoc_s2 : forall (e e' e'' : expr) (v v' v'' : value_name) (t t' : typexpr), v <> v'' -> v' <> v'' -> is_value_of_expr e -> exprClosedOnVariable e' v'' -> exprClosedOnVariable e'' v'' ->
    mon_assoc_rel ( ( ( (subst_expr e v e'))  ) >>= (E_function v' t' e''))    ( ( ((E_apply (E_function v t e') e) >>= (E_function v' t' e''))) )
| mon_assoc_s3 : forall (e e' e'' : expr) (v v' : value_name) (t t' : typexpr), is_value_of_expr e -> 
    mon_assoc_rel ( ( ( (subst_expr e v e'))  ) >>= (E_function v' t' e''))    ( ( ((subst_expr e v e') >>= (E_function v' t' e''))) )
| mon_assoc_fin : forall (e : expr) , 
    mon_assoc_rel e e.

Hint Constructors mon_assoc_rel.

Theorem mon_assoc_wbsm: isExprRelationStepWeakBisimilarity mon_assoc_rel.
Proof.
 unfold isExprRelationStepWeakBisimilarity.
 intros.
 inversion H.
 substs.
 splits.
 intros.
 inversion H4.
 substs.
 inversion H10.
 substs.
 Hint Unfold exprClosedOnVariable.
 exists ((e'1 >>=
       E_function v'' t
         (E_apply (E_function v t e') (E_ident v'') >>= E_function v' t' e''))).
 intuition.
 apply simpl_weakred with (s:=s).
 apply JO_red_evalbind.
 assumption.
 substs.
 exists ((E_live_expr e'1 >>=
       E_function v'' t
         (E_apply (E_function v t e') (E_ident v'') >>= E_function v' t' e''))).
 intuition.
 apply simpl_weakred with (s:=s).
 apply JO_red_movebind.
 assumption.
 substs. 
 exists ((E_apply (E_function v'' t (E_apply (E_function v t e') (E_ident v'') >>= (E_function v' t' e''))) v0)).
 intuition.
 apply simpl_weakred with (s:=s).
 apply JO_red_dobind.
 assumption.
 intros.
 inversion H4.
 substs.
 exists (e'0 >>= E_function v t e' >>= E_function v' t' e'').
 intuition.
 apply simpl_weakred with (s:=s).
 apply JO_red_evalbind.
 apply JO_red_evalbind.
 assumption.
 substs.
 exists (E_live_expr e'0 >>= E_function v t e' >>= E_function v' t' e'').
 intuition.
 apply simpl_weakred with (s:=s).
 apply JO_red_evalbind.
 apply JO_red_movebind.
 assumption.
 substs.
 exists ( (E_apply (E_function v t e') v0 ) >>= (E_function v' t' e'')).
 intuition.
 apply simpl_weakred with (s:=s).
 apply JO_red_evalbind.
 apply JO_red_dobind.
 assumption.
 intros.
 
 splits.
 intros.
 substs.
 inversion H7.
 substs.
 inversion H11.
 substs.
 exists ( ( ((E_apply (E_function v t e') e) >>= (E_function v' t' e''))) ).
 intuition.
 apply simpl_weakred with (s:=s).
 assert ((subst_expr e v'' (E_apply (E_function v t e') (E_ident v'') >>= E_function v' t' e'')) = E_apply (E_function v t e') e >>= E_function v' t' e'').
 simpl.
 assert (subst_expr e v'' e' = e'); intuition.
  assert (subst_expr e v'' e'' = e''); intuition.
 rewrite -> H5; rewrite -> H6.
 destruct (eq_value_name v v''); destruct (eq_value_name v'' v''); destruct (eq_value_name v' v''); intuition.
 rewrite <- H5.
 apply JO_red_app.
 assumption.
 intuition.
 apply mon_assoc_s2 with (v'':=v''); intuition.
 substs.
 apply red_not_value in H13; simpl in H13; intuition.
 apply red_not_value in H12; simpl in H12; intuition.
 intros.
 substs.
 inversion H7.
 substs.
 simpl in H7.
 simpl.
 assert (subst_expr e v'' e' = e'); intuition.
 assert (subst_expr e v'' e'' = e''); intuition.
 destruct (eq_value_name v v''); destruct (eq_value_name v'' v''); destruct (eq_value_name v' v''); intuition.
 rewrite -> H5 in H7; rewrite -> H6 in H7.
 rewrite -> H5; rewrite -> H6.
 exists (E_apply (E_function v t e') e >>= E_function v' t' e'').
 intuition.
 apply weakred_T.
 apply star_refl.
 substs.
 apply red_not_value in H12; simpl in H12; intuition.
 substs.
 apply red_not_value in H11; simpl in H11; intuition.
 substs.
 splits.
 intros.
 inversion H5.
 substs.
 exists (e'0 >>= E_function v' t' e'').
 intuition.
 apply weakred_tau_prefix with (e':=(subst_expr e v e' >>= E_function v' t' e'')).
 apply simpl_weakred with (s:=S_First).
 apply JO_red_evalbind.
 apply JO_red_app.
 assumption.
 apply simpl_weakred with (s:=s).
 apply JO_red_evalbind.
 assumption.
 substs.
 exists (E_live_expr e'0 >>= E_function v' t' e'').
 intuition.
 apply weakred_tau_prefix with (e':=(subst_expr e v e' >>= E_function v' t' e'')).
 apply simpl_weakred with (s:=S_First).
 apply JO_red_evalbind.
 apply JO_red_app.
 assumption.
 rewrite <- H6.
 apply simpl_weakred with (s:=s).
 apply JO_red_movebind.
 assumption.
 substs.
 exists (E_apply (E_function v' t' e'') v0).
 intuition.
 apply weakred_tau_prefix with (e':=(subst_expr e v e' >>= E_function v' t' e'')).
 apply simpl_weakred with (s:=S_First).
 apply JO_red_evalbind.
 apply JO_red_app.
 assumption.
 rewrite <- H6.
 apply simpl_weakred with (s:=S_First).
 apply JO_red_dobind.
 assumption.
 intros.
 inversion H5.
 substs.
 inversion H11.
 substs.
 exists (subst_expr e v e' >>= E_function v' t' e'').
 intuition.
 apply weakred_T.
 apply star_refl.
 apply red_not_value in H13; simpl in H13; intuition.
 apply red_not_value in H12; simpl in H12; intuition.
 substs.
 split.
 intros.
 exists p'.
 split; [eauto | auto ].
 intros.
 exists q'.
 split; [eauto | auto ].
 substs.
 split.
 intros.
 exists p'.
 split; [eauto | auto ].
 intros.
 exists q'.
 split; [eauto | auto ].
Qed.
