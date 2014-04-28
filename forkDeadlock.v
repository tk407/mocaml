Load forkProofs.

Definition deadlock_proc : Prop :=
    (exists (d: expr), totalDetTauStep d d).

Lemma deadlock_proc_tdr : forall (d : expr), totalDetTauStep d d  -> ((forall (a b : expr), tauRed a b -> (a=d -> b=d) )).
Proof.
 intros.
 specialize star_ind with (X:=expr)(R:=tauStep)(P:=(fun k l => (k=d -> l=d))).
 intros.
 assert ((forall x0 : expr, x0 = d -> x0 = d)).
 intros; intuition.
 intuition.
 assert ((forall y x0 z : expr,
      tauStep x0 y -> star tauStep y z -> (y = d -> z = d) -> x0 = d -> z = d)).
 intros.
 substs.
 apply H6.
 inversion H.
 intuition.
 substs.
 apply H11 in H2.
 substs.
 reflexivity.
 assert (forall x0 x1 : expr, star tauStep x0 x1 -> x0 = d -> x1 = d).
 apply H4.
 assumption.
 substs.
 apply H5 with (x0:=d).
 assumption.
 reflexivity.
Qed.

Lemma deadlock_proc_labr : forall (d : expr), totalDetTauStep d d  -> ((forall (a b : expr), tauRed a b -> (a=d -> b=d) )) -> ( ((forall (a b : expr) (l:label), labRed l a b -> (a=d -> False) ))).
Proof.
 intros.
 inversion H1.
 intuition.
 substs.
 assert (e1=d).
 apply H0 with (a:=d).
 assumption.
 reflexivity.
 substs.
 inversion H.
 intuition. 
 substs.
 apply H2 in H3.
 assumption.
Qed.

Inductive deadlock_left_rel : relation expr :=
 | deadlock_live : forall (d e : expr), totalDetTauStep d d -> deadlock_left_rel ((LM_expr d) # (LM_expr e)) e
 | deadlock_dead : forall (d e : expr), totalDetTauStep d d -> is_value_of_expr e -> deadlock_left_rel ((LM_expr d) #> (e)) e.

Lemma deadlock_rel_wbsm_h : forall (p q : expr), deadlock_left_rel p q -> 
        ((forall (p' : expr) (r : redlabel), weakred r p p' -> (exists (q' : expr), weakred r q q' /\  deadlock_left_rel p' q' )) /\(forall (q' : expr) (r : redlabel), weakred r q q' -> (exists (p' : expr), weakred r p p' /\  deadlock_left_rel p' q' ))
 ).
Proof.
 intros.
 split.
 Check weakind.
 intros.
 inversion H.
 substs.
 inversion H0.
 substs.
 apply fork_tau_behave_ee in H2.
 intuition.
 destruct H3.
 destruct H2.
 intuition.
 substs.
 exists x0.
 intuition.
 Hint Constructors weakred. 
 auto.
 Hint Constructors deadlock_left_rel.
 apply deadlock_live.
 assert (L:=H1).
 apply deadlock_proc_tdr with (a:=d)(b:=x) in H1.
 substs.
 assumption.
 assumption.
 reflexivity.
 destruct H2.
 destruct H2.
 intuition.
 substs.
 exists x0.
 intuition.
 apply deadlock_dead.
 assert (L:=H1).
 apply deadlock_proc_tdr with (a:=d)(b:=x) in H1.
 substs.
 assumption.
 assumption.
 reflexivity.
 assumption.
 destruct H2.
 destruct H2.
 intuition.
 substs.
 exists x0.
 intuition.
 assert (totalDetTauStep x x).
 assert (L:=H1).
 apply deadlock_proc_tdr with (a:=d)(b:=x) in H1.
 substs.
 assumption.
 assumption.
 reflexivity.
 inversion H5.
 intuition.
 inversion H9.
 apply red_not_value in H10; simpl in H10; intuition.
 substs.
 apply fork_label_origin_ee in H2.
 intuition.
 destruct H3.
 intuition.
 destruct H2.
 intuition.
 substs.
 specialize deadlock_proc_labr with (d:=d).
 intros.
 specialize deadlock_proc_tdr with (d:=d).
 intuition.
 apply H5 in H3.
 intuition.
 reflexivity.
 destruct H4.
 intuition.
 substs.
 specialize deadlock_proc_labr with (d:=d).
 intros.
 specialize deadlock_proc_tdr with (d:=d).
 intuition.
 apply H6 in H3.
 intuition.
 reflexivity.
 specialize deadlock_proc_labr with (d:=d).
 intros.
 specialize deadlock_proc_tdr with (d:=d).
 intuition.
 apply H5 in H3.
 intuition.
 reflexivity.
 destruct H3.
 intuition.
 destruct H2.
 intuition.
 substs.
 exists x.
 intuition.
 apply deadlock_live.
 assert (L:=H1).
 apply deadlock_proc_tdr with (a:=d)(b:=x0) in H1.
 substs; intuition.
 assumption.
 reflexivity.
 destruct H4.
 intuition.
 substs.
 exists x.
 intuition.
 apply deadlock_dead.
 assert (L:=H1).
 apply deadlock_proc_tdr with (a:=d)(b:=x0) in H1.
 substs; intuition.
 assumption.
 reflexivity.
 assumption.
 destruct H4.
 intuition.
 substs.
 assert (L:=H1).
 apply deadlock_proc_tdr with (a:=d)(b:=x0) in H1.
 substs; intuition.
 inversion L.
 intuition.
 inversion H7; substs.
 apply red_not_value in H8; intuition.
 assumption.
 reflexivity.
 substs.
 inversion H0.
 substs.
 apply taured_val_id in H3.
 substs.
 exists q.
 intuition.
 apply weakred_T.
 apply star_refl.
 simpl; auto.
 substs.
 apply labred_not_val in H3.
 simpl in H3; intuition.
 intros.
 inversion H.
 substs.
 exists ((LM_expr d # LM_expr q')).
 intuition.
 inversion H0.
 substs.
 apply weakred_T.
 apply fork_tau_push_ee_2.
 assumption.
 substs.
 apply weakred_L.
 inversion H2.
 intuition.
 apply lab_r with (e1:=(LM_expr d # LM_expr e1))(e2:=(LM_expr d # LM_expr e2))(s:=S_Second).
 Hint Resolve fork_tau_push_ee_2.
 intuition.
 apply JO_red_forkmove2 with (s:=s).
 assumption.
 substs.
 exists (LM_expr d #> q).
 intuition.
 inversion H0.
 Hint Constructors weakred.
 Hint Immediate star_refl.
 apply weakred_T.
 auto.
 apply star_refl.
 substs.
 apply labred_not_val in H3; intuition.
 inversion H0.
 substs.
 apply taured_val_id in H3.
 substs.
 apply deadlock_dead.
 assumption.
 assumption.
 assumption.
 substs.
 apply labred_not_val in H3; intuition.
Qed.

Theorem deadlock_rel_wbsm : isExprRelationWeakBisimilarity deadlock_left_rel. 
Proof.
 apply weakbisim_weakred.
 apply deadlock_rel_wbsm_h.
Qed.

Theorem deadlock_left_wbsm :  forall (d e : expr), totalDetTauStep d d -> isExprWeaklyBisimilar ((LM_expr d) # (LM_expr e)) e.
Proof.
 intros.
 apply isexprweaklybisimilar.
 exists deadlock_left_rel.
 intuition.
 apply deadlock_rel_wbsm.
Qed.

(*
Theorem deadlock_right_wbsm :  forall (d e : expr), totalDetTauStep d d -> isExprWeaklyBisimilar ((LM_expr e) # (LM_expr d)) e.
Proof.
 intros.
 apply isexprweaklybisimilar.
 exists deadlock_left_rel.
 intuition.
 apply deadlock_rel_wbsm.
Qed.
*)

Inductive deadlock_bind_left_rel : relation expr :=
 | deadlock_bind : forall (d e : expr), totalDetTauStep d d -> deadlock_bind_left_rel ((E_live_expr (LM_expr d)) >>= e) d.

Lemma deadlock_bind_rel_wbsm_h : forall (p q : expr), deadlock_bind_left_rel p q -> 
        ((forall (p' : expr) (r : redlabel), weakred r p p' -> (exists (q' : expr), weakred r q q' /\  deadlock_bind_left_rel p' q' )) /\(forall (q' : expr) (r : redlabel), weakred r q q' -> (exists (p' : expr), weakred r p p' /\  deadlock_bind_left_rel p' q' ))
 ).
Proof.
 intros.
 inversion H.
 substs.
 split.
 intros.
 inversion H1.
 substs.
 apply bind_tau_behave_back_h in H2.
 destruct H2.
 destruct H2.
 intuition.
 simplify_eq H3; clear H3; intros; substs.
 destruct H2.
 intuition.
 substs.
 apply taured_val_id in H3; substs.
 exists q.
 intuition.
 apply weakred_T.
 apply star_refl.
 simpl; auto.
 destruct H2.
 intuition.
 destruct H5.
 intuition.
 substs.
 simplify_eq H3; clear H3; intros; substs.
 apply taured_val_id in H4. simplify_eq H4; clear H4; intros; substs.
 specialize deadlock_proc_tdr with (a:=x1)(b:=x2).
 intros.
 apply H3 with (a:=x1)(b:=x2) in H0.
 substs.
 exists x1.
 intuition.
 assumption.
 reflexivity.
 simpl; auto.
 simplify_eq H3; clear H3; intros; substs.
 apply taured_val_id in H4. simplify_eq H4; clear H4; intros; substs.
 specialize deadlock_proc_tdr with (a:=x1)(b:=x2).
 intros.
 assert (L:=H0).
 apply H3 with (a:=x1)(b:=x2) in H0.
 substs.
 inversion L.
 intuition.
 inversion H8.
 apply red_not_value in H9; intuition.
 assumption.
 reflexivity.
 simpl; auto.
 exists (E_live_expr (LM_expr q)) e.
 reflexivity.
 substs.
 apply bind_lab_behave_back_h in H2.
 intuition.
 destruct H3.
 intuition.
 apply labred_not_val in H3; simpl in H3; auto.
 intuition.
 destruct H2.
 intuition.
 destruct H4.
 intuition.
 apply taured_val_id in H3; substs.
 simplify_eq H3; clear H3; intuition; substs.
 assert (L:=H0).
 apply deadlock_proc_labr with (d:=x)(a:=x)(b:=x0)(l:=l) in H0.
 intuition.
 specialize deadlock_proc_tdr with (d:=x).
 intuition.
 assumption.
 reflexivity.
 simpl; auto.
 apply taured_val_id in H3; substs.
 simplify_eq H3; clear H3; intuition; substs.
 assert (L:=H0).
 apply deadlock_proc_tdr with (d:=x)(a:=x)(b:=x0) in H0.
 substs.
 inversion L.
 intuition.
 inversion H7.
 apply red_not_value in H8; intuition.
 assumption.
 reflexivity.
 simpl; auto.
 apply taured_val_id in H3; substs.
 simplify_eq H3; clear H3; intuition; substs.
 simpl; auto.
 intros.
 inversion H1.
 substs.
 assert (L:=H0).
 apply deadlock_proc_tdr with (d:=q)(a:=q)(b:=q') in H0.
 substs.
 exists (E_live_expr (LM_expr q) >>= e).
 intuition.
 apply weakred_T; apply star_refl.
 assumption.
 reflexivity.
 substs.
 apply deadlock_proc_labr with (d:=q)(a:=q)(b:=q')(l:=l) in H0.
 intuition.
 specialize deadlock_proc_tdr with (d:=q).
 intuition.
 assumption.
 reflexivity.
Qed.
 