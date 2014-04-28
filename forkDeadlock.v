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

Lemma deadlock_rel_wbsm : forall (p q : expr), deadlock_left_rel p q -> 
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
 apply weakred_T.
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



 
 
 