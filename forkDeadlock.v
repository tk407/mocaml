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
 | deadlock_live : forall (d e : expr), totalDetTauStep d d -> deadlock_left_rel (( d) # ( e)) e
 | deadlock_dead : forall (d e : expr), totalDetTauStep d d -> is_value_of_expr e -> deadlock_left_rel (( d) #> (e)) e.

Lemma deadlock_rel_wbsm : isExprRelationStepWeakBisimilarity deadlock_left_rel.
Proof.
 unfold isExprRelationStepWeakBisimilarity.
 intros.
 inversion H.
 substs.
 split.
 intros.
 inversion H1.
 apply red_not_value in H7; simpl in H7; intuition.
 apply red_not_value in H8; simpl in H8; intuition.
 substs.
 inversion H0.
 substs.
 induction rl.
 intuition.
 apply tStep in H4.
 apply H6 in H4.
 substs.
 exists q.
 Hint Constructors deadlock_left_rel.
 intuition.
 apply weakred_T.
 apply star_refl.
 intuition.
 apply H2 in H4.
 contradiction.
 substs.
 exists e''.
 intuition.
 apply simpl_weakred with (s:=s0); assumption.
 substs.
 inversion H0; intuition.
 inversion H5.
 apply red_not_value in H6; contradiction.
 substs.
 exists q.
 intuition.
 apply weakred_T.
 apply star_refl.
 intros.
 exists (d # q').
 intuition.
 apply simpl_weakred with (s:=S_Seq SO_Second s).
 apply JO_red_forkmove2 with (s:=s).
 assumption.
 inversion H0; intuition.
 inversion H6.
 apply red_not_value in H7; contradiction.
 substs.
 split.
 intros.
 apply red_not_value in H2; simpl in H2; intuition.
 intros.
 apply red_not_value in H2; simpl in H2; intuition.
Qed.

Definition takeright : expr :=
    E_function (0) TE_unit 
      (E_case (E_ident (0)) 
           (1) (E_proj2  (E_ident (1))) 
           (2) (E_ret (E_proj2  (E_ident (2))))).

Lemma takeright_right : forall (v v' : expr), 
           is_value_of_expr v ->
           is_value_of_expr v' ->
           totalTauRed ( E_apply (takeright) (E_taggingright (( E_pair v v' )) ) ) (E_live_expr v').
Proof.
 intros.
 apply S_star with (y:=((E_case ((E_taggingright (E_pair v v'))) 
           (1) (E_proj2  (E_ident (1))) 
           (2) (E_ret (E_proj2  (E_ident (2))))))).
 apply JO_red_app_td.
 simpl.
 auto.
 apply S_star with (y:=(E_ret (E_proj2  ((E_pair v v'))))).
 apply JO_red_evalcaseinr_td.
 simpl; auto.
 apply S_star with (y:=E_ret v').
 simpl.
 apply JO_red_evalret_td.
 apply JO_red_proj2_td.
 trivial.
 trivial.
 apply star1.
 apply JO_red_ret_td.
 apply sstar1.
 simpl;auto.
Qed.

Lemma takeright_right_b : forall (v v' : expr), 
           is_value_of_expr v ->
           is_value_of_expr v' ->
           totalTauRed ( (E_live_expr (  (E_taggingright (( E_pair v v' )))) ) >>= (takeright)) (E_live_expr v').
Proof.
 intros.
 apply S_star  with (y:=(E_apply (takeright) (E_taggingright (( E_pair v v' )) ))).
 apply JO_red_dobind_td.
 apply sstar1.
 simpl; auto.
 apply takeright_right.
 assumption.
 assumption.
Qed.

Lemma takeright_left : forall (v v' : expr), 
           is_value_of_expr v ->
           is_value_of_expr v' ->
           totalTauRed ( E_apply (takeright) (E_taggingleft ( ( E_pair v v' )) ) ) v'.
Proof.
 intros.
 apply S_star with (y:=((E_case ((E_taggingleft (E_pair v v'))) 
           (1) (E_proj2  (E_ident (1))) 
           (2) (E_ret (E_proj2  (E_ident (2))))))).
 apply JO_red_app_td.
 simpl.
 auto.
 apply S_star with (y:=((E_proj2  ((E_pair v v'))))).
 apply JO_red_evalcaseinl_td.
 simpl; auto.
 apply star1.
 apply JO_red_proj2_td.
 trivial.
 trivial.
Qed.

Lemma takeright_left_b : forall (v v' : expr), 
           is_value_of_expr v ->
           is_value_of_expr v' ->
           totalTauRed (  (E_live_expr((E_taggingleft ( ( E_pair v v' )) ))) >>= (takeright)) v'.
Proof.
 intros.
 apply S_star  with (y:=(E_apply (takeright) ((E_taggingleft ( (E_pair v v')) )))).
 apply JO_red_dobind_td.
 apply sstar1.
 simpl; auto.
 apply takeright_left.
 assumption.
 assumption.
Qed.

Inductive deadlock_left_ext_rel : relation expr :=
 | deadlock_ext_live : forall (d e : expr), totalDetTauStep d d -> deadlock_left_ext_rel ((( d) # ( e)) >>= takeright) (E_ret e)
 | deadlock_ext_dead : forall (d e f : expr), totalDetTauStep d d -> is_value_of_expr e -> totalTauRed ((( d) #> (e))>>= takeright) f -> deadlock_left_ext_rel f (E_live_expr e).

Lemma deadlock_ext_rel_wbsm : isExprRelationStepWeakBisimilarity deadlock_left_ext_rel.
Proof.
 unfold isExprRelationStepWeakBisimilarity.
 intros.
 inversion H.
 substs.
 split.
 intros.
 inversion H1.
 apply red_not_value in H7; simpl in H7; intuition.
 substs.
 inversion H1.
 substs.
 inversion H6.
 apply red_not_value in H9; simpl in H9; intuition.
 apply red_not_value in H10; simpl in H10; intuition.
 substs.
 inversion H0.
 substs.
 induction rl.
 intuition.
 apply tStep in H4.
 apply H8 in H4.
 substs.
 exists (E_ret e).
 Hint Constructors deadlock_left_ext_rel.
 intuition.
 apply weakred_T.
 apply star_refl.
 intuition.
 apply H2 in H4.
 contradiction.
 substs.
 exists (E_ret e'').
 intuition.
 apply simpl_weakred with (s:=s0). apply JO_red_evalret. assumption.
 substs.
 inversion H0; intuition.
 inversion H5.
 apply red_not_value in H8; contradiction.
 substs.
 exists (E_live_expr e).
 intuition.
 apply simpl_weakred with (s:=sstar1).
 apply JO_red_ret.
 assumption.
 apply deadlock_ext_dead with (d:=d)(e:=e)(f:=(d #> e >>= takeright)); intuition.
 apply star_refl.
 intros.
 inversion H1.
 substs.
 exists (d #> e >>= takeright).
 intuition.
 apply weakred_T; apply star1; apply tStep with (s:=sstar1); apply JO_red_evalbind; apply JO_red_forkdeath2.
 assumption.
 apply deadlock_ext_dead with (d:=d)(e:=e)(f:=(d #> e >>= takeright)); intuition.
 apply star_refl.
 intros.
 substs.
 exists (d # e' >>= takeright).
 intuition.
 apply simpl_weakred with (s:=S_Seq SO_Second s).
 apply JO_red_evalbind.
 apply JO_red_forkmove2; intuition.
 inversion H0; intuition.
 substs.
 inversion H7.
 apply red_not_value in H5; contradiction.
 substs.
 specialize takeright_right_b with (v:=E_live_expr d)(v':=e).
 intros.
 simpl in H3.
 assert (L:=H1).
 apply H3 in H1; intuition.
 apply ttau_midpoint with (e':=p) in H1; intuition.
 apply tau_incl_totalTau in H5; apply taured_val_id in H5; simpl; auto; substs.
 apply red_not_value in H4; simpl in H4; intuition.
 exists (E_live_expr e).
 inversion H5.
 substs.
 apply red_not_value in H4; simpl in H4; intuition.
 substs.
 induction rl.
 inversion H1; substs; intuition.
 apply weakred_T; apply star_refl.
 apply tStep in H4; apply H10 in H4; substs.
 apply deadlock_ext_dead with (d:=d)(e:=e); intuition.
 apply star_S with (y:=p); intuition.
 inversion H1; intuition.
 apply H7 in H4; intuition.
 apply H7 in H4; intuition.
 apply red_not_value in H4; simpl in H4; intuition.
Qed.

Theorem deadlock_ext_rel_vewbsm : isExprRelationValueEqualWeakBisimilarity deadlock_left_ext_rel.
Proof.
 unfold isExprRelationValueEqualWeakBisimilarity.
 intuition.
 apply isExprRelationWeakBisimilarity_equiv_isExprRelationStepWeakBisimilarity.
 apply deadlock_ext_rel_wbsm.
 inversion H1; substs; simpl in H; simpl in H0; intuition.
 inversion H2; substs; simpl in H; simpl in H0; intuition.
 specialize takeright_right_b with (v:=E_live_expr d)(v':=e).
 intros.
 simpl in H7.
 assert (L:=H3).
 apply H7 in H3; intuition.
 apply ttau_midpoint with (e':=vp) in H3; intuition.
 apply tau_incl_totalTau in H9; apply taured_val_id in H9; simpl; auto; substs.
 apply tau_incl_totalTau in H9; apply taured_val_id in H9.
 assumption.
 assumption.
Qed.



Inductive deadlock_right_rel : relation expr :=
 | deadlock_right_live : forall (d e : expr), totalDetTauStep d d -> deadlock_right_rel (( e) # ( d)) e
 | deadlock_right_dead : forall (d e : expr), totalDetTauStep d d -> is_value_of_expr e -> deadlock_right_rel (( e) <# (d)) e.

Lemma deadlock_right_rel_wbsm : isExprRelationStepWeakBisimilarity deadlock_right_rel.
Proof.
 assert (eeq (deadlock_right_rel) (comp fork_comm_rel deadlock_left_rel)).
 unfold eeq.
 unfold Relations.incl.
 unfold comp.
 split.
 intros.
 inversion H.
 substs.
 exists (d # y); intuition.
 substs.
 exists (d #> y); intuition.
 intros.
 destruct H.
 inversion H0.
 substs.
 inversion H.
 substs.
 Hint Constructors deadlock_right_rel.
 intuition.
 substs.
 inversion H.
 substs; intuition.
 apply eeq_sym in H.
 apply isExprRelationStepWeakBisimilarity_eeq in H.
 assumption.
 apply isExprRelationStepWeakBisimilarity_comp.
 apply fork_comm_wbsm.
 apply deadlock_rel_wbsm.
Qed.

(*
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
*)
Inductive deadlock_bind_left_rel : relation expr :=
 | deadlock_bind : forall (d e : expr), totalDetTauStep d d -> deadlock_bind_left_rel (d >>= e) d.

Lemma deadlock_bind_rel_wbsm : isExprRelationStepWeakBisimilarity deadlock_bind_left_rel.
Proof.
 unfold isExprRelationStepWeakBisimilarity.
 intros.
 inversion H.
 substs.
 split.
 intros.
 inversion H1.
 substs.
 inversion H0.
 substs.
 intuition.
 induction rl.
 apply tStep in H7.
 apply H5 in H7.
 substs.
 exists e'.
 Hint Constructors deadlock_bind_left_rel.
 intuition.
 apply weakred_T; apply star_refl.
 apply H2 in H7.
 intuition.
 substs.
 inversion H0.
 substs.
 intuition.
 inversion H3.
 apply red_not_value in H4; simpl in H4; intuition.
 substs.
 inversion H0.
 substs.
 intuition.
 inversion H3.
 apply red_not_value in H4; simpl in H4; intuition.
 substs.
 intros.
 assert (q=q' /\ rl=RL_tau).
 inversion H0.
 substs.
 induction rl.
 intuition.

 apply tStep in H1.
 apply H5 in H1.
 assumption.
 apply H2 in H1;intuition.
 substs.
 exists (q' >>= e).
 intuition.
 substs.
 apply weakred_T; intuition.
 apply star_refl.
 substs.
 auto.
Qed.

(*
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
*)
 