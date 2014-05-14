Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Classical_Prop.


Load redTotalDetProp.







Definition swapbodyl : expr :=
            E_ret (  
             E_taggingright (
              E_pair (E_proj2  (E_ident (1))) 
                     (E_proj1  (E_ident (1)))
                            )
                   ).

Definition swapbodyr : expr :=
            E_ret (  
             E_taggingleft (
              E_pair (E_proj2  (E_ident (2))) 
                     (E_proj1  (E_ident (2)))
                           )
                   ).

Definition swapbody : expr := E_case (E_ident (0)) 
           (1) (swapbodyl) 
           (2) (swapbodyr).

Definition swapf : expr :=
    E_function (0) TE_unit swapbody.








Lemma swapf_right : forall (v v' : expr), 
           is_value_of_expr v ->
           is_value_of_expr v' ->
           totalTauRed ( E_apply (swapf) (E_taggingright (( E_pair v v' )) ) ) (E_live_expr((E_taggingleft( ( ( E_pair v' v )) )))).
Proof.
 intros.
 apply S_star with (y:=(subst_expr (E_taggingright ( ( E_pair v v' ))) 0 swapbody )).
 apply JO_red_app_td.
 simpl.
 auto.
 simpl.
 apply S_star with (y:=(subst_expr   ( ( E_pair v v' ))   2   swapbodyr )).
 apply JO_red_evalcaseinr_td.
 simpl; auto.
 apply S_star with (y:=E_ret 
                                    ( E_taggingleft 
                                     (
                                        (E_pair 
                                          (   
                                                    (v') 
                                          ) 
                                          (E_proj1  (E_pair v v')) 
                                        )
                                     ))).
 simpl.
 apply JO_red_evalret_td.
 apply JO_red_evalinl_td.
 simpl; intuition.
 apply JO_red_pair_1_td.
 simpl; auto.
 apply JO_red_proj2_td.
 trivial.
 trivial.
 apply S_star with (y:=E_ret  
                                    ( E_taggingleft 
                                     ( 
                                        (E_pair (v') (v)  
                                        )
                                     ))).
 apply JO_red_evalret_td.
 apply JO_red_evalinl_td.
 simpl; auto.
 intuition.
 apply JO_red_pair_2_td.
 assumption.
 apply JO_red_proj1_td.
 trivial.
 trivial.
 apply star1.
 apply JO_red_ret_td.
 apply sstar1.
 simpl;auto.
Qed.

Lemma swapf_right_b : forall (v v' : expr), 
           is_value_of_expr v ->
           is_value_of_expr v' ->
           totalTauRed ( (E_live_expr (  (E_taggingright (( E_pair v v' )))) ) >>= swapf) (E_live_expr((E_taggingleft( ( ( E_pair v' v )) )))).
Proof.
 intros.
 apply S_star  with (y:=(E_apply (swapf) (E_taggingright (( E_pair v v' )) ))).
 apply JO_red_dobind_td.
 apply sstar1.
 simpl; auto.
 apply swapf_right.
 assumption.
 assumption.
Qed.

Lemma swapf_left : forall (v v' : expr), 
           is_value_of_expr v ->
           is_value_of_expr v' ->
           totalTauRed ( E_apply (swapf) (E_taggingleft ( ( E_pair v v' )) ) ) (E_live_expr(( (E_taggingright ( E_pair v' v )) ))).
Proof.
 intros.
 apply S_star with (y:=(subst_expr (E_taggingleft ( ( E_pair v v' ))) 0 swapbody )).
 apply JO_red_app_td.
 simpl.
 auto.
 simpl.
 apply S_star with (y:=(subst_expr   ( ( E_pair v v' ))   1   swapbodyl )).
 apply JO_red_evalcaseinl_td.
 simpl; auto.
 apply S_star with (y:=(E_ret   
                                   (  
                                     ( E_taggingright
                                        (E_pair v' (E_proj1 (E_pair v v'))  
                                        )
                                     )
                                   ))).
 simpl.
 Hint Resolve JO_red_evalret_td.
 Hint Resolve JO_red_evalinr_td.
 Hint Resolve JO_red_pair_1_td.
 Hint Resolve JO_red_pair_2_td.
 Hint Resolve JO_red_proj2_td.
 intuition.
 apply JO_red_evalret_td. 
 apply JO_red_evalinr_td; intuition; simpl in H1; intuition.
 apply S_star with (y:=(E_ret
       (
          (E_taggingright
             (E_pair v' v))))).
 Hint Resolve JO_red_pair_2_td.
 Hint Resolve JO_red_proj1_td.
 apply JO_red_evalret_td; intuition.
 apply JO_red_evalinr_td; intuition; simpl in H1; intuition.
 apply star1. 
 apply JO_red_ret_td.
 apply sstar1.
 simpl;auto.
Qed.

Lemma swapf_left_b : forall (v v' : expr), 
           is_value_of_expr v ->
           is_value_of_expr v' ->
           totalTauRed (  (E_live_expr((E_taggingleft ( ( E_pair v v' )) ))) >>= (swapf)) (E_live_expr(( (E_taggingright ( E_pair v' v )) ))).
Proof.
 intros.
 apply S_star  with (y:=(E_apply (swapf) ((E_taggingleft ( (E_pair v v')) )))).
 apply JO_red_dobind_td.
 apply sstar1.
 simpl; auto.
 apply swapf_left.
 assumption.
 assumption.
Qed.


Inductive fork_comm_rel :  relation expr := 
 | forkee_start : forall (e e' : expr), fork_comm_rel (e # e') (e' # e)
 | forkee_endl : forall (e e' : expr), is_value_of_expr e -> fork_comm_rel (e <# e') (e' #> e)
 | forkee_endr : forall (e e' : expr), is_value_of_expr e' -> fork_comm_rel (e #> e') (e' <# e).

Hint Constructors fork_comm_rel.

Theorem fork_comm_wbsm: isExprRelationStepWeakBisimilarity fork_comm_rel.
Proof.
 unfold isExprRelationStepWeakBisimilarity.
 intros.
 inversion H.
 substs.
 split.
 intros.
 inversion H0.
 apply red_not_value in H6; simpl in H6; intuition.
 apply red_not_value in H7; simpl in H7; intuition.
 substs.
 exists (e' # e'').
 intuition.
 apply simpl_weakred with (s:=S_Seq SO_Second s0).
 apply JO_red_forkmove2 with (s:=s0).
 assumption.
 assumption.
 substs.
 exists (e'' # e).
 intuition.
 apply simpl_weakred with (s:=S_Seq SO_First s0).
 apply JO_red_forkmove1 with (s:=s0).
 assumption.
 assumption.
 substs.
 exists (e' #> e).
 intuition.
 apply simpl_weakred with (s:=sstar1).
 apply JO_red_forkdeath2.
 assumption.
 substs.
 exists (e' <# e).
 intuition.
 apply simpl_weakred with (s:=sstar1).
 apply JO_red_forkdeath1.
 assumption.
 intros.
 inversion H0.
 apply red_not_value in H6; simpl in H6; intuition.
 apply red_not_value in H7; simpl in H7; intuition.
 substs.
 exists (e # e'').
 intuition.
 apply simpl_weakred with (s:=S_Seq SO_Second s0).
 apply JO_red_forkmove2 with (s:=s0).
 assumption.
 assumption.
 substs.
 exists (e'' # e').
 intuition.
 apply simpl_weakred with (s:=S_Seq SO_First s0).
 apply JO_red_forkmove1 with (s:=s0).
 assumption.
 assumption.
 substs.
 exists (e #> e').
 intuition.
 apply simpl_weakred with (s:=sstar1).
 apply JO_red_forkdeath2.
 assumption.
 substs.
 exists (e <# e').
 intuition.
 apply simpl_weakred with (s:=sstar1).
 apply JO_red_forkdeath1.
 assumption.
 substs.
 split.
 intros.
 apply red_not_value in H1; simpl in H1; intuition.
 intros.
 apply red_not_value in H1; simpl in H1; intuition.
 substs.
 split.
 intros.
 apply red_not_value in H1; simpl in H1; intuition.
 intros.
 apply red_not_value in H1; simpl in H1; intuition.
Qed.

Inductive fork_comm_swapped_rel :  relation expr := 
 | forkee_s_start : forall (e e' : expr), fork_comm_swapped_rel (e # e') (( (e' # e))>>= swapf)
 | forkee_s_endl : forall (e e' f : expr), is_value_of_expr e -> totalTauRed (((e' #> e))>>= swapf) f -> fork_comm_swapped_rel (e <# e') f
 | forkee_s_endr : forall (e e' f : expr), is_value_of_expr e' -> totalTauRed (( (e' <# e))>>= swapf) f -> fork_comm_swapped_rel (e #> e') f.

Hint Constructors fork_comm_swapped_rel.

Theorem fork_comm_swapped_wbsm: isExprRelationStepWeakBisimilarity fork_comm_swapped_rel.
Proof.
 unfold isExprRelationStepWeakBisimilarity.
 intros.
 inversion H.
 substs.
 split.
 intros.
 inversion H0.
 apply red_not_value in H6; simpl in H6; intuition.
 apply red_not_value in H7; simpl in H7; intuition.
 substs.
 exists ( (e' # e'') >>= swapf).
 intuition.
 apply simpl_weakred with (s:=S_Seq SO_Second s0).
 apply JO_red_evalbind.
 apply JO_red_forkmove2 with (s:=s0).
 assumption.
 assumption.
 substs.
 exists ( (e'' # e) >>= swapf).
 intuition.
 apply simpl_weakred with (s:=S_Seq SO_First s0).
 apply JO_red_evalbind.
 apply JO_red_forkmove1 with (s:=s0).
 assumption.
 assumption.
 substs.
 exists ( (e' #> e) >>= swapf).
 intuition.
 apply simpl_weakred with (s:=sstar1).
 apply JO_red_evalbind.
 apply JO_red_forkdeath2.
 assumption.
 apply forkee_s_endl.
 assumption.
 apply star_refl.
 substs.
 exists ( (e' <# e) >>= swapf).
 intuition.
 apply simpl_weakred with (s:=sstar1).
 apply JO_red_evalbind.
 apply JO_red_forkdeath1.
 assumption.
 apply forkee_s_endr.
 assumption.
 apply star_refl.
 intros.
 inversion H0.
 substs.
 inversion H6.
 apply red_not_value in H7; simpl in H7; intuition.
 apply red_not_value in H8; simpl in H8; intuition.
 substs.
 exists (e # e'').
 intuition.
 apply simpl_weakred with (s:=S_Seq SO_Second s0).
 apply JO_red_forkmove2 with (s:=s0).
 assumption.
 assumption.
 substs.
 exists (e'' # e').
 intuition.
 apply simpl_weakred with (s:=S_Seq SO_First s0).
 apply JO_red_forkmove1 with (s:=s0).
 assumption.
 assumption.
 substs.
 exists (e #> e').
 intuition.
 apply simpl_weakred with (s:=sstar1).
 apply JO_red_forkdeath2.
 assumption.
 substs.
 apply forkee_s_endr.
 assumption.
 apply star_refl.
 substs.
 exists (e <# e').
 intuition.
 apply simpl_weakred with (s:=sstar1).
 apply JO_red_forkdeath1.
 assumption.
 apply forkee_s_endl.
 assumption.
 apply star_refl.
 substs.
 specialize swapf_right_b with (v:=(E_live_expr e'))(v':=e).
 intros.
 assert (H3:=H0).
 simpl in H2.
 apply H2 in H3.
 apply ttau_midpoint with (e':=q) in H3.
 split.
 intros.
 apply red_not_value in H4; simpl in H4; intuition.
 intros.
  exists (e <# e').
 split.
 intuition.
 apply tau_incl_totalTau  in H5.
 apply taured_val_id in H5.
 substs.
 apply red_not_value in H4; simpl in H4; intuition.
 simpl; auto.
 assert (rl=RL_tau).
 inversion H5.
 substs.
 apply red_not_value in H4; simpl in H4; intuition.
 substs.
 inversion H3.
 intuition.
 substs.
 induction rl.
 reflexivity.
 apply H7 in H4; intuition.
 substs.
 apply weakred_T.
 apply star_refl.
 intuition.
 inversion H5.
 substs.
 apply red_not_value in H4; simpl in H4; intuition.
 substs.
 apply tts_not_val in H3.
 simpl in H3; intuition.
 apply forkee_s_endl.
 assumption.
 apply star_S with (y:=q).
 assumption.
 inversion H5.
 substs.
 apply red_not_value in H4; simpl in H4; intuition.
 substs.
 inversion H3.
 intuition.
 substs.
 induction rl.
 apply tStep in H4.
 apply H12 in H4.
 substs.
 assumption.
 apply H7 in H4; intuition.
 assumption.
 trivial.
 substs.
 specialize swapf_left_b with (v:=e')(v':=(E_live_expr e)).
 intros.
 assert (H3:=H0).
 simpl in H2.
 apply H2 in H3.
 apply ttau_midpoint with (e':=q) in H3.
 split.
 intros.
 apply red_not_value in H4; simpl in H4; intuition.
 intros.
  exists (e #> e').
 split.
 intuition.
 apply tau_incl_totalTau  in H5.
 apply taured_val_id in H5.
 substs.
 apply red_not_value in H4; simpl in H4; intuition.
 simpl; auto.
 assert (rl=RL_tau).
 inversion H5.
 substs.
 apply red_not_value in H4; simpl in H4; intuition.
 substs.
 inversion H3.
 intuition.
 substs.
 induction rl.
 reflexivity.
 apply H7 in H4; intuition.
 substs.
 apply weakred_T.
 apply star_refl.
 intuition.
 inversion H5.
 substs.
 apply red_not_value in H4; simpl in H4; intuition.
 substs.
 apply tts_not_val in H3.
 simpl in H3; intuition.
 apply forkee_s_endr.
 assumption.
 apply star_S with (y:=q).
 assumption.
 inversion H5.
 substs.
 apply red_not_value in H4; simpl in H4; intuition.
 substs.
 inversion H3.
 intuition.
 substs.
 induction rl.
 apply tStep in H4.
 apply H12 in H4.
 substs.
 assumption.
 apply H7 in H4; intuition.
 assumption.
 trivial.
Qed.
 
Theorem fork_comm_swapped_rel_vewbsm : isExprRelationValueEqualWeakBisimilarity fork_comm_swapped_rel.
Proof.
 unfold isExprRelationValueEqualWeakBisimilarity.
 intuition.
 apply isExprRelationWeakBisimilarity_equiv_isExprRelationStepWeakBisimilarity.
 apply fork_comm_swapped_wbsm.
 inversion H1; substs; simpl in H; simpl in H0; intuition.
 specialize swapf_right_b with (v:=(E_live_expr e'))(v':= e); intros.
 simpl in H4.
 apply H4 in H2.
 apply ttau_midpoint with (e':=vq) in H2.
 intuition.
 apply tau_incl_totalTau in H5.
 apply taured_val_id in H5.
 substs.
 reflexivity.
 simpl; auto.
 apply tau_incl_totalTau in H5.
 apply taured_val_id in H5.
 substs.
 reflexivity.
 simpl; auto.
 assumption.
 trivial.
 specialize swapf_left_b with (v:= e')(v':= (E_live_expr e)); intros.
 simpl in H4.
 apply H4 in H2.
 apply ttau_midpoint with (e':=vq) in H2.
 intuition.
 apply tau_incl_totalTau in H5.
 apply taured_val_id in H5.
 substs.
 reflexivity.
 simpl; auto.
 apply tau_incl_totalTau in H5.
 apply taured_val_id in H5.
 substs.
 reflexivity.
 simpl; auto.
 assumption.
 trivial.
Qed.
 

Lemma fork_not_associative_counterexample: forall (R : relation expr), isExprRelationStepWeakBisimilarity R -> R ((E_unit # E_unit ) # (E_comp E_unit) ) (E_unit # (E_unit # (E_comp E_unit) )) -> False.
Proof.
 intros.
 unfold isExprRelationStepWeakBisimilarity in H.
 apply H in H0.
 intuition.
 specialize H1 with (p':=((E_unit # E_unit) # E_unit))(s:= S_Seq SO_Second sstar1)(rl:=RL_labelled E_unit).
 assert ((E_unit # E_unit) # E_comp E_unit [S_Seq SO_Second sstar1]-->
     [RL_labelled E_unit](E_unit # E_unit) # E_unit).
 apply JO_red_forkmove2.
 apply JO_red_docomp.
 simpl; auto.
 apply H1 in H0.
 destruct H0.
 intuition.
 inversion H3.
 substs.
 inversion H5.
 intuition.
 inversion H9.
 substs.
 inversion H0.
 apply red_not_value in H13; simpl in H13; intuition.
 apply red_not_value in H14; simpl in H14; intuition.
 inversion H8.
 simpl in H14; intuition.
 inversion H10.
 inversion H15.
 substs.
 apply red_not_value in H23; simpl in H23; intuition.
 apply red_not_value in H24; simpl in H24; intuition.
 inversion H20.
 simpl in H24; intuition.
 substs.
 apply taured_val_id in H12.
 substs.
 apply red_not_value in H0; simpl in H0; intuition.
 apply taured_val_id in H12.
 substs.
 intuition.
 intuition.
 simpl in H21; intuition.
Qed.
