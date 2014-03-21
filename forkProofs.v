Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Classical_Prop.


Load mconbaseMonProofs.

Load LibTactics.






Definition swapbodyl : expr :=E_apply ( E_constant CONST_ret )  
                                   ( 
                                     ( E_taggingright
                                        (E_apply 
                                          ( E_apply (E_constant CONST_pair)  
                                                    (E_apply (E_constant CONST_proj2) (E_ident (1))) 
                                          ) 
                                          (E_apply (E_constant CONST_proj1) (E_ident (1)))  
                                        )
                                     )
                                    ).

Definition swapbodyr : expr :=E_apply ( E_constant CONST_ret )  
                                   (E_taggingleft  
                                     ( 
                                        (E_apply 
                                          ( E_apply (E_constant CONST_pair)  
                                                    (E_apply (E_constant CONST_proj2) (E_ident (2))) 
                                          ) 
                                          (E_apply (E_constant CONST_proj1) (E_ident (2)))  
                                        )
                                     )
                                    ).

Definition swapbody : expr := E_case (E_ident (0)) 
           (1) ( 
                 swapbodyl
               ) 
           (2) (

                swapbodyr

               ).

Definition swapf : expr :=
    E_function (0) ((  (TE_sum  (TE_sum  (TE_prod (TE_var(TV_ident(2))) (TE_var(TV_ident(1))))   (TE_prod (TE_var(TV_ident(2)))  (TE_concurrent (TE_var(TV_ident(1)))) ) )   (TE_prod  (TE_concurrent (TE_var(TV_ident(2))))  (TE_var(TV_ident(1)))) ) )) 
      (
       swapbody

      ).

Lemma JO_red_evalcaseinl_td : forall (x:value_name) (e:expr) (x':value_name) (e':expr) (v:expr),
     is_value_of_expr v ->
     totalDetTauStep (E_case  (E_taggingleft v)  x e x' e')  (subst_expr  v   x   e ).
Proof.
 intros.
 apply ttStep.
 split.
 apply tStep with (s:=S_First).
 apply JO_red_evalcaseinl.
 trivial.
 split.
 intros.
 inversion H0.
 inversion H9.
 apply red_not_value in H11; contradiction.
 intros.
 inversion H0.
 inversion H1.
 reflexivity.
 inversion H12.
 apply red_not_value in H14; contradiction.
Qed. 

Lemma JO_red_evalcaseinr_td : forall (x:value_name) (e:expr) (x':value_name) (e':expr)  (v:expr),
     is_value_of_expr v ->
     totalDetTauStep (E_case  (E_taggingright v)  x e x' e') (subst_expr  v   x'   e' ).
Proof.
 intros.
 apply ttStep.
 split.
 apply tStep with (s:=S_First).
 apply JO_red_evalcaseinr.
 trivial.
 split.
 intros.
 inversion H0.
 inversion H9.
 apply red_not_value in H11; contradiction.
 intros.
 inversion H0.
 inversion H1.
 reflexivity.
 inversion H12.
 apply red_not_value in H14; contradiction.
Qed.

Lemma JO_red_inpair_td : forall (v v':expr),
     is_value_of_expr v ->
     is_value_of_expr v' ->
     totalDetTauStep (E_apply  (E_apply (E_constant CONST_pair) v)  v')  (E_pair v v').
Proof.
 intros.
 apply ttStep.
 split.
 apply tStep with (s:=S_First).
 apply JO_red_inpair.
 trivial.
 trivial.
 split.
 intros.
 inversion H1.
 apply red_not_value in H7; contradiction.
 inversion H8.
 apply red_not_value in H14; contradiction.
 inversion H15.
 intros.
 inversion H1.
 inversion H2.
 apply red_not_value in H10; contradiction.
 inversion H11.
 apply red_not_value in H17; contradiction.
 inversion H18.
 reflexivity.
Qed.


Lemma JO_red_proj1_td : forall (v v':expr),
     is_value_of_expr v ->
     is_value_of_expr v' ->
     totalDetTauStep (E_apply (E_constant CONST_proj1) (E_pair v v'))  v.
Proof.
 intros.
 apply ttStep.
 split.
 apply tStep with (s:=S_First).
 apply JO_red_proj1.
 trivial.
 trivial.
 split.
 intros.
 inversion H1.
 inversion H7.
 apply red_not_value in H13; contradiction.
 apply red_not_value in H14; contradiction.
 inversion H8.
 intros.
 inversion H1.
 inversion H2.
 inversion H10.
 apply red_not_value in H16; contradiction.
 apply red_not_value in H17; contradiction.
 inversion H11.
 reflexivity.
Qed.


Lemma JO_red_proj2_td : forall (v v':expr) ,
     is_value_of_expr v ->
     is_value_of_expr v' ->
     totalDetTauStep (E_apply (E_constant CONST_proj2) (E_pair v v')) v'.
Proof.
 intros.
 apply ttStep.
 split.
 apply tStep with (s:=S_First).
 apply JO_red_proj2.
 trivial.
 trivial.
 split.
 intros.
 inversion H1.
 inversion H7.
 apply red_not_value in H13; contradiction.
 apply red_not_value in H14; contradiction.
 inversion H8.
 intros.
 inversion H1.
 inversion H2.
 inversion H10.
 apply red_not_value in H16; contradiction.
 apply red_not_value in H17; contradiction.
 inversion H11.
 reflexivity.
Qed.

Lemma tau_app1 : forall (e e' e'' : expr),
       tauStep (e') (e'') ->
       tauStep (E_apply e e') (E_apply e e'').
Proof.
 intros.
 inversion H.
 apply tStep with (s:=s).
 apply JO_red_context_app1.
 trivial.
Qed.

Lemma tau_app2 : forall (e e' e'' : expr),
       is_value_of_expr e' ->
       tauStep (e) (e'') ->
       tauStep (E_apply e e') (E_apply e'' e').
Proof.
 intros.
 inversion H0.
 apply tStep with (s:=s).
 apply JO_red_context_app2.
 trivial.
 trivial.
Qed.

Lemma  JO_red_context_app1_td : forall (e e':expr) (e'':expr),
     ~ (is_value_of_expr e') ->
     totalDetTauStep e' e'' ->
     totalDetTauStep (E_apply e e') (E_apply e e'').
Proof.
intros.
 apply ttStep.
 split.
 inversion H0.
 elim H1.
 intros.
 apply tau_app1.
 trivial.
 split.
 intros.
 inversion H1.
 rewrite <- H4 in H; simpl in H; auto.
rewrite <- H4 in H; simpl in H; auto.
 rewrite <- H4 in H; simpl in H; auto.
 rewrite <- H4 in H; simpl in H; auto.
 rewrite <- H4 in H; simpl in H; auto.
 substs.
 inversion H0.
 intuition.
 apply H2 in H7.
 auto.
 contradiction.
 intros.
 inversion H1.
 inversion H2.
 contradiction.
 rewrite <- H7 in H; simpl in H; auto.
 intuition.
 rewrite <- H7 in H; simpl in H; auto.
 intuition.
 rewrite <- H7 in H; simpl in H; auto.
 intuition.
 rewrite <- H7 in H; simpl in H; auto; intuition.
 contradiction.
 substs.
 inverts H0.
 intuition.
 f_equal.
 apply H5. 
 apply tStep with (s:=s); trivial.
 substs.
 contradiction.
 substs.
 contradiction.
 substs.
 contradiction.
 substs.
 simpl in H.
 intuition.
 substs.
 simpl in H; intuition.
Qed.

Lemma simpTau : forall(e e' : expr) (s: select),  
      e [s] --> [RL_tau] e' -> tauStep e e'.
Proof.
 intros.
 apply tStep with (s:=s).
 trivial.
Qed.

Hint Resolve simpTau.

Lemma JO_red_evalinl_td : forall (e:expr) (e':expr),
     (~ is_value_of_expr e) -> 
     totalDetTauStep e e' ->
     totalDetTauStep (E_taggingleft e) (E_taggingleft e').
Proof.
 intros.
 inversion H0.
 intuition.
 apply ttStep.
 split.
 inversion H4.
 apply tStep with (s:= s).
 apply JO_red_evalinl.
 trivial.
 split; intros.
 inversion H5.
 apply H1 in H8.
 trivial.
 inversion H5.
 inversion H7.
 cut (tauStep e e'2).
 intros.
 apply H6 in H15; trivial.
 f_equal.
 trivial.
 eauto.
Qed.

Lemma JO_red_evalinr_td : forall (e:expr) (e':expr),
     (~ is_value_of_expr e) -> 
     totalDetTauStep e e' ->
     totalDetTauStep (E_taggingright e) (E_taggingright e').
Proof.
 intros.
 inversion H0.
 intuition.
 apply ttStep.
 split.
 inversion H4.
 apply tStep with (s:= s).
 apply JO_red_evalinr.
 trivial.
 split; intros.
 inversion H5.
 apply H1 in H8.
 trivial.
 inversion H5.
 inversion H7.
 cut (tauStep e e'2).
 intros.
 apply H6 in H15; trivial.
 f_equal.
 trivial.
 eauto.
Qed.

Lemma  JO_red_context_app2_td : forall (e e':expr) (e'':expr),
     (is_value_of_expr e') ->
     ~ (is_value_of_expr e) ->
     totalDetTauStep e e'' ->
     totalDetTauStep (E_apply e e') (E_apply e'' e').
Proof.
intros.
 apply ttStep.
 split.
 inversion H1.
 elim H2.
 intros.
 apply tau_app2.
 trivial.
 trivial.
 split.
 intros.
 inversion H2.
 rewrite <- H3 in H0; simpl in H0; auto.
 rewrite <- H3 in H0; simpl in H0; auto.
 rewrite <- H4 in H0; simpl in H0; auto.
 rewrite <- H4 in H0; simpl in H0; auto.
 substs.
 apply red_not_value in H8; intuition.
 substs.
 inversion H1.
 intuition.
 apply H3 in H9.
 auto.
 intros.
 inversion H2.
 inversion H3.
 substs; simpl in H0; auto.
 intuition.
 rewrite <- H6 in H0; simpl in H0; auto.
 intuition.
 rewrite <- H6 in H0; simpl in H0; auto.
 intuition.
 rewrite <- H6 in H0; simpl in H0; auto.
 intuition.
 rewrite <- H6 in H0; simpl in H0; auto; intuition.
 substs; simpl in H0; intuition.
 apply red_not_value in H11; contradiction.
 substs.
 inverts H1.
 intuition.
 f_equal.
 apply H6. 
 apply tStep with (s:=s); trivial.
 substs.
 contradiction.
 substs.
 contradiction.
 substs.
 simpl in H0; intuition. 
 substs.
 simpl in H0; intuition. 
Qed.


Lemma swapf_right : forall (v v' : expr), 
           is_value_of_expr v ->
           is_value_of_expr v' ->
           totalTauRed ( E_apply (swapf) (E_taggingright (( E_pair v v' )) ) ) (E_live_expr(LM_expr(E_taggingleft( ( ( E_pair v' v )) )))).
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
 apply S_star with (y:=E_apply ( E_constant CONST_ret )
                                    ( E_taggingleft 
                                     (
                                        (E_apply 
                                          ( E_apply (E_constant CONST_pair)  
                                                    (E_apply (E_constant CONST_proj2) ( E_pair v v' )) 
                                          ) 
                                          (v)  
                                        )
                                     ))).
 simpl.
 apply JO_red_context_app1_td.
 simpl.
 intuition.
 apply JO_red_evalinl_td.
 simpl; auto.
 apply JO_red_context_app1_td.
 simpl; auto.
 apply JO_red_proj1_td.
 trivial.
 trivial.
 apply S_star with (y:=E_apply ( E_constant CONST_ret ) 
                                    ( E_taggingleft 
                                     ( 
                                        (E_apply 
                                          ( E_apply (E_constant CONST_pair)  
                                                    (v') 
                                          ) 
                                          (v)  
                                        )
                                     ))).
 apply JO_red_context_app1_td.
 simpl; auto.
 apply JO_red_evalinl_td.
 simpl; auto.
 apply JO_red_context_app2_td.
 simpl; auto.
 simpl; auto.
 apply JO_red_context_app1_td.
 simpl; auto.
 apply JO_red_proj2_td.
 trivial.
 trivial.
 apply S_star with (y:=((E_apply (E_constant CONST_ret)
     ( E_taggingleft (
        ( (E_pair v' v))))))).
 apply JO_red_context_app1_td.
 simpl; auto.
 apply JO_red_evalinl_td.
 simpl; auto.
 apply JO_red_inpair_td.
 simpl; auto.
 simpl; auto.
 apply S_star with (y:=(E_live_expr (LM_expr (E_taggingleft (((E_pair v' v))))))).
 apply JO_red_ret_td.
 apply S_First.
 simpl;auto.
 apply star_refl.
Qed.

Lemma swapf_right_b : forall (v v' : expr), 
           is_value_of_expr v ->
           is_value_of_expr v' ->
           totalTauRed ( (E_live_expr ( LM_expr (E_taggingright (( E_pair v v' )))) ) >>= swapf) (E_live_expr(LM_expr(E_taggingleft( ( ( E_pair v' v )) )))).
Proof.
 intros.
 apply S_star  with (y:=(E_apply (swapf) (E_taggingright (( E_pair v v' )) ))).
 apply JO_red_dobind_td.
 apply S_First.
 simpl; auto.
 apply swapf_right.
 assumption.
 assumption.
Qed.

Lemma swapf_left : forall (v v' : expr), 
           is_value_of_expr v ->
           is_value_of_expr v' ->
           totalTauRed ( E_apply (swapf) (E_taggingleft ( ( E_pair v v' )) ) ) (E_live_expr(LM_expr( (E_taggingright ( E_pair v' v )) ))).
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
 apply S_star with (y:=E_apply ( E_constant CONST_ret )  
                                   (  
                                     ( E_taggingright
                                        (E_apply 
                                          ( E_apply (E_constant CONST_pair)  
                                                    (E_apply (E_constant CONST_proj2) (E_pair v v' )) 
                                          ) 
                                          (v)  
                                        )
                                     )
                                   )).
 simpl.
 apply JO_red_context_app1_td.
 simpl.
 intuition.
 apply JO_red_evalinr_td.
 simpl; auto.
 apply JO_red_context_app1_td.
 simpl; auto.
 apply JO_red_proj1_td.
 trivial.
 trivial.
 apply S_star with (y:=(E_apply (E_constant CONST_ret)
       (
          (E_taggingright
             (E_apply
                (E_apply (E_constant CONST_pair)
                   (v')) v))))).
 apply JO_red_context_app1_td.
 simpl; auto.
  apply JO_red_evalinr_td.
 simpl; auto.
 apply JO_red_context_app2_td.
 simpl; auto.
 simpl; auto.
 apply JO_red_context_app1_td.
 simpl; auto.
 apply JO_red_proj2_td.
 trivial.
 trivial.
 apply S_star with (y:=((E_apply (E_constant CONST_ret)
     (
        (E_taggingright (E_pair v' v)))))).
 apply JO_red_context_app1_td.
 simpl; auto.
 apply JO_red_evalinr_td.
 simpl; auto.
 apply JO_red_inpair_td.
 simpl; auto.
 simpl; auto.
 apply S_star with (y:=(E_live_expr (LM_expr ((E_taggingright (E_pair v' v)))))).
 apply JO_red_ret_td.
 apply S_First.
 simpl;auto.
 apply star_refl.
Qed.

Lemma swapf_left_b : forall (v v' : expr), 
           is_value_of_expr v ->
           is_value_of_expr v' ->
           totalTauRed (  (E_live_expr(LM_expr(E_taggingleft ( ( E_pair v v' )) ))) >>= (swapf)) (E_live_expr(LM_expr( (E_taggingright ( E_pair v' v )) ))).
Proof.
 intros.
 apply S_star  with (y:=(E_apply (swapf) ((E_taggingleft ( (E_pair v v')) )))).
 apply JO_red_dobind_td.
 apply S_First.
 simpl; auto.
 apply swapf_left.
 assumption.
 assumption.
Qed.



Lemma simp_lab_r : forall (e e' : expr) (s :select) (l : label), JO_red e s (RL_labelled l) e' -> labRed l e e'.
Proof.
 intros.
 apply lab_r with (e1:=e)(e2:=e')(s:=s).
 splits.
 apply star_refl.
 trivial.
 apply star_refl.
Qed.

Lemma taured_val_id : forall (e e' : expr), tauRed e e' -> is_value_of_expr e -> e = e'.
Proof.
 intros.
 inversion H.
 reflexivity.
 inversion H1.
 apply red_not_value in H5; contradiction.
Qed.

Lemma labred_not_val : forall (e e' : expr)(l : label), labRed l e e' -> ~(is_value_of_expr e).
Proof.
 intros.
 inversion H.
 intuition.
 apply taured_val_id in H5; intuition; substs.
 apply red_not_value in H0.
 contradiction.
Qed. 


Check star_ind.

Lemma bind_tau_behave_front : forall ( e e' x : expr), tauRed e x -> tauRed (e >>= e') (x >>= e').
Proof.
 intros.
 apply star_ind with (R:=tauStep)(X:=expr)(P:= (fun y z => tauRed (y >>= e') (z >>= e'))).
 intros.
 apply star_refl.
 intros.
 apply S_star with (y:=(y>>=e')).
 inversion H0.
 apply tStep with (s:= s).
 apply JO_red_evalbind.
 assumption.
 assumption.
 assumption.
Qed.

Lemma bind_lab_behave_front : forall ( e e' x : expr) (l : label), labRed l e x -> labRed l (e >>= e') (x >>= e').
Proof.
 intros.
 inversion H.
 intuition.
 substs.
 apply lab_r with (e1:=(e1 >>= e'))(e2:=(e2 >>= e'))(s:=s).
 splits; [apply bind_tau_behave_front; assumption | apply JO_red_evalbind; assumption | apply bind_tau_behave_front; assumption ].
Qed.

Lemma fork_tau_behave_edge1 : forall  (e e' x : expr), tauRed e x -> ~ (is_value_of_expr e') -> tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e))) (E_live_expr (LM_expr e'))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr x))) (E_live_expr (LM_expr e'))).
Proof. 
 intros.
 apply star_ind with (R:=tauStep)(X:=expr)(P:= (fun y z => tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr y))) (E_live_expr (LM_expr e'))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr z))) (E_live_expr (LM_expr e'))))).
 intros; apply star_refl.
 intros.
 apply S_star with (y:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr y))) (E_live_expr (LM_expr e')))).
 apply tStep with (s:=S_First).
 inversion H1.
 apply  JO_red_forkmove1 with (s:=s).
 assumption.
 assumption.
 assumption.
Qed.

Lemma fork_tau_behave_edge2 : forall  (e e' x : expr), tauRed e' x -> ~ (is_value_of_expr e) -> tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e))) (E_live_expr (LM_expr e'))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e))) (E_live_expr (LM_expr x))).
Proof. 
 intros.
 apply star_ind with (R:=tauStep)(X:=expr)(P:= (fun y z => tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e))) (E_live_expr (LM_expr y))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e))) (E_live_expr (LM_expr z))))).
 intros; apply star_refl.
 intros.
 apply S_star with (y:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e))) (E_live_expr (LM_expr y)))).
 apply tStep with (s:=S_Second).
 inversion H1.
 apply  JO_red_forkmove2 with (s:=s).
 assumption.
 assumption.
 assumption.
Qed.

Lemma fork_lab_behave_edge1 : forall  (e e' x : expr) (l:label), labRed l e x -> ~ (is_value_of_expr e') -> labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e))) (E_live_expr (LM_expr e'))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr x))) (E_live_expr (LM_expr e'))).
Proof.
 intros.
 inversion H.
 intuition.
 substs.
 apply lab_r with (e1:= (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e1)))
     (E_live_expr (LM_expr e'))))(e2:= (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e2)))
     (E_live_expr (LM_expr e'))))(s:=S_First).
 splits.
 apply fork_tau_behave_edge1;[ assumption | assumption ].
 apply JO_red_forkmove1 with (s:=s);  assumption .
 apply fork_tau_behave_edge1; [ assumption |  assumption ].
Qed.

Lemma fork_tau_behave_edge12 : forall  (e e' x y : expr), tauRed e' x -> tauRed e y -> ~ is_value_of_expr e' -> ~ (is_value_of_expr e) -> ~ is_value_of_expr y -> ~ (is_value_of_expr x) -> tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e))) (E_live_expr (LM_expr e'))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr y))) (E_live_expr (LM_expr x))).
Proof. 
 intros.
 assert (He:=H0).
 apply fork_tau_behave_edge1 with (e':=e') in He.
 assert (He':=H).
 apply fork_tau_behave_edge2 with (e:=y) in He'.
 apply star_trans with (y:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr y)))
          (E_live_expr (LM_expr e')))).
 assumption.
 assumption.
 assumption.
 assumption.
Qed.




Lemma fork_lab_behave_edge2 : forall  (e e' x : expr) (l:label), labRed l e' x -> ~ (is_value_of_expr e) -> labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e))) (E_live_expr (LM_expr e'))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e))) (E_live_expr (LM_expr x))).
Proof.
 intros.
 inversion H.
 intuition.
 substs.
 apply lab_r with (e1:= (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e)))
     (E_live_expr (LM_expr e1))))(e2:= (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e)))
     (E_live_expr (LM_expr e2))))(s:=S_Second).
 splits.
 apply fork_tau_behave_edge2;[ assumption | assumption ].
 apply JO_red_forkmove2 with (s:=s); assumption.
 apply fork_tau_behave_edge2; [ assumption |  assumption ].
Qed.


Inductive fork_tau_ce_int_s : relation expr :=
 | fork_tau_ce_int_step : forall (e e' : expr) (l : label), tauStep e e' -> fork_tau_ce_int_s (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_comp l)))
          (E_live_expr (LM_expr e))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_comp l)))
          (E_live_expr (LM_expr e'))).
Inductive fork_tau_ce_ext_s : relation expr :=
 | fork_tau_ce_ext_step : forall (e e' : expr) (l : label), tauStep (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_comp l)))
          (E_live_expr (LM_expr e))) e' -> fork_tau_ce_ext_s (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_comp l)))
          (E_live_expr (LM_expr e))) e'.



Lemma fork_tau_behave_ce: forall (expr5 e : expr) (lab : label), tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_comp lab)))
          (E_live_expr (LM_expr expr5))) e -> ((e = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_comp lab)))
          (E_live_expr (LM_expr expr5))))\/(e = E_live_expr
       (LM_expr (E_taggingright (E_pair (E_live_expr (LM_comp lab)) expr5))) /\ is_value_of_expr expr5)) .
Proof.
 intros.
 inversion H.
 substs.
 auto.
 substs.
 inversion H0.
 substs.
 inversion H2.
 right.
 substs.
 apply taured_val_id in H1.
 substs.
 splits.
 reflexivity.
 assumption.
 simpl; auto.
 apply red_not_value in H8; simpl in H8; intuition.
 apply red_not_value in H9; simpl in H9; intuition.
Qed.

Lemma fork_label_origin_ce: forall (expr5 e : expr) (lab l : label), labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_comp lab)))
          (E_live_expr (LM_expr expr5))) e -> (l=lab).
Proof.
 intros.
 inversion H; intuition; substs.
 apply fork_tau_behave_ce in H4.
 substs.
 intuition; substs.
 inversion H0; intuition; substs.
 apply red_not_value in H7; simpl in H7; intuition.
 apply red_not_value in H8; simpl in H8; intuition.
 apply red_not_value in H0; simpl in H0; intuition.
Qed.

Lemma fork_tau_behave_ec: forall (expr5 e : expr) (lab : label), tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr expr5)) ) (E_live_expr (LM_comp lab))) e -> 
 ((e = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr expr5))) (E_live_expr (LM_comp lab))))\/(e=E_live_expr
       (LM_expr (E_taggingleft (E_pair expr5 (E_live_expr (LM_comp lab))))) /\ is_value_of_expr expr5)) .
Proof.
 intros.
 inversion H.
 left.
 reflexivity.
 substs.
 inversion H0.
 substs.
 inversion H2.
 substs.
 apply taured_val_id in H1.
 substs.
 right.
 splits.
 reflexivity.
 assumption.
 simpl; auto.
 apply red_not_value in H8; simpl in H8; intuition.
 apply red_not_value in H9; simpl in H9; intuition.
Qed.

Lemma fork_label_origin_ec: forall (expr5 e : expr) (lab l : label), labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr expr5))) (E_live_expr (LM_comp lab))) e -> (l=lab (* \/ (exists (e' : expr), labRed l expr5 e' /\ e = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e'))) (E_live_expr (LM_comp lab))))*)).
Proof.
 intros.
 inversion H; intuition; substs.
 apply fork_tau_behave_ec in H4.
 substs.
 intuition.
 substs.
 inversion H0; intuition; substs.
 apply red_not_value in H7; simpl in H7; intuition.
 apply red_not_value in H8; simpl in H8; intuition.
 substs.
 apply red_not_value in H0; simpl in H0; intuition.
Qed.

Lemma fork_tau_behave_cc : forall (e : expr) (lab1 lab2 : label), tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_comp lab1))) (E_live_expr (LM_comp lab2))) e -> e= (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_comp lab1))) (E_live_expr (LM_comp lab2))).
Proof.
 intros.
 inversion H.
 reflexivity.
 substs.
 inversion H0.
 substs.
 inversion H2.
 substs.
  apply red_not_value in H8; simpl in H8; intuition.
 apply red_not_value in H9; simpl in H9; intuition.
Qed.

Lemma fork_label_origin_cc: forall (e : expr) (lab1 lab2 l : label), labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_comp lab1))) (E_live_expr (LM_comp lab2))) e -> 
((l=lab1 /\ e = (E_live_expr
       (LM_expr
          (E_taggingleft
             (E_pair (E_constant CONST_unit) (E_live_expr (LM_comp lab2))))))) 
 \/ (l=lab2 /\ e =((E_live_expr
          (LM_expr
             (E_taggingright
                (E_pair (E_live_expr (LM_comp lab1)) (E_constant CONST_unit)))))) )).
Proof.
 intros.
 inversion H; intuition; substs.
 inversion H4; intuition; substs.
 inversion H0; intuition; substs.
 left. splits. reflexivity.
 inversion H6. reflexivity. substs. inversion H1. substs.
 inversion H3.
 apply taured_val_id in H6; substs.
 right.
 splits. reflexivity.
 reflexivity.
 simpl; auto.
 apply red_not_value in H8; simpl in H8; intuition.
 apply red_not_value in H9; simpl in H9; intuition.
 inversion H1; intuition; substs.
 inversion H3; intuition; substs.
 apply red_not_value in H11; simpl in H11; intuition.
 apply red_not_value in H12; simpl in H12; intuition.
Qed.


Lemma fork_tau_step_behave_ee: forall (p q e : expr), tauStep (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr p)) ) (E_live_expr (LM_expr q))) e -> 
   ((exists (p' q' : expr), tauRed p p' /\ tauRed q q' /\ e = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr p')) ) (E_live_expr (LM_expr q')))) \/ 
  ((exists (p' vq : expr), is_value_of_expr vq /\ tauRed p p' /\ tauRed q vq /\ e = ((E_live_expr (LM_expr  (  (E_taggingright  (E_pair  (E_live_expr (LM_expr p')) vq ) ) ) )))) \/ 
  ((exists (vp q' : expr), is_value_of_expr vp /\ tauRed p vp /\ tauRed q q' /\ e=((E_live_expr (LM_expr  (E_taggingleft  (  (E_pair vp (E_live_expr (LM_expr q'))  ) ) ) ))))))) .
Proof.
 intros.
 inversion H.
 substs.
 inversion H0; intuition; substs.
 left.
 exists e'' q; splits.
 apply S_star with (y:=e''); [ apply tStep with (s:=s0); assumption | apply star_refl]. apply star_refl.
 reflexivity.
 left.
 exists p e''; splits.
 apply star_refl.
 apply S_star with (y:=e''); [  apply tStep with (s:=s0); assumption | apply star_refl ]. 
 reflexivity.
 right. right.
 exists p q.
 splits; [ assumption | apply star_refl | apply star_refl | reflexivity ].
 right. left.
 exists p q.
 splits; [ assumption | apply star_refl | apply star_refl | reflexivity ].
 apply red_not_value in H6; simpl in H6; intuition.
 apply red_not_value in H7; simpl in H7; intuition.
Qed.


Definition  fork_tau_step_ee : expr -> expr -> Prop := (fun b e => (forall (p q : expr), b=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr p)) ) (E_live_expr (LM_expr q))) -> 
   ((exists (p' q' : expr), tauRed p p' /\ tauRed q q' /\ e = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr p')) ) (E_live_expr (LM_expr q')))) \/ 
  ((exists (p' vq : expr), is_value_of_expr vq /\ tauRed p p' /\ tauRed q vq /\ e = ((E_live_expr (LM_expr  (  (E_taggingright  (E_pair  (E_live_expr (LM_expr p')) vq ) ) ) )))) \/ 
  (
   (exists (vp q' : expr), is_value_of_expr vp /\ tauRed p vp /\ tauRed q q' /\ e=((E_live_expr (LM_expr  (E_taggingleft  ( (E_pair vp (E_live_expr (LM_expr q'))  ) ) ) ))))))))) .


Lemma fork_tau_behave_ee_h: forall (b e : expr), tauRed b e -> (fork_tau_step_ee) b e.
Proof.
 apply star_ind.
 intros.
 unfolds.
 intros.
 substs.
 left; exists p q; splits; [apply star_refl | apply star_refl | reflexivity].
 intros.
 unfolds in H1.
 unfolds.
 intros.
 substs.
 apply fork_tau_step_behave_ee in H.
 intuition.
 destruct H2; destruct H.
 specialize (H1 x x0).
 elim H; intros; elim H3; intros.
 apply H1 in H5.
 destruct H5.
 left.
 destruct H5 as [ p' H5]; destruct H5 as [ q' H5 ].
 exists p' q'.
 splits.
 apply star_trans with (y:=x); [ jauto | jauto ].
 apply star_trans with (y:=x0); [ jauto | jauto ].
 jauto.
 destruct H5.
 right; left.
 destruct H5 as [ p' H5]; destruct H5 as [ vq H5 ].
 exists p' vq.
 splits.
 jauto.
 apply star_trans with (y:=x); [ jauto | jauto ].
 apply star_trans with (y:=x0); [ jauto | jauto ].
 jauto.
 right; right.

 destruct H5 as [ vp H5]; destruct H5 as [ q' H5 ].
 exists vp q'.
 splits.
 jauto.
 jauto.
 apply star_trans with (y:=x); [ jauto | jauto ].
 apply star_trans with (y:=x0); [ jauto | jauto ].
 jauto.
 destruct H as [ x H]; destruct H as [ vy H ].
 right; left.
 exists x vy.
 splits. jauto. jauto. jauto.
 elim H; intros; clear H; elim H3; intros; clear H3; elim H4; intros; clear H4; substs.
 inversion H0.
 reflexivity.
 inversion H4.
 apply red_not_value in H8; simpl in H8; intuition.
 right; right.
 destruct H as [ vp H2]; destruct H2 as [ vq H2 ]; exists vp vq; splits; jauto;jauto;jauto;jauto.
 elim H2; intros; clear H2. elim H3; intros; clear H3. elim H4; intros; clear H4.  substs.
 apply taured_val_id in H0; substs; reflexivity.
Qed.
 
Lemma fork_tau_behave_ee : forall (p q e : expr), tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr p)) ) (E_live_expr (LM_expr q))) e -> 
((exists (p' q' : expr), tauRed p p' /\ tauRed q q' /\ e = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr p')) ) (E_live_expr (LM_expr q')))) \/ 
  ((exists (p' vq : expr), is_value_of_expr vq /\ tauRed p p' /\ tauRed q vq /\ e = ((E_live_expr (LM_expr  (  (E_taggingright  (E_pair  (E_live_expr (LM_expr p')) vq ) ) ) )))) \/ 
  (
   (exists (vp q' : expr), is_value_of_expr vp /\ tauRed p vp /\ tauRed q q' /\ e=((E_live_expr (LM_expr  (E_taggingleft  (  (E_pair vp (E_live_expr (LM_expr q'))  ) ) ) ))))))) .
Proof.
 intros.
 apply fork_tau_behave_ee_h in H.
 specialize (H p q).
 apply H.
 reflexivity.
Qed.
(*

Lemma fork_tau_serialise1 : forall (p q p' q': expr), tauRed
       (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr p)))
          (E_live_expr (LM_expr q)))
       (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr p')))
          (E_live_expr (LM_expr q'))) -> tauRed
       (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr p)))
          (E_live_expr (LM_expr q)))
       (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr p')))
          (E_live_expr (LM_expr q))).
Proof.
 intros.
 assert (H0 := H).
 apply fork_tau_behave_ee in H0.
 intuition.
 destruct H1.
 destruct H0.
 intuition.
 simplify_eq H3.
 intros; substs.
 clear H3.
 inversion H.
 substs.
 apply star_refl.
 substs.
 inversion H2.
 substs.
 inversion H4.
 substs.
 apply fork_tau_behave_edge1.
 assumption.
 assumption.
 substs.
 apply fork_tau_behave_edge1.
 assumption.
 apply red_not_value in H11.
 assumption.
 substs.
 inversion H3.
 substs.
 inversion H5.
 apply red_not_value in H7; simpl in H7; intuition.
 substs.
 inversion H3.
 substs.
 inversion H5.
 apply red_not_value in H7; simpl in H7; intuition.
 substs.
 inversion H3.
 substs.
 inversion H5.
 apply red_not_value in H8; simpl in H8; intuition.
 substs.
 apply red_not_value in H10; simpl in H10; intuition.
 substs.
 apply red_not_value in H11; simpl in H11; intuition.
 substs.
 destruct H0.
 destruct H0.
 intuition.
 discriminate H4.
 destruct H1.
 destruct H0.
 intuition.
 discriminate H5.
 destruct H1; destruct H0; intuition.
 discriminate H4.
Qed.
*)
Lemma fork_label_origin_ee : forall (e' e e'' : expr) (l : label), labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e)) ) (E_live_expr (LM_expr e'))) e'' -> 
 ((exists (f : expr), labRed l e f /\ (
((exists ( q' : expr), tauRed e' q' /\ e'' = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr f)) ) (E_live_expr (LM_expr q')))) \/ 
  ((exists ( vq : expr), is_value_of_expr vq /\ tauRed e' vq /\ e'' = ((E_live_expr (LM_expr  (  (E_taggingright  (E_pair  (E_live_expr (LM_expr f)) vq ) ) ) )))) \/ 
  (
   (exists ( q' : expr), is_value_of_expr f /\  tauRed e' q' /\ e''=((E_live_expr (LM_expr  (E_taggingleft  (  (E_pair f (E_live_expr (LM_expr q'))  ) ) ) )))))))

)) 


\/ 
  (exists (f : expr), labRed l e' f /\ (
((exists (p'  : expr), tauRed e p' /\ e'' = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr p')) ) (E_live_expr (LM_expr f)))) \/ 
  ((exists (p'  : expr), is_value_of_expr f /\ tauRed e p'  /\ e'' = ((E_live_expr (LM_expr  (  (E_taggingright  (E_pair  (E_live_expr (LM_expr p')) f ) ) ) )))) \/ 
  (
   (exists (vp : expr), is_value_of_expr vp /\ tauRed e vp  /\ e''=((E_live_expr (LM_expr  (E_taggingleft  (  (E_pair vp (E_live_expr (LM_expr f))  ) ) ) ))))))) 

))).
Proof.
 intros.
 inversion H; substs.
 elim H0; intros; substs; clear H0.
 apply fork_tau_behave_ee in H1.
 destruct H1.
 destruct H0; destruct H0.
 elim H0; intros; clear H0.
 elim H3; intros; clear H3.
 substs.
 elim H2; intros; clear H2.
 inversion H3.
 substs.
 left. 
 apply fork_tau_behave_ee in H4.
 destruct H4.
 destruct H2; destruct H2.
 exists x1. splits. apply lab_r with (e1:=x)(e2:=e''0)(s:=s0).
 splits; [ assumption | assumption |  intuition ].
 substs.
 intuition.
 substs.
 left.
 exists x2; splits; [ apply star_trans with (y:=x0); [ assumption | assumption ] | reflexivity ].
 destruct H2; destruct H2.
 destruct H2.
 exists x1. splits. apply lab_r with (e1:=x)(e2:=e''0)(s:=s0).
 splits; [ assumption | assumption |  intuition ].
 substs.
 intuition.
 substs.
 right; left.
 exists x2; splits; [ assumption | apply star_trans with (y:=x0); [ assumption | assumption ] | reflexivity ].
 destruct H2; destruct H2.
 exists x1. splits. apply lab_r with (e1:=x)(e2:=e''0)(s:=s0).
 splits; [ assumption | assumption |  intuition ].
 substs.
 intuition.
 substs.
 (*right; left.
 exists x2; splits; [ assumption | assumption | apply star_trans with (y:=x0); [ assumption | assumption ] | reflexivity ].
 destruct H2; destruct H2.
 exists x1. splits. apply lab_r with (e1:=x)(e2:=e''0)(s:=s0).
 splits; [ assumption | assumption |  intuition ].
 substs.
 intuition.
 substs. *)
 right; right. 
 exists x2; splits; [ assumption | apply star_trans with (y:=x0); [ assumption | assumption ] | reflexivity ].
 substs.


 right.
 
 apply fork_tau_behave_ee in H4.
 destruct H4.
 destruct H2; destruct H2.
 exists x2. splits. apply lab_r with (e1:=x0)(e2:=e''0)(s:=s0).
 splits; [ assumption | assumption |  intuition ].
 substs.
 intuition.
 substs.
 left.
 exists x1; splits; [ apply star_trans with (y:=x); [ assumption | assumption ] | reflexivity ].
 destruct H2; destruct H2.
 destruct H2.
 exists x2. splits. apply lab_r with (e1:=x0)(e2:=e''0)(s:=s0).
 splits; [ assumption | assumption |  intuition ].
 substs.
 intuition.
 substs.
 right; left.
 exists x1; splits; [ assumption | apply star_trans with (y:=x); [ assumption | assumption ] | reflexivity ].
 destruct H2; destruct H2.
 exists x2. splits. apply lab_r with (e1:=x0)(e2:=e''0)(s:=s0).
 splits; [ assumption | assumption |  intuition ].
 substs.
 intuition.
 substs. (*
 right; right; left.
 exists x1; splits; [ assumption | assumption | apply star_trans with (y:=x); [ assumption | assumption ] | reflexivity ].
 destruct H2; destruct H2.
 exists x2. splits. apply lab_r with (e1:=x0)(e2:=e''0)(s:=s0).
 splits; [ assumption | assumption |  intuition ].
 substs.
 intuition.
 substs.*)
 right; right.
 exists x1; splits; [ assumption | apply star_trans with (y:=x); [ assumption | assumption ] | reflexivity ].
 substs.
 

 apply red_not_value in H9; simpl in H9; intuition.
 substs.
 apply red_not_value in H10; simpl in H10; intuition.
 substs.
 elim H2; intros; clear H2.
 apply red_not_value in H1.
 destruct H0.
 destruct H0; destruct H0; intuition; substs; simpl in H1; intuition. 
 destruct H0.
 destruct H0; destruct H0; intuition; substs; simpl in H1; intuition.
Qed.



Lemma fork_tau_swap_ee_non_val : forall (p q p' q': expr), (~ (is_value_of_expr p)) -> (~(is_value_of_expr q)) ->  (~ (is_value_of_expr p')) -> (~(is_value_of_expr q')) ->  tauRed
       (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr p)))
          (E_live_expr (LM_expr q)))
       (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr p')))
          (E_live_expr (LM_expr q'))) -> tauRed
       (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr q)))
          (E_live_expr (LM_expr p)))
       (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr q')))
          (E_live_expr (LM_expr p'))).
Proof.
 intros.
 apply fork_tau_behave_ee in H3.
 intuition.
 destruct H4; destruct H3; intuition.
 simplify_eq H6; intros; substs.
 apply fork_tau_behave_edge12.
 assumption. assumption. assumption. assumption. assumption. assumption.
 destruct H3; destruct H3; intuition.
 simplify_eq H7; intros; substs.
 destruct H3; destruct H3; intuition.
 simplify_eq H7; intros; substs; assumption.
Qed.




Lemma star_rev_ind : forall (X :Type) (R: relation X) (P : X -> X -> Prop),
      (forall x : X, P x x) ->
       (forall y x z : X, star R x y -> R y z -> P x y -> P x z) ->
       forall x x0 : X, star R x x0 -> P x x0.
Proof.
 intros.
 assert (star ( trans R ) x0 x).
 assert ((trans ( star R) ) x0 x).
 unfold trans.
 assumption.
 assert (eeq (trans (star R)) (star (trans R))).
 apply inv_star.
 intuition.
 unfold eeq in H3.
 intuition.
 assert (H3:=H2).
 induction H2.
 apply H.
 substs.
 apply H0 with (y:=y).
 assert ((trans ( star R) ) y z).
 assert (eeq (trans (star R)) (star (trans R))).
 apply inv_star.
 intuition.
 unfold eeq in H5.
 intuition.
 unfold trans in H5.
 assumption.
 unfold trans in H2.
 assumption.
 apply IHstar.
 assert ((trans ( star R) ) y z).
 assert (eeq (trans (star R)) (star (trans R))).
 apply inv_star.
 intuition.
 unfold eeq in H5.
 intuition.
 unfold trans in H5.
 assumption.
 assumption.
Qed.


Lemma fork_comm_step_int : forall (p q p' q' : livemodes) (s: select)(rl : redlabel), (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p))) (E_live_expr (q))) [ s ] --> [ rl ] (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p'))) (E_live_expr (q'))) ->
(exists (s' : select ), (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (q))) (E_live_expr (p))) [ s' ] --> [ rl ] (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (q'))) (E_live_expr (p')))).
Proof.
 intros.
 inversion H.
 substs.
 exists (S_Second).
 apply JO_red_forkmove2 with (s:=s0).
 assumption. 
 substs.
 exists (S_First).
 apply JO_red_forkmove1 with (s:=s0).
 assumption.
 substs.
 apply red_not_value in H4; simpl in H4; intuition.
 substs.
 apply red_not_value in H7; simpl in H7; intuition.
Qed.

Lemma fork_comm_taustep : forall (p q p' q' : livemodes), tauStep (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p))) (E_live_expr (q))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p'))) (E_live_expr (q'))) -> 
                          tauStep (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (q))) (E_live_expr (p))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (q'))) (E_live_expr (p'))).
Proof. 
intros.
 inversion H.
 substs.
 apply fork_comm_step_int in H0.
 destruct H0.
 apply tStep with (s:=x).
 assumption.
Qed.

Lemma fork_comm_taured_h : forall (x y : expr), tauRed x y -> ((fun x y => (exists (p q p' q' : livemodes), x = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr p))
         (E_live_expr q)) /\ y = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr p'))
         (E_live_expr q'))) -> (exists (p q p' q' : livemodes), x = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr p))
         (E_live_expr q)) /\ y = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr p'))
         (E_live_expr q')) /\ tauRed
  (E_apply (E_apply (E_constant CONST_fork) (E_live_expr q)) (E_live_expr p))
  (E_apply (E_apply (E_constant CONST_fork) (E_live_expr q'))     (E_live_expr p')))) x y).
Proof.
 apply star_ind.
 intros.
 destruct H; destruct H; destruct H; destruct H.
 intuition.
 substs.
 simplify_eq H1.
 intros; substs.
 exists x2 x3 x2 x3.
 splits.
 reflexivity.
 reflexivity.
 apply star_refl.
 intros.
 intuition. 
 destruct H2. destruct H2; destruct H2; destruct H2.
 intuition; substs.
 exists x0 x1 x2 x3.
 splits.
 reflexivity.
 reflexivity.
 inversion H.
 substs.
 inversion H2.
 intros.
 substs.
 assert (exists p q p' q',
     E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e'')))
       (E_live_expr (LM_expr e')) =
     E_apply (E_apply (E_constant CONST_fork) (E_live_expr p))
       (E_live_expr q) /\
     E_apply (E_apply (E_constant CONST_fork) (E_live_expr x2))
       (E_live_expr x3) =
     E_apply (E_apply (E_constant CONST_fork) (E_live_expr p'))
       (E_live_expr q') /\
     tauRed
       (E_apply (E_apply (E_constant CONST_fork) (E_live_expr q))
          (E_live_expr p))
       (E_apply (E_apply (E_constant CONST_fork) (E_live_expr q'))
          (E_live_expr p'))).
 apply H1.
 exists (LM_expr e'') (LM_expr e') x2 x3.
 splits; [reflexivity | reflexivity].
 destruct H3. destruct H3; destruct H3; destruct H3.
 intuition.
 simplify_eq H4.
 simplify_eq H3.
 intros.
 substs.
 clear H3.
 clear H4.
 apply S_star with (y:=((E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e')))
          (E_live_expr (LM_expr e''))))).
 apply tStep with (s:=S_Second).
 apply JO_red_forkmove2 with (s:=s0).
 intuition.
 assumption.
 substs.
 assert (exists p q p' q',
     E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e)))
       (E_live_expr (LM_expr e'')) =
     E_apply (E_apply (E_constant CONST_fork) (E_live_expr p))
       (E_live_expr q) /\
     E_apply (E_apply (E_constant CONST_fork) (E_live_expr x2))
       (E_live_expr x3) =
     E_apply (E_apply (E_constant CONST_fork) (E_live_expr p'))
       (E_live_expr q') /\
     tauRed
       (E_apply (E_apply (E_constant CONST_fork) (E_live_expr q))
          (E_live_expr p))
       (E_apply (E_apply (E_constant CONST_fork) (E_live_expr q'))
          (E_live_expr p'))).
 apply H1.
 exists (LM_expr e) (LM_expr e'') x2 x3.
 splits; [reflexivity | reflexivity ].
 destruct H3; destruct H3; destruct H3; destruct H3.
 intuition.
 substs.
 simplify_eq H4; simplify_eq H3; intros; substs; clear H4; clear H3.
 apply S_star with (y:=((E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e'')))
     (E_live_expr (LM_expr e))))).
 apply tStep with (s:=S_First).
 apply JO_red_forkmove1 with (s:=s0).
 assumption.
 assumption.
 substs.
 inversion H0.
 substs.
 inversion H3.
 substs.
 apply red_not_value in H5; simpl in H5; intuition.
 substs.
 inversion H0.
 substs.
 inversion H3.
 substs.
 apply red_not_value in H5; simpl in H5; intuition.
 substs.
 inversion H0.
 substs.
 apply red_not_value in H8; simpl in H8; intuition.
 substs.
 apply red_not_value in H8; simpl in H8; intuition.
 apply red_not_value in H9; simpl in H9; intuition.
Qed.

Lemma fork_comm_taured : forall (p q p' q' : livemodes), tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p))) (E_live_expr (q))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p'))) (E_live_expr (q'))) -> 
                          tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (q))) (E_live_expr (p))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (q'))) (E_live_expr (p'))).
Proof.
 intros.
 apply fork_comm_taured_h in H.
 destruct H;destruct H;destruct H;destruct H.
 intuition.
 simplify_eq H0; simplify_eq H; intros; substs; clear H0; clear H.
 assumption.
 exists p q p' q'; splits ; [reflexivity | reflexivity ].
Qed.



Lemma fork_comm_labred : forall (p q p' q' : livemodes)(l :label), labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p))) (E_live_expr (q))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p'))) (E_live_expr (q'))) -> 
                          labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (q))) (E_live_expr (p))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (q'))) (E_live_expr (p'))).
Proof.
 intros.
 inversion H.
 substs.
 intuition.
 induction p.
 induction q.
 apply fork_tau_behave_cc in H1.
 substs.
 inversion H0.
 substs.
 apply taured_val_id in H3.
 discriminate H3.
 simpl; auto.
 intros. 
 substs.
 apply taured_val_id in H3.
 discriminate H3.
 simpl; auto.
 substs.
 apply red_not_value in H7; simpl in H7; intuition.
 substs.
 apply red_not_value in H8; simpl in H8; intuition.
 substs.
  apply fork_tau_behave_ce in H1.
 substs.
 intuition.
 substs.
 inversion H0.
 substs.
 apply taured_val_id in H3. discriminate H3.
 simpl; auto.
 substs.
 apply red_not_value in H7; simpl in H7; intuition.
 substs.
 apply red_not_value in H8; simpl in H8; intuition.
 substs.
 apply red_not_value in H0; simpl in H0; intuition.
 induction q.
 apply fork_tau_behave_ec in H1.
 intuition.
 substs.
  inversion H0.
 substs.
 apply taured_val_id in H3. discriminate H3.
 simpl; auto.
 substs.
 apply red_not_value in H7; simpl in H7; intuition.
 substs.
 apply red_not_value in H8; simpl in H8; intuition.
 substs.
 apply red_not_value in H0; simpl in H0; intuition.
 assert (K:=H1).
 apply fork_tau_behave_ee in H1.
 intuition.
 destruct H2. destruct H1.
 intuition.
 substs.
 inversion H0.
 substs.
  apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr x0)))
       (E_live_expr (LM_expr x))))(e2:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr x0)))
       (E_live_expr (LM_expr e''))))(s:=S_Second).
 substs.
 splits.
 apply fork_comm_taured.
 assumption.
 apply JO_red_forkmove2 with (s:=s0).
 assumption.
 apply fork_comm_taured.
 assumption.
 substs.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr x0)))
       (E_live_expr (LM_expr x))))(e2:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e'')))
       (E_live_expr (LM_expr x))))(s:=S_First).
 substs.
 splits.
 apply fork_comm_taured.
 assumption.
 apply JO_red_forkmove1 with (s:=s0).
 assumption.
 apply fork_comm_taured.
 assumption.
 apply red_not_value in H9; simpl in H9; intuition.
 apply red_not_value in H10; simpl in H10; intuition.
 destruct H1; destruct H1.
 intuition.
 substs.
 apply red_not_value in H0; simpl in H0; intuition.
 destruct H1; destruct H1.
 intuition.
 substs.
 apply red_not_value in H0; simpl in H0; intuition.
Qed.


Lemma fork_lab_behave : forall (p q : livemodes)(e : expr)(l : label),  labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p))) (E_live_expr (q)))  e ->
 ((exists (p' q' : livemodes), e=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p'))) (E_live_expr (q'))) ) \/ 

(exists (lm : livemodes), e=(E_live_expr lm)) /\ 
(exists (p' q' : livemodes), ((exists (s : select), (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p')) ) (E_live_expr (q'))) [ s ] --> [ RL_labelled l ] e)  /\ tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p))) (E_live_expr (q))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p'))) (E_live_expr (q')))) 
    \/ (labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p)) ) (E_live_expr (q)))  (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p')) ) (E_live_expr (q'))) /\ tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p')) ) (E_live_expr (q'))) e)) ).
intros.
 inversion H.
 substs.
 intuition.
 assert (K:=H1).
 induction p; induction q.
 apply fork_tau_behave_cc in H1.
 substs.
 inversion H0.
 substs.
 apply taured_val_id in H3.
 substs.
 right.
 splits.
 exists ((LM_expr
     (E_taggingleft
        (E_pair (E_constant CONST_unit) (E_live_expr (LM_comp lab0)))))).
 reflexivity.
 exists (LM_comp l) (LM_comp lab0).
 left.
 splits.
 exists S_First.
 assumption.
 apply star_refl.
 simpl; auto.
 substs.
 apply taured_val_id in H3.
 substs.
 right.
 splits.
 exists ((LM_expr
            (E_taggingright
               (E_pair (E_live_expr (LM_comp lab)) (E_constant CONST_unit))))).
 reflexivity.
 exists (LM_comp lab) (LM_comp l).
 left.
 splits.
 exists S_Second.
 assumption.
 apply star_refl.
 simpl; auto.
 substs.
 apply red_not_value in H7; simpl in H7; intuition.
 apply red_not_value in H8; simpl in H8; intuition.
 apply fork_tau_behave_ce in H1.
 substs.
 intuition; substs.
 inversion H0.
 substs.
 apply taured_val_id in H3.
 substs.
 right.
 splits.
 exists (LM_expr
     (E_taggingleft
        (E_pair (E_constant CONST_unit) (E_live_expr (LM_expr expr5))))).
 reflexivity.
 exists (LM_comp l) (LM_expr expr5).
 left.
 splits.
 exists S_First.
 assumption.
 apply star_refl.
 simpl; auto.
 substs.
 apply red_not_value in H7; simpl in H7; auto.
 intuition.
 apply red_not_value in H8; simpl in H8; intuition.
 apply red_not_value in H0; simpl in H0; intuition.
 apply fork_tau_behave_ec in H1.
 intuition; substs.
 inversion H0.
 substs.
 apply taured_val_id in H3; substs.
 right.
 splits.
 exists (LM_expr
     (E_taggingright
        (E_pair (E_live_expr (LM_expr expr5)) (E_constant CONST_unit)))).
 reflexivity.
 exists (LM_expr expr5) (LM_comp l).
 left.
 splits.
 exists S_Second.
 assumption.
 apply star_refl.
 simpl; auto.
 substs.
 apply red_not_value in H7; simpl in H7; intuition.
 apply red_not_value in H8; simpl in H8; intuition.
 apply red_not_value in H0; simpl in H0; intuition.

 apply fork_tau_behave_ee in H1.
 intuition.
 destruct H2; destruct H1.
 intuition.
 substs.
 inversion H0.
 substs.
 assert (L:=H3).
 apply fork_tau_behave_ee in H3.
 intuition.
 destruct H4. destruct H3.
 intuition; substs.
 left.
 exists (LM_expr x1) (LM_expr x2); reflexivity.
 destruct H3. destruct H3.
 intuition; substs.
 
 
 right.
 splits.
 exists (LM_expr (E_taggingright (E_pair (E_live_expr (LM_expr x1)) x2))).
 reflexivity.
 exists ( (LM_expr e'')) (LM_expr x0).
 right.
 splits.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr x)))
         (E_live_expr (LM_expr x0))))(e2:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e'')))
       (E_live_expr (LM_expr x0))))(s:=S_First).
 splits; [ assumption | assumption | apply star_refl ].
 assumption.
  destruct H3. destruct H3.
 intuition; substs.
  right.
 splits.
  exists (LM_expr (E_taggingleft (E_pair x1 (E_live_expr (LM_expr x2))))); reflexivity.
 exists ( (LM_expr e'')) (LM_expr x0).
 right.
 splits.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr x)))
         (E_live_expr (LM_expr x0))))(e2:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e'')))
       (E_live_expr (LM_expr x0))))(s:=S_First).
 splits; [ assumption | assumption | apply star_refl ].
 assumption.
 substs.


 assert (L:=H3).
 apply fork_tau_behave_ee in H3.
 intuition.
 destruct H4. destruct H3.
 intuition; substs.
 left.
 exists (LM_expr x1) (LM_expr x2); reflexivity.
 destruct H3. destruct H3.
 intuition; substs.
 
 
 right.
 splits.
 exists (LM_expr (E_taggingright (E_pair (E_live_expr (LM_expr x1)) x2))).
 reflexivity.
 exists ( (LM_expr x)) (LM_expr e'').
 right.
 splits.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr x)))
         (E_live_expr (LM_expr x0))))(e2:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr x)))
       (E_live_expr (LM_expr e''))))(s:=S_Second).
 splits; [ assumption | assumption | apply star_refl ].
 assumption.
  destruct H3. destruct H3.
 intuition; substs.
  right.
 splits.
  exists (LM_expr (E_taggingleft (E_pair x1 (E_live_expr (LM_expr x2))))); reflexivity.
 exists ( (LM_expr x)) (LM_expr e'').
 right.
 splits.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr x)))
         (E_live_expr (LM_expr x0))))(e2:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr x)))
       (E_live_expr (LM_expr e''))))(s:=S_Second).
 splits; [ assumption | assumption | apply star_refl ].
 assumption.
 substs.
 apply red_not_value in H9; simpl in H9; intuition.
 apply red_not_value in H10; simpl in H10; intuition.
 destruct H1; destruct H1; intuition; substs; apply red_not_value in H0; simpl in H0; intuition.
 destruct H1; destruct H1; intuition; substs; apply red_not_value in H0; simpl in H0; intuition.
Qed.

 



Lemma fork_comm_step_fin : forall (p q lm : livemodes) (s: select)(rl : redlabel), (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p))) (E_live_expr (q))) [ s ] --> [ rl ] (E_live_expr lm )->
(exists (s' : select ) (lm' : livemodes), (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (q))) (E_live_expr (p))) [ s' ] --> [ rl ] (E_live_expr lm') /\ totalTauRed ((E_live_expr lm') >>= swapf) (E_live_expr lm ) ).
Proof.
 intros.
 inversion H.
 substs.
 exists S_Second.
 exists (LM_expr (E_taggingright (E_pair  (E_live_expr q) v))).
 splits.
 apply JO_red_forkdeath2.
 assumption.
 apply swapf_right_b.
 simpl; auto.
 assumption.
 subst.
 exists (S_First)  (LM_expr (E_taggingleft (E_pair v' (E_live_expr p) ))).
 splits. 
 apply JO_red_forkdeath1.
 assumption.
 apply swapf_left_b.
 assumption.
 simpl; auto.
 substs.
 exists S_Second.
 exists (LM_expr (E_taggingright (E_pair  (E_live_expr q) (E_constant CONST_unit)))).
 splits.
 apply JO_red_forkdocomp2.
 apply swapf_right_b.
 simpl; auto.
 simpl; auto.
 subst.
 exists (S_First)  (LM_expr (E_taggingleft (E_pair (E_constant CONST_unit) (E_live_expr p) ))).
 splits. 
 apply JO_red_forkdocomp1.
 apply swapf_left_b.
 simpl; auto.
 simpl; auto.
Qed.


Lemma fork_comm_tau_fin_h : forall (x y : expr), tauRed x y ->  ((fun x y => (exists ( p q lm : livemodes ), x = ((E_apply(E_apply (E_constant CONST_fork) (E_live_expr (p))) (E_live_expr (q)))) /\ y = (E_live_expr lm) ) ->
               (exists ( p q lm lm': livemodes ), x = ((E_apply(E_apply (E_constant CONST_fork) (E_live_expr (p))) (E_live_expr (q)))) /\ y = (E_live_expr lm) /\ tauRed (((E_apply(E_apply (E_constant CONST_fork) (E_live_expr (q))) (E_live_expr (p)))) >>= swapf) (E_live_expr lm) /\  tauRed (((E_apply(E_apply (E_constant CONST_fork) (E_live_expr (q))) (E_live_expr (p))))) (E_live_expr lm') /\ totalTauRed ((E_live_expr lm') >>= swapf) ((E_live_expr lm)))) x y).
Proof.
 apply star_ind.
 intros.
 destruct H; destruct H; destruct H.
 intuition.
 rewrite -> H1 in H0.
 discriminate H0.
 intros.
 destruct H2; destruct H2; destruct H2.
 intuition.
 substs.
 
 inversion H.
 substs.
 inversion H2.
 substs.
 
 assert (exists p q lm lm',
     E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e'')))
       (E_live_expr (LM_expr e')) =
     E_apply (E_apply (E_constant CONST_fork) (E_live_expr p))
       (E_live_expr q) /\
     E_live_expr x2 = E_live_expr lm /\
     tauRed
       (E_apply (E_apply (E_constant CONST_fork) (E_live_expr q))
          (E_live_expr p) >>= swapf) (E_live_expr lm) /\
     tauRed
       (E_apply (E_apply (E_constant CONST_fork) (E_live_expr q))
          (E_live_expr p)) (E_live_expr lm') /\
     totalTauRed (E_live_expr lm' >>= swapf) (E_live_expr lm)).



 apply H1.
 exists (LM_expr e'') (LM_expr e') x2; splits; [reflexivity | reflexivity ].
 destruct H3; destruct H3; destruct H3; destruct H3; intuition.
  simplify_eq H4; simplify_eq H3; intros; substs; clear H3; clear H4.
 exists (LM_expr e) (LM_expr e') x1 x3.
   splits.
 reflexivity.
 reflexivity.

 apply S_star with (y:=((E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e')))
          (E_live_expr (LM_expr e''))) >>= swapf )).
 apply tStep with (s:=S_Second).
 apply JO_red_evalbind.
 apply JO_red_forkmove2 with (s:=s0).
 assumption.
 assumption.
 apply S_star with (y:=((E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e')))
          (E_live_expr (LM_expr e''))))).
 apply tStep with (s:=S_Second).
 apply JO_red_forkmove2 with (s:=s0).
 assumption.
 assumption.
 assumption.
 substs.

 assert ( exists p q lm lm',
     E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e)))
       (E_live_expr (LM_expr e'')) =
     E_apply (E_apply (E_constant CONST_fork) (E_live_expr p))
       (E_live_expr q) /\
     E_live_expr x2 = E_live_expr lm /\
     tauRed
       (E_apply (E_apply (E_constant CONST_fork) (E_live_expr q))
          (E_live_expr p) >>= swapf) (E_live_expr lm) /\
     tauRed
       (E_apply (E_apply (E_constant CONST_fork) (E_live_expr q))
          (E_live_expr p)) (E_live_expr lm') /\
     totalTauRed (E_live_expr lm' >>= swapf) (E_live_expr lm)).
 apply H1.
 exists (LM_expr e) (LM_expr e'') x2.
 splits; [reflexivity | reflexivity].
 destruct H3; destruct H3; destruct H3; destruct H3; intuition.
 simplify_eq H4; simplify_eq H3; intros; substs.
 clear H3; clear H4.
 exists (LM_expr e) (LM_expr e') x1 x3.
   splits.
 reflexivity.
 reflexivity.
 apply S_star with (y:=((E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e'')))
          (E_live_expr (LM_expr e))) >>= swapf )).
 apply tStep with (s:=S_First).
 apply JO_red_evalbind.
 apply JO_red_forkmove1 with (s:=s0).
 assumption.
 assumption.
 apply S_star with (y:=((E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e'')))
          (E_live_expr (LM_expr e))))).
 apply tStep with (s:=S_First).
 apply JO_red_forkmove1 with (s:=s0).
 assumption.
 assumption.
 assumption.
 substs.
 apply taured_val_id in H0.
 apply fork_comm_step_fin in H2.
 destruct H2.
 destruct H2; intuition.
 
 exists (LM_expr v) x1 x2 x0.
 splits.
 reflexivity.
 reflexivity.
 apply S_star with (y:=((E_live_expr x0) >>= swapf)).
 apply tStep with (s:=x).
 apply JO_red_evalbind with (s:=x).
 assumption.
 apply tau_incl_totalTau.
 simplify_eq H0; clear H0; intros; substs.
 assumption.
 apply S_star with (y:=((E_live_expr x0))).
 apply tStep with (s:=x).
 assumption.
 apply star_refl.
 substs.
  simplify_eq H0; clear H0; intros; substs.
 assumption.
 simpl; auto.
 substs.

 apply taured_val_id in H0.
 apply fork_comm_step_fin in H2.
 destruct H2.
 destruct H2; intuition.
 
  exists x0 (LM_expr v') x2 x1.
 splits.
 reflexivity.
 reflexivity.
 apply S_star with (y:=((E_live_expr x1) >>= swapf)).
 apply tStep with (s:=x).
 apply JO_red_evalbind with (s:=x).
 assumption.
 apply tau_incl_totalTau.
 simplify_eq H0; intros; substs.
 assumption.
 apply S_star with (y:=((E_live_expr x1))).
 apply tStep with (s:=x).
 assumption.
 apply star_refl.
 simplify_eq H0; intros; substs.
 assumption.
 simpl; auto.
 substs.

 apply taured_val_id in H0.
 apply red_not_value in H8; simpl in H8; intuition.
 apply red_not_value in H8; simpl in H8; intuition.
 apply red_not_value in H9; simpl in H9; intuition.
Qed.

               
Lemma fork_comm_tau_fin : forall ( p q lm : livemodes ), tauRed ((E_apply(E_apply (E_constant CONST_fork) (E_live_expr (p))) (E_live_expr (q)))) (E_live_expr lm) -> 
                                                          tauRed (((E_apply (E_apply (E_constant CONST_fork) (E_live_expr (q))) (E_live_expr (p)))) >>= swapf) (E_live_expr lm) /\
                                                          (exists (lm' : livemodes), tauRed (((E_apply (E_apply (E_constant CONST_fork) (E_live_expr (q))) (E_live_expr (p))))) (E_live_expr lm') /\ totalTauRed ((E_live_expr lm')>>= swapf)(E_live_expr lm) ).
Proof.
 intros.
 apply fork_comm_tau_fin_h in H.
 destruct H; destruct H; destruct H; destruct H.
 intuition.
 simplify_eq H0; simplify_eq H; intros; substs; clear H0; clear H.
 assumption.
 exists x2.
  simplify_eq H0; simplify_eq H; intros; substs; clear H0; clear H.
 splits.
 assumption.
 assumption.
 exists p q lm; splits; [ reflexivity | reflexivity ].
Qed.

Lemma bind_tau_behave_back_h : forall (x y : expr), tauRed x y -> ((fun x y => (exists (e e' : expr), x = (e >>= e') ) -> (exists (e e' : expr), x = (e >>= e') /\ ((exists (f : expr), tauRed e f /\ y = (f >>= e')) \/ (exists (f : expr), tauRed e (E_live_expr (LM_expr f)) /\ ((exists (f' : expr ), (tauRed f f' /\ y=(((E_live_expr (LM_expr f')))>>=e') ) \/ (tauRed f f' /\ is_value_of_expr f' /\ tauRed (E_apply e' f') y))))) )   ) x y). 
Proof.
 apply star_ind.
 intros.
 destruct H; destruct H.
 substs.
 exists x0 x1.
 splits.
 reflexivity.
 left.
 exists x0.
 splits.
 apply star_refl.
 reflexivity.
 intros.
 destruct H2; destruct H2; substs.
 exists x0 x1.
 splits.
 reflexivity.
 inversion H.
 substs.
 inversion H2.
 substs.
 assert (  exists e e'0,
     e' >>= x1 = e >>= e'0 /\
     ((exists f, tauRed e f /\ z = f >>= e'0) \/
      (exists f,
       tauRed e (E_live_expr (LM_expr f)) /\
       (exists f',
        tauRed f f' /\ z = E_live_expr (LM_expr f') >>= e'0 \/
        tauRed f f' /\ is_value_of_expr f' /\ tauRed (E_apply e'0 f') z)))).
 apply H1.
 exists e' x1.
 reflexivity.
 destruct H3; destruct H3.
 intuition.
 simplify_eq H4; clear H4; intros; substs.
 destruct H3.
 intuition.
 substs.
 left.
 exists x1.
 splits.
 apply S_star with (y:=x).
 apply tStep with (s:=s).
 assumption.
 assumption.
 reflexivity.
 simplify_eq H4; clear H4; intros; substs.
 right.
 destruct H3.
 exists x1.
 splits.
 apply S_star with (y:=x).
 apply tStep with (s:=s).
 assumption.
 intuition.
 intuition.
 substs.
 assert ( exists e e'0,
     E_live_expr (LM_expr e') >>= x1 = e >>= e'0 /\
     ((exists f, tauRed e f /\ z = f >>= e'0) \/
      (exists f,
       tauRed e (E_live_expr (LM_expr f)) /\
       (exists f',
        tauRed f f' /\ z = E_live_expr (LM_expr f') >>= e'0 \/
        tauRed f f' /\ is_value_of_expr f' /\ tauRed (E_apply e'0 f') z)))).
 apply H1.
 exists (E_live_expr (LM_expr e')) (x1).
 reflexivity.
 destruct H3; destruct H3.
 intuition.
 substs.
 simplify_eq H4; clear H4; intros; substs.
 destruct H3; elim H3; intros.
 simplify_eq H5; clear H5; intros; substs.
 apply taured_val_id in H4.
 substs.
 right.
 exists e.
 splits.
 apply star_refl.
 
 exists e'.
 left.
 splits.
 apply S_star with (y:=e').
 apply tStep with (s:=s).
 assumption.
 apply star_refl.
 apply reflexivity.
 simpl; auto.
 simplify_eq H4; clear H4; intros; substs.
 destruct H3.
 elim H3.
 intros.
 apply taured_val_id in H4.
 simplify_eq H4; clear H4; intros; substs.
 destruct H5.
 destruct H4.
 clear H3.
 intuition.
 substs.
 right.
 exists e.
 splits.
 apply star_refl.
 exists x1.
 left.
 splits.
 apply S_star with (y:=x).
 apply tStep with (s:=s).
 assumption.
 assumption.
 apply reflexivity.
 clear H3.
 intuition.
 right.
 exists e.
 splits.
 apply star_refl.
 exists x1.
 right.
 splits.
 apply S_star with (y:=x).
 apply tStep with (s:=s).
 assumption.
 assumption.
 assumption.
 assumption.
 simpl; auto.
 substs.
 right.
 exists v.
 splits.
 apply star_refl.
 exists v.
 right.
 splits.
 apply star_refl.
 assumption.
 assumption.
Qed.



Lemma fork_swap_tau_behave : forall (e : expr )( p q : livemodes ), tauRed (E_bind (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p))) (E_live_expr (q))) (swapf)) e ->
                                 ((exists (p' q' : livemodes), e = (E_bind (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p'))) (E_live_expr (q'))) (swapf)) /\ tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p))) (E_live_expr (q)))  (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p'))) (E_live_expr (q'))) ) \/ 
                                 ((exists (lm : livemodes),  tauRed ( (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p))) (E_live_expr (q)))) (E_live_expr lm) /\ totalTauRed ((E_live_expr lm) >>= swapf) e)) ).
Proof.
 intros.
 assert (H0:=H).
 apply bind_tau_behave_back_h in H0. 
 destruct H0.
 destruct H0.
 intuition.
 simplify_eq H1; clear H1; intros; substs.
 destruct H0.
 intuition.
 assert (K:=H1).
 simplify_eq H2; clear H2; intros; substs.
 induction p; induction q.
 apply fork_tau_behave_cc in H1.
 substs.
 left.
 exists (LM_comp lab) (LM_comp lab0).
 splits; [reflexivity | apply star_refl].
 apply fork_tau_behave_ce in H1.
 intuition.
 substs.
 left.
 exists (LM_comp lab) (LM_expr expr5).
 splits; [reflexivity | apply star_refl].
 substs.
 right.
 exists (LM_expr (E_taggingright (E_pair (E_live_expr (LM_comp lab)) expr5))).
 splits.
 assumption.
 apply star_refl.
 apply fork_tau_behave_ec in H1.
 intuition.
 substs.
 left.
 exists (LM_expr expr5) (LM_comp lab).
 splits; [reflexivity | apply star_refl].
 substs.
 right.
 exists (LM_expr (E_taggingleft (E_pair expr5 (E_live_expr (LM_comp lab))))).
 splits.
 assumption. 
 apply star_refl.
 assert (L:=H1).
 apply fork_tau_behave_ee in H1.
 intuition.
 destruct H0; destruct H0; intuition; substs.
 left.
 exists (LM_expr x0) (LM_expr x1).
 splits; [reflexivity | assumption].
 destruct H1; destruct H0; intuition; substs.
 right.
 exists ((LM_expr (E_taggingright (E_pair (E_live_expr (LM_expr x0)) x1)))).
 splits.
 assumption.
 apply star_refl.
 destruct H1; destruct H0; intuition; substs.
 right.
 exists (LM_expr (E_taggingleft (E_pair x0 (E_live_expr (LM_expr x1))))).
 splits.
 assumption.
 apply star_refl.
 destruct H0.  intuition; substs.
 destruct H3.
 intuition.
 substs.
 simplify_eq H1. clear H1; intros; substs.
 assert (L:=H).
 right.
 apply taured_val_id in H0.
 substs.
 exists (LM_expr x2).
 splits.
 assumption.
 apply star_refl.
 induction p.
 induction q.
 apply fork_tau_behave_cc in H2.
 discriminate H2.
 apply fork_tau_behave_ce in H2.
 intuition.
 discriminate H1.
 simplify_eq H2; intros; substs; simpl; auto.
 induction q.
  apply fork_tau_behave_ec in H2.
 intuition.
 discriminate H1.
 simplify_eq H2; intros; substs; auto.
 simpl; auto.
 apply fork_tau_behave_ee in H2.
 intuition.
 destruct H1; destruct H1; intuition.
 discriminate H4.
 destruct H2; destruct H1; intuition.
 simplify_eq H5; intros; substs; simpl; auto.
 destruct H2; destruct H1; intuition.
 simplify_eq H5; intros; substs; simpl; auto.
 simplify_eq H1; intros; substs; simpl; auto.
 
 right.
 exists (LM_expr x2).
 clear H1.
 assert (L:=H2).
 induction p.
 induction q.
 
 apply fork_tau_behave_cc in H2.
 discriminate H2.
 apply fork_tau_behave_ce in H2.
 intuition.
 discriminate H1.
 simplify_eq H1; intros; substs; simpl; auto.
 apply taured_val_id in H0.
 substs.
 assumption.
 simplify_eq H2; intros; substs.
 simpl; auto.
 simplify_eq H2; intros; substs.
 apply taured_val_id in H0.
 substs.
 assert ((totalTauRed
       (E_apply swapf
          (E_taggingright (E_pair (E_live_expr (LM_comp lab)) expr5))) (E_live_expr
     (LM_expr (E_taggingleft (E_pair expr5 (E_live_expr (LM_comp lab)) ))))) /\ tauRed
       (E_apply swapf
          (E_taggingright (E_pair (E_live_expr (LM_comp lab)) expr5))) e).
 splits.
 apply swapf_right.
 simpl; auto.
 assumption.
 assumption.
 apply ttau_prefix in H0.
 intuition.
 apply S_star with (y:=(E_apply swapf
          (E_taggingright (E_pair (E_live_expr (LM_comp lab)) expr5)))).
 apply JO_red_dobind_td.
 apply S_First.
 simpl; auto.
 assumption.
 apply taured_val_id in H1.
 substs.
 apply swapf_right_b.
 simpl; auto.
 assumption.
 simpl; auto.
 simpl; auto.
 induction q.
  apply fork_tau_behave_ec in H2.
 intuition.
 discriminate H1.
 simplify_eq H1; intros; substs; auto.
 simplify_eq H2; intros; substs; auto.
 apply taured_val_id in H0.
 substs.
 assumption.
 simpl; auto.
 simplify_eq H2; intros; substs.
 apply taured_val_id in H0.
 substs.
 assert ((totalTauRed
       (E_apply swapf
          (E_taggingleft (E_pair expr5 (E_live_expr (LM_comp lab))))) (E_live_expr
     (LM_expr (E_taggingright (E_pair  (E_live_expr (LM_comp lab)) expr5 ))))) /\ tauRed
       (E_apply swapf
          (E_taggingleft (E_pair expr5 (E_live_expr (LM_comp lab))))) e).
 splits.
 apply swapf_left.
 simpl; auto.
 simpl; auto.
 assumption.
 apply ttau_prefix in H0.
 intuition.
 apply S_star with (y:=(E_apply swapf
          (E_taggingleft (E_pair expr5 (E_live_expr (LM_comp lab)))))).
 apply JO_red_dobind_td.
 apply S_First.
 simpl; auto.
 assumption.
 apply taured_val_id in H1. 
 substs.
 apply swapf_left_b.
 assumption.
 simpl; auto.
 simpl; auto.
 simpl; auto.
 apply fork_tau_behave_ee in H2.
 destruct H2.
  destruct H1; destruct H1.
 elim H1.
 intros.
 elim H4.
 intros.
 discriminate H7.
intuition.
 destruct H2; destruct H1; intuition.
 simplify_eq H7; intros; substs.
 apply taured_val_id in H0.
 substs.
 assumption.
 simpl; auto.
 destruct H2; destruct H1; intuition.
 simplify_eq H7; intros; substs.
 apply taured_val_id in H0.
 substs.
 assert ((totalTauRed
       (E_apply swapf (E_taggingright (E_pair (E_live_expr (LM_expr x)) x0))) (E_live_expr
     (LM_expr (E_taggingleft (E_pair x0 (E_live_expr  (LM_expr x))  ))))) /\ tauRed
       (E_apply swapf (E_taggingright (E_pair (E_live_expr (LM_expr x)) x0)))
       e).
 splits.
 apply swapf_right.
 simpl; auto.
 simpl; auto.
 assumption.
 apply ttau_prefix in H0.
 intuition.
 apply S_star with (y:=(E_apply swapf (E_taggingright (E_pair (E_live_expr (LM_expr x)) x0)))).
 apply JO_red_dobind_td.
 apply S_First.
 simpl; auto.
 assumption.
 apply taured_val_id in H6; substs.
 apply swapf_right_b.
 simpl; auto.
 simpl; auto.
 simpl; auto.
 simpl; auto.
 

 destruct H2; destruct H1; intuition.
 simplify_eq H7; intros; substs.
 apply taured_val_id in H0.
 substs.
 assumption.
 simpl; auto.
 destruct H2; destruct H1; intuition.
 simplify_eq H7; intros; substs.
 apply taured_val_id in H0.
 substs.
 assert ((totalTauRed
       (E_apply swapf (E_taggingleft (E_pair x (E_live_expr (LM_expr x0)) ))) (E_live_expr
     (LM_expr (E_taggingright (E_pair  (E_live_expr  (LM_expr x0)) x  ))))) /\ tauRed
       (E_apply swapf (E_taggingleft (E_pair x (E_live_expr (LM_expr x0)) )))
       e).
 splits.
 apply swapf_left.
 simpl; auto.
 simpl; auto.
 assumption.
 apply ttau_prefix in H0.
 intuition.
 apply S_star with (y:=(E_apply swapf (E_taggingleft (E_pair x (E_live_expr (LM_expr x0)) )))).
 apply JO_red_dobind_td.
 apply S_First.
 simpl; auto.
 assumption.
 apply taured_val_id in H6; substs.
 apply swapf_left_b.
 simpl; auto.
 simpl; auto.
 simpl; auto.
 simpl; auto.

 exists (E_apply (E_apply (E_constant CONST_fork) (E_live_expr p)) (E_live_expr q)) (swapf).
 reflexivity.
Qed.


Lemma fork_swap_lab_behave : forall (e : expr )( p q : livemodes )(l : label), labRed l (E_bind (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p))) (E_live_expr (q))) (swapf)) e ->
                                 ((exists (p' q' : livemodes), e = (E_bind (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p'))) (E_live_expr (q'))) (swapf)) /\ labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p))) (E_live_expr (q)))  (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p'))) (E_live_expr (q'))) ) \/ 
                                 ((exists (lm : livemodes),  labRed l ( (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p))) (E_live_expr (q)))) (E_live_expr lm) /\ totalTauRed ((E_live_expr lm) >>= swapf) e)) ).
Proof.
 intros.
 inversion H.
 intuition; substs. 
 assert (L:=H4).
 apply fork_swap_tau_behave in H4.
 intuition.
 destruct H1; destruct H1.
 intuition; substs.
 inversion H0.
 substs.
 inversion H8.
 substs.
 assert (K:=H6).
 apply fork_swap_tau_behave in H6.
 intuition.
 left.
 destruct H1; destruct H1.
 intuition; substs.
 exists x x0.
 splits.
 reflexivity.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e0)))
          (E_live_expr (LM_expr e'0))))(e2:= E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e'')))
       (E_live_expr (LM_expr e'0)))(s:=S_First).
 splits; [assumption | assumption | assumption ].
 destruct H1.
 right.
 exists x.
 splits.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e0)))
       (E_live_expr (LM_expr e'0))))(e2:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e'')))
       (E_live_expr (LM_expr e'0))))(s:=S_First). splits.
 assumption.
 assumption.
 intuition.
 intuition.
 substs. 

  apply fork_swap_tau_behave in H6.
 intuition.
 left.
 destruct H1; destruct H1.
 intuition; substs.
 exists x x0.
 splits.
 reflexivity.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e0)))
       (E_live_expr (LM_expr e'0))))(e2:= ( E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e0)))
       (E_live_expr (LM_expr e''))))(s:=S_Second).
 splits; [assumption | assumption | assumption ].
 destruct H1.
 right.
 exists x.
 splits.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e0)))
       (E_live_expr (LM_expr e'0))))(e2:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e0)))
       (E_live_expr (LM_expr e''))))(s:=S_Second). splits.
 assumption.
 assumption.
 intuition.
 intuition.
 substs.

 right.
 exists  (LM_expr
          (
             (E_taggingleft
                (E_pair (E_constant CONST_unit) (E_live_expr (x0)))))).
 splits.
 apply lab_r with (e1:=( E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_comp l)))
       (E_live_expr (x0))))(e2:=(E_live_expr
       (LM_expr
          (E_taggingleft
             (
                (E_pair (E_constant CONST_unit) (E_live_expr (x0))))))))(s:=(S_First)).
 splits.
 assumption.
 assumption.
 apply star_refl.
 assert ((totalTauRed (E_live_expr
          (LM_expr
             (E_taggingleft
                (
                   (E_pair (E_constant CONST_unit) (E_live_expr (x0)))))) >>=
        swapf) (E_live_expr
          (LM_expr
             (
                (E_taggingright
                   (E_pair  (E_live_expr (x0)) (E_constant CONST_unit))))) )) /\ (tauRed
       (E_live_expr
          (LM_expr
             (E_taggingleft
                (
                   (E_pair (E_constant CONST_unit) (E_live_expr (x0)))))) >>=
        swapf) e)).
 splits.
 apply swapf_left_b.
 simpl; auto.
 simpl; auto.
 assumption.
 apply ttau_prefix in H1.
 intuition.
 apply taured_val_id in H2.
 substs.
 apply swapf_left_b.
 simpl; auto.
 simpl; auto.
 simpl; auto.
 substs.
 right.
 exists ((LM_expr
          (E_taggingright
             (E_pair (E_live_expr (x)) (E_constant CONST_unit))))).
 splits.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (x)))
       (E_live_expr (LM_comp l))))(e2:=( E_live_expr
       (LM_expr
          (E_taggingright
             (E_pair (E_live_expr (x)) (E_constant CONST_unit))))))(s:=S_Second). splits.
 assumption.
 assumption.
 apply star_refl.
 assert ((totalTauRed
       (E_live_expr
          (LM_expr
             (E_taggingright
                (E_pair (E_live_expr (x)) (E_constant CONST_unit)))) >>=
        swapf) (E_live_expr
          (LM_expr
            (E_taggingleft
             (
                (E_pair  (E_constant CONST_unit) (E_live_expr (x)))))) )) /\ (tauRed
       (E_live_expr
          (LM_expr
             (E_taggingright
                (E_pair (E_live_expr (x)) (E_constant CONST_unit)))) >>=
        swapf) e)).
 splits.
 apply swapf_right_b.
 simpl; auto.
 simpl; auto.
 assumption.
 apply ttau_prefix in H1.
 intuition.
 apply taured_val_id in H2; substs.
 apply swapf_right_b.
 simpl; auto.
 simpl; auto.
 simpl; auto.
 substs.
 apply red_not_value in H9; simpl in H9; intuition.
 apply red_not_value in H10; simpl in H10; intuition.
 destruct H1; intuition.
 induction p; induction q.
 apply fork_tau_behave_cc in H2; discriminate H2.
  apply fork_tau_behave_ce in H2.
 intuition.
  discriminate H1.
 simplify_eq H2; intros; substs.
 assert (totalTauRed
       (E_live_expr
          (LM_expr
             (E_taggingright (E_pair (E_live_expr (LM_comp lab)) expr5))) >>=
        swapf) (E_live_expr
          (LM_expr
             (E_taggingleft (E_pair expr5 (E_live_expr (LM_comp lab))))) )).
 apply swapf_right_b.
 simpl; auto.
 assumption.
 apply ttau_midpoint  with (e':=(E_live_expr
          (LM_expr (E_taggingleft (E_pair expr5 (E_live_expr (LM_comp lab))))))) in H3.
 intuition.
 inversion H5.
 substs.
 apply red_not_value in H0; simpl in H0; intuition.
 substs.
 inversion H3.
 intuition.
 apply H8 in H0.
 intuition.
 apply tau_incl_totalTau in H5.
 apply taured_val_id in H5.
 substs.
 apply red_not_value in H0; simpl in H0; intuition.
 simpl; auto.
 apply swapf_right_b.
 simpl; auto.
 simpl; auto.
 apply fork_tau_behave_ec in H2.
 intuition.
  discriminate H1.
 simplify_eq H2; clear H2; intros; substs.
 assert (totalTauRed
       (E_live_expr
          (LM_expr
             (E_taggingleft (E_pair expr5 (E_live_expr (LM_comp lab)) ))) >>=
        swapf) (E_live_expr
          (LM_expr
             (E_taggingright (E_pair (E_live_expr (LM_comp lab)) expr5))) )).
 apply swapf_left_b.
 simpl; auto.
 simpl; auto.
 apply ttau_midpoint  with (e':=(E_live_expr
          (LM_expr (E_taggingright (E_pair (E_live_expr (LM_comp lab)) expr5))))) in H3.
 intuition.
 inversion H2.
 substs.
 apply red_not_value in H0; simpl in H0; intuition.
 substs.
 inversion H3.
 intuition.
 apply H7 in H0.
 intuition.
 apply tau_incl_totalTau in H2.
 apply taured_val_id in H2.
 substs.
 apply red_not_value in H0; simpl in H0; intuition.
 simpl; auto.
 apply swapf_left_b.
 simpl; auto.
 simpl; auto.

  apply fork_tau_behave_ee in H2.
 intuition.
 destruct H1.
 destruct H1.
 intuition.
 discriminate H5.
 destruct H2; destruct H1; intuition.
 simplify_eq H7; clear H7; intros; substs.
 assert ((totalTauRed
        (E_live_expr
          (LM_expr (E_taggingright (E_pair (E_live_expr (LM_expr x0)) x1))) >>=
        swapf) (E_live_expr
          (LM_expr
             (E_taggingleft
                (
                   (E_pair x1 (E_live_expr (LM_expr x0)))))))) /\ (tauRed
       (E_live_expr
          (LM_expr (E_taggingright (E_pair (E_live_expr (LM_expr x0)) x1))) >>=
        swapf) e1)).
 splits.
 apply swapf_right_b.
 simpl; auto.
 assumption.
 apply tau_incl_totalTau.
 assumption.
 apply ttau_prefix in H5.
 intuition.
 inversion H8.
 substs.
 inversion H0.
 substs.
 inversion H7.
 substs.
 intuition.
 apply H10 in H0.
 intuition.
 apply taured_val_id in H7.
 substs.
 inversion H0.
 simpl; auto.

 destruct H2; destruct H1; intuition.
 simplify_eq H7; clear H7; intros; substs.
 assert ((totalTauRed
        (E_live_expr
          (LM_expr
             (E_taggingleft
                ( (E_pair x0 (E_live_expr (LM_expr x1)))))) >>=
        swapf) (E_live_expr
          (LM_expr
             (
                (E_taggingright (E_pair (E_live_expr (LM_expr x1)) x0 )))))) /\ (tauRed
       (E_live_expr
          (LM_expr
             (E_taggingleft
                ( (E_pair x0 (E_live_expr (LM_expr x1)))))) >>=
        swapf) e1)).
 splits.
 apply swapf_left_b.
 simpl; auto.
 simpl; auto.
 apply tau_incl_totalTau.
 assumption.
 apply ttau_prefix in H5.
 intuition.
 inversion H8.
 substs.
 apply red_not_value in H0; simpl in H0; intuition.
 substs.
 inversion H7.
 intuition.
 apply H10 in H0.
 intuition.
 apply taured_val_id in H7.
 substs.
 apply red_not_value in H0; simpl in H0; intuition.
 simpl; auto.
Qed.


Lemma ttr_val_not_labred : forall (e v e' : expr)(l:label), totalTauRed e v /\ is_value_of_expr v -> (~ (labRed l e e')).
Proof.
 intros.
 intuition.
 inversion H0.
 intuition.
 assert (totalTauRed e v /\ tauRed e e1).
 auto.
 apply ttau_prefix in H7.
 intuition.
 inversion H10.
 substs.
 apply red_not_value in H; contradiction.
 substs.
 inversion H9.
 intuition.
 apply H3 in H.
 auto.
 substs.
 inversion H9.
 substs.
 apply red_not_value in H; contradiction.
 substs.
 inversion H3.
 apply red_not_value in H5; contradiction.
Qed.

Lemma fork_comm_taured_ee_laststep_h : forall (x y : expr), tauRed x y -> ((fun x y => 
   ( exists ( e e' : expr) (lm : livemodes),  
       x = (E_apply
         (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e')))
         (E_live_expr (LM_expr e))) /\
       y = (E_live_expr  lm)) -> 
( exists (e e' : expr) (lm : livemodes), 
       x = (E_apply
         (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e')))
         (E_live_expr (LM_expr e))) /\ 
       y = (E_live_expr  lm) /\
       (exists (p q : expr), tauRed x (E_apply
         (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr q)))
         (E_live_expr (LM_expr p))) /\ tauStep (E_apply
         (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr q)))
         (E_live_expr (LM_expr p))) (E_live_expr  lm) )))x y ).
Proof.
 apply star_ind.
 intros.
 destruct H; destruct H; destruct H; destruct H; intuition; substs.
 discriminate H0.
 intros.
 destruct H2; destruct H2; destruct H2; destruct H2; intuition; substs.
 exists x0 x1 x2.
 splits.
 reflexivity.
 reflexivity.
 assert  (tauRed
      (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr x1)))
         (E_live_expr (LM_expr x0))) y).
 apply S_star with (y:=y).
 assumption.
 apply star_refl.
 apply fork_tau_behave_ee in H2.
 intuition.
 destruct H3. destruct H2.
 intuition. 
 substs.
 assert (exists e e' lm,
     E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr x)))
       (E_live_expr (LM_expr x3)) =
     E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr e')))
       (E_live_expr (LM_expr e)) /\
     E_live_expr x2 = E_live_expr lm /\
     (exists p q,
      tauRed
        (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr x)))
           (E_live_expr (LM_expr x3)))
        (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr q)))
           (E_live_expr (LM_expr p))) /\
      tauStep
        (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr q)))
           (E_live_expr (LM_expr p))) (E_live_expr lm))).
 apply H1.
 exists x3 x x2.
 splits.
 reflexivity.
 reflexivity.
 destruct H4. destruct H4. destruct H4. intuition.
 simplify_eq H5; simplify_eq H4; clear H5; clear H4; intros; substs.
 destruct H7. destruct H4. intuition.
 exists x x2.
 splits.
 apply S_star with  (y:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr x5)))
          (E_live_expr (LM_expr x4)))).
 assumption.
 assumption.
 assumption.
 exists x0 x1.
 destruct H2. destruct H2.
 intuition.
 substs.
 apply star_refl.
 substs.
 apply taured_val_id in H0.
 simplify_eq H0; clear H0; intros; substs.
 assumption.
 simpl; auto.
 exists x0 x1.

 destruct H2. destruct H2.
 intuition.
 substs.
 apply star_refl.
 substs.
 apply taured_val_id in H0.
 simplify_eq H0; clear H0; intros; substs.
 assumption.
 simpl; auto.
Qed.


Inductive fork_comm_rel :  relation expr := 
 | forkee_start : forall (e e' : livemodes), fork_comm_rel (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (e))) (E_live_expr (e'))) (E_bind (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (e'))) (E_live_expr (e))) (swapf))
 | forkee_tau : forall  ( lm lm' : livemodes) (e : expr),  totalTauRed (E_bind ((E_live_expr lm')) (swapf)) (E_live_expr lm) /\  totalTauRed (E_bind ((E_live_expr lm')) (swapf)) e  -> fork_comm_rel (E_live_expr lm) e.


Theorem fork_comm_wbsm : forall (p q : expr), fork_comm_rel p q -> ((forall (l : label) (p' : expr), labRed l p p' -> (exists (q' : expr), labRed l q q' /\ fork_comm_rel p' q') ) /\ (forall (l : label) (q' : expr), labRed l q q' -> (exists (p' : expr), labRed l p p' /\ fork_comm_rel p' q') )).
Proof. 
 intros.
 splits.
 induction H.
 intros.
 substs.
 assert (L := H).
 apply fork_lab_behave in H.
 destruct H.
 destruct H; destruct H.
 substs.
 assert (H0 := L).
 apply fork_comm_labred in H0.
 exists ((E_apply (E_apply (E_constant CONST_fork) (E_live_expr x0))
          (E_live_expr x)) >>= swapf).
 splits.
 apply bind_lab_behave_front.
 assumption.
 apply forkee_start.
 intuition.
 destruct H0.
 substs.
 destruct H1.
 destruct H.
 destruct H.
 destruct H.
 destruct H.
 assert (M:=H).
 apply fork_comm_step_fin in H.
 exists (E_live_expr x).
 splits.
 destruct H.
 destruct H.
 apply lab_r with (e1:= ((E_apply (E_apply (E_constant CONST_fork) (E_live_expr x1))
      (E_live_expr x0)) >>= swapf))(e2:= ((E_live_expr x4) >>= swapf))(s:=x3).
 splits.
 assert (N:=H0).
 apply fork_comm_taured in H0.
 apply bind_tau_behave_front.
 assumption.
 apply JO_red_evalbind.
 intuition.
 elim H; intros.
 apply tau_incl_totalTau in H2.
 assumption.
 apply fork_comm_taured in H0.
 destruct H; destruct H; intuition.
 apply forkee_tau with (lm':=x4).
 splits.
 assumption.
 assumption.
 intuition.
 apply fork_comm_tau_fin in H1.
 intuition.
 destruct H2.
 exists ( (E_live_expr x2) >>= swapf).
 splits.
 apply fork_comm_labred in H0.
 inversion H0.
 intuition.
 substs.
 apply lab_r with (e1:=(e1 >>= swapf))(e2:=(e2 >>= swapf))(s:=s).
 splits.
 apply bind_tau_behave_front.
 assumption.
 apply JO_red_evalbind.
 assumption.
 apply bind_tau_behave_front.
 apply star_trans with (y:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr x1))
          (E_live_expr x0))).
 assumption.
 assumption.
 apply forkee_tau with (lm':=x2) .
 splits.
 intuition.
 apply star_refl.
 intros.
 apply labred_not_val in H0.
 simpl in H0; intuition.


(* <- *)
 
 inversion H.
 substs.
 intros.
 apply fork_swap_lab_behave in H0.
 intuition.
 destruct H1; destruct H0; intuition; substs.
 apply fork_comm_labred in H2.
 exists (E_apply (E_apply (E_constant CONST_fork) (E_live_expr x0))
          (E_live_expr x)).
 splits.
 assumption.
 apply forkee_start.
 destruct H1.
 intuition.
 apply fork_lab_behave in H1.
 intuition.
 destruct H0; destruct H0.
 simplify_eq H0; clear H0; intros; substs.
 destruct H1.
 simplify_eq H0; clear H0; intros; substs.
 destruct H3. destruct H0.
 intuition.
 destruct H0.
 inversion H0.
 substs.
 exists (E_live_expr
          (LM_expr
             (
                (E_taggingright
                   (E_pair  (E_live_expr x1) (E_constant CONST_unit)))))).
 splits.
 apply fork_comm_taured in H3.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr x1))
          (E_live_expr (LM_comp l))))(e2:=(E_live_expr
     (LM_expr
        (E_taggingright
           (E_pair (E_live_expr x1) (E_constant CONST_unit))))))(s:=S_Second).
 splits.
 assumption.
 apply JO_red_forkdocomp2.
 apply star_refl.
 apply forkee_tau with (lm':=(LM_expr
             (E_taggingleft
                (
                   (E_pair (E_constant CONST_unit) (E_live_expr x1)))))).
 splits.
 apply swapf_left_b.
 simpl; auto.
 simpl; auto.
 assumption.
 substs.


 exists (E_live_expr
          (LM_expr
            (E_taggingleft
             (
                (E_pair (E_constant CONST_unit) (E_live_expr x) ))))).
 splits.
 apply fork_comm_taured in H3.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_comp l)))
          (E_live_expr x)))(e2:=(E_live_expr
     (LM_expr
        (E_taggingleft
           (
              (E_pair (E_constant CONST_unit) (E_live_expr x)))))))(s:=S_First).
 splits.
 assumption.
 apply JO_red_forkdocomp1.
 apply star_refl.
 apply forkee_tau with (lm':=(LM_expr
             (E_taggingright
                (E_pair (E_live_expr x) (E_constant CONST_unit))))).
 splits.
 apply swapf_right_b.
 simpl; auto.
 simpl; auto.
 assumption.
 substs.
 
 assert (L:=H3).
 assert(K:=H3).
 induction x; induction x1.
 apply fork_tau_behave_cc in H3.
 discriminate H3.
 apply fork_tau_behave_ce in H3.
 intuition.
 discriminate H1.
 simplify_eq H3; clear H3; intros; substs.
 apply fork_tau_behave_ce in L.
 intuition.
 discriminate H1.
 exists (E_live_expr
         (LM_expr (E_taggingleft (E_pair expr5 (E_live_expr (LM_comp lab)) )))).
 splits.
 apply fork_comm_labred in H0.
 inversion H0.
 intuition.
 substs.
 apply lab_r with (e1:=e1)(e2:=e2)(s:=s).
 splits.
 assumption.
 assumption.
 apply star_trans with (y:=(E_apply
           (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr expr5)))
           (E_live_expr (LM_comp lab)))).
 assumption.
 apply S_star with (y:=(E_live_expr
     (LM_expr (E_taggingleft (E_pair expr5 (E_live_expr (LM_comp lab))))))).
 apply tStep with (s:=S_First).
 apply JO_red_forkdeath1.
 assumption.
 apply star_refl.
 apply forkee_tau with (lm':=(LM_expr
             (E_taggingright (E_pair (E_live_expr (LM_comp lab)) expr5)))).
 splits.
 apply swapf_right_b.
 simpl; auto.
 assumption.
 assumption.
 apply fork_tau_behave_ec in H3.
 intuition.
 discriminate H1.
 simplify_eq H3; clear H3; intros; substs.
 exists (E_live_expr
         (LM_expr (E_taggingright (E_pair (E_live_expr (LM_comp lab)) expr5 )))).
 splits.
 apply fork_comm_labred in H0.
 inversion H0.
 intuition.
 substs.
 apply lab_r with (e1:=e1)(e2:=e2)(s:=s).
 splits.
 assumption.
 assumption.
 apply star_trans with (y:=(E_apply
           (E_apply (E_constant CONST_fork) (E_live_expr (LM_comp lab)))
           (E_live_expr (LM_expr expr5)))).
 assumption.
 apply S_star with (y:=(E_live_expr
     (LM_expr (E_taggingright (E_pair (E_live_expr (LM_comp lab)) expr5))))).
 apply tStep with (s:=S_Second).
 apply JO_red_forkdeath2.
 assumption.
 apply star_refl.
 apply forkee_tau with (lm':=(LM_expr
             (E_taggingleft (E_pair expr5 (E_live_expr (LM_comp lab)))))).
 splits.
 apply swapf_left_b.
 simpl; auto.
 simpl; auto.
 simpl; auto.


 apply fork_tau_behave_ee in H3.
 intuition.
 destruct H1. destruct H1; intuition.
 discriminate H5.
 destruct H3; destruct H1; intuition.
 simplify_eq H6; clear H6; intros; substs.
 exists (E_live_expr
          (LM_expr (E_taggingleft ( (E_pair  x1 (E_live_expr (LM_expr x))))))).
 splits.
 apply fork_comm_labred in H0.
 apply fork_comm_taured_ee_laststep_h in L.
 destruct L.
 destruct H5.
 destruct H5.
 intuition.
 simplify_eq  H6; clear H6; intros; substs.
 simplify_eq  H5; clear H5; intros; substs.
 destruct H8.
 destruct H5.
 intuition.
 inversion H7.
 substs.
 inversion H5.
 substs.
 assert (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr x1)))
       (E_live_expr (LM_expr x)) [S_First]--> [RL_tau]
     E_live_expr
       (LM_expr (E_taggingleft( (E_pair  x1 (E_live_expr (LM_expr x))))))).
 apply JO_red_forkdeath1.
 assumption.
 apply fork_comm_taured in H6.
 inversion H0; intuition.
 substs.
 apply lab_r with (e1:=e1)(e2:=e2)(s:=s).
 splits.
 assumption.
 assumption.
 apply star_trans with (y:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr x0)))
           (E_live_expr (LM_expr x2)))).
 assumption.
 apply star_trans with (y:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr x1)))
          (E_live_expr (LM_expr x)))).
 assumption.
 apply S_star with (y:=(E_live_expr
     (LM_expr
        (E_taggingleft ( (E_pair x1 (E_live_expr (LM_expr x)))))))).
 apply tStep with (s:=S_First).
 assumption.
 apply star_refl.
 exists expr0 expr5 (LM_expr (E_taggingright (E_pair (E_live_expr (LM_expr x)) x1))).
 splits; [reflexivity | reflexivity ].
 
 apply forkee_tau with (lm':=(LM_expr (E_taggingright (E_pair (E_live_expr (LM_expr x)) x1)))).
  splits.
 apply swapf_right_b.
 simpl; auto.
 assumption.
 assumption.


 destruct H3. destruct H1; intuition.
 simplify_eq H6; clear H6; intros; substs.
 exists (E_live_expr
          (LM_expr
             (
                (E_taggingright (E_pair (E_live_expr (LM_expr x1)) x ))))).
 splits.
 apply fork_comm_labred in H0.
  inversion H0.
 substs.
 apply lab_r with (e1:=e1)(e2:=e2)(s:=s).
 splits.
 intuition.
 intuition.
 intuition.
 apply star_trans with (y:=(E_apply
          (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr expr0)))
          (E_live_expr (LM_expr expr5)))).
 
 assumption.
 
 apply fork_comm_taured_ee_laststep_h in L.
 destruct L.
 destruct H7.
 destruct H7.
 intuition.
 simplify_eq  H9; clear H9; intros; substs.
 simplify_eq  H7; clear H7; intros; substs.
 destruct H11.
 destruct H7.
 intuition.
 inversion H10.
 substs.
 inversion H7.
 substs.
 assert (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr x1)))
       (E_live_expr (LM_expr x)) [S_Second]--> [RL_tau]
     E_live_expr
       (LM_expr
          (
             (E_taggingright (E_pair (E_live_expr (LM_expr x1)) x))))).
 apply JO_red_forkdeath2.
 assumption.
 apply fork_comm_taured in H9.
 apply star_trans with (y:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (LM_expr x1)))
          (E_live_expr (LM_expr x)))).
 assumption.
 apply S_star with (y:=(E_live_expr
     (LM_expr (E_taggingright (E_pair (E_live_expr (LM_expr x1)) x))))).
 apply tStep with (s:=S_Second).
 assumption.
 apply star_refl.
 exists expr0 expr5 (LM_expr
     (E_taggingleft ( (E_pair x (E_live_expr (LM_expr x1)))))).
 splits; [reflexivity | reflexivity ].
 
 apply forkee_tau with (lm':=(LM_expr
             (E_taggingleft
                ( (E_pair x (E_live_expr (LM_expr x1))))))).
  splits.
 apply swapf_left_b.
 simpl; auto.
 simpl; auto.
 assumption.
 
 intros.
 substs.
 intuition.
 assert (totalTauRed (E_live_expr lm' >>= swapf) (E_live_expr lm) /\ tauRed (E_live_expr lm' >>= swapf) q).
 splits.
 assumption.
 apply tau_incl_totalTau.
 assumption.

 apply ttau_prefix in H0.
 intuition.
 inversion H3.

 intuition; substs.
 assert (~ (labRed l q q')).
 apply ttr_val_not_labred with (v:= (E_live_expr lm)).
 intuition.
 simpl.
 auto.
 contradiction.
 apply taured_val_id in H4; substs.
 apply labred_not_val in H3.
 simpl in H3; intuition.
 simpl; auto.

 Qed.
