Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Classical_Prop.

Load mconbaseMonProofs.

Check 0.

Definition swapbodyll : expr :=  E_apply ( E_constant CONST_ret )  
                                   ( E_taggingleft 
                                     ( E_taggingleft
                                        (E_apply 
                                          ( E_apply (E_constant CONST_pair)  
                                                    (E_apply (E_constant CONST_proj2) (E_ident (3))) 
                                          ) 
                                          (E_apply (E_constant CONST_proj1) (E_ident (3)))  
                                        )
                                     )
                                   ).

Definition swapbodyl : expr := E_case (E_ident (1)) 
                    (3) ( 
                          swapbodyll
                        ) 
                    (4) (
                           E_apply ( E_constant CONST_ret )  
                                   ( E_taggingleft 
                                     ( E_taggingright
                                        (E_apply 
                                          ( E_apply (E_constant CONST_pair)  
                                                    (E_apply (E_constant CONST_proj2) (E_ident (4))) 
                                          ) 
                                          (E_apply (E_constant CONST_proj1) (E_ident (4)))  
                                        )
                                     )
                                   )

                        ).

Definition swapbodyrr : expr := E_apply ( E_constant CONST_ret )  
                                   ( E_taggingright 
                                     ( E_taggingright
                                        (E_apply 
                                          ( E_apply (E_constant CONST_pair)  
                                                    (E_apply (E_constant CONST_proj2) (E_ident (5))) 
                                          ) 
                                          (E_apply (E_constant CONST_proj1) (E_ident (5)))  
                                        )
                                     )
                                   ).

Definition swapbodyrl : expr :=   E_apply ( E_constant CONST_ret )  
                                   ( E_taggingright 
                                     ( E_taggingleft
                                        (E_apply 
                                          ( E_apply (E_constant CONST_pair)  
                                                    (E_apply (E_constant CONST_proj2) (E_ident (6))) 
                                          ) 
                                          (E_apply (E_constant CONST_proj1) (E_ident (6)))  
                                        )
                                     )
                                   ).

Definition swapbodyr : expr :=  E_case (E_ident (2)) 
                    (5) ( 
                           swapbodyrr
                        ) 
                    (6) (
                         
                           swapbodyrl

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
 rewrite <- H3 in H; simpl in H; auto.
rewrite <- H3 in H; simpl in H; auto.
 rewrite <- H4 in H; simpl in H; auto.
 rewrite <- H4 in H; simpl in H; auto.
 rewrite <- H4 in H; simpl in H; auto.
 rewrite <- H4 in H; simpl in H; auto.
 rewrite <- H4 in H; simpl in H; auto.
 rewrite <- H4 in H; simpl in H; auto.
 inversion H0.
 elim H8; intros H11 H12; elim H12; intros.
 apply H13 in H7; auto.
 contradiction.
 intros.
 inversion H1.
 inversion H2.
 contradiction.
 rewrite <- H6 in H; simpl in H; auto.
 intuition.
 rewrite <- H6 in H; simpl in H; auto.
 intuition.
 rewrite <- H7 in H; simpl in H; auto.
 intuition.
 rewrite <- H7 in H; simpl in H; auto; intuition.
 rewrite <- H6 in H; simpl in H; auto; intuition.
 rewrite <- H7 in H; simpl in H; auto; intuition.
 rewrite <- H7 in H; simpl in H; auto; intuition.
 rewrite <- H7 in H; simpl in H; auto; intuition.
 rewrite <- H7 in H; simpl in H; auto; intuition.
 rewrite <- H7 in H; simpl in H; auto; intuition.
 rewrite <- H7 in H; simpl in H; auto; intuition.
 contradiction.
 inversion H0; intuition.
 cut (tauStep e' e''0).
 intros.
 apply H16 in H15.
 rewrite H15; reflexivity.
 apply tStep with (s:=s).
 trivial.
 contradiction.
 contradiction.
 contradiction.
 rewrite <- H6 in H; simpl in H; intuition.
 rewrite <- H6 in H2; rewrite <- H6 in H1; rewrite <- H6 in H0.
 rewrite <- H10 in H2.
 rewrite <- H10 in H7.
 intuition.
 rewrite <- H6 in H; simpl in H; rewrite <- H10 in H9; intuition.
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
 rewrite <- H3 in H0; simpl in H0; intuition.
rewrite <- H3 in H0; simpl in H0; intuition.
 rewrite <- H4 in H0; simpl in H0; intuition.
 rewrite <- H4 in H0; simpl in H0; intuition.
 rewrite <- H4 in H0; simpl in H0; intuition.
 rewrite <- H4 in H0; simpl in H0; intuition.
 rewrite <- H4 in H0; simpl in H0; intuition.
 rewrite <- H4 in H0; simpl in H0; intuition.
 apply red_not_value in H8.
 contradiction.
 inversion H1.
 intuition.
 apply H10 in H9; trivial.
 intros.
 inversion H2.
 inversion H3.
 intros.
 rewrite <- H6 in H0; simpl in H0; auto; intuition.
 rewrite <- H6 in H0; simpl in H0; auto; intuition.
 rewrite <- H6 in H0; simpl in H0; auto; intuition.
 rewrite <- H6 in H0; simpl in H0; auto; intuition.
 rewrite <- H6 in H0; simpl in H0; auto; intuition.
 rewrite <- H6 in H0; simpl in H0; auto; intuition.
 rewrite <- H7 in H0; simpl in H0; auto; intuition.
 rewrite <- H7 in H0; simpl in H0; auto; intuition.
 rewrite <- H7 in H0; simpl in H0; auto; intuition.
 rewrite <- H7 in H0; simpl in H0; auto; intuition.
 rewrite <- H7 in H0; simpl in H0; auto; intuition.
 rewrite <- H7 in H0; simpl in H0; auto; intuition.
 rewrite <- H6 in H0; simpl in H0; auto; intuition.
 apply red_not_value in H11.
 contradiction.
 cut (tauStep e e'1).
 intros.
 inversion H1.
 intuition.
 apply H19 in H13.
 rewrite H13; reflexivity.
 
 eauto.
 rewrite <- H6 in H0; simpl in H0.
 contradiction.
 rewrite <- H6 in H0; simpl in H0;
 contradiction.
 rewrite <- H6 in H0; simpl in H0; intuition.
 rewrite <- H6 in H0; simpl in H0; intuition.
Qed.

Lemma swapf_left_left : forall (v v' : expr), 
           is_value_of_expr v ->
           is_value_of_expr v' ->
           totalTauRed ( E_apply (swapf) (E_taggingleft (E_taggingleft ( E_pair v v' )) ) ) (E_live_expr(LM_expr(E_taggingleft (E_taggingleft ( E_pair v' v )) ))).
Proof.
 intros.
 apply S_star with (y:=(subst_expr (E_taggingleft (E_taggingleft ( E_pair v v' ))) 0 swapbody )).
 apply JO_red_app_td.
 simpl.
 auto.
 simpl.
 apply S_star with (y:=(subst_expr   (E_taggingleft ( E_pair v v' ))   1   swapbodyl )).
 apply JO_red_evalcaseinl_td.
 simpl; auto.
 apply S_star with (y:=(subst_expr    ( E_pair v v' )   3   swapbodyll )).
 apply JO_red_evalcaseinl_td.
 simpl; auto.
 apply S_star with (y:=E_apply ( E_constant CONST_ret )  
                                   ( E_taggingleft 
                                     ( E_taggingleft
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
 apply JO_red_evalinl_td.
 simpl; auto.
 apply JO_red_evalinl_td.
 simpl; auto.
 apply JO_red_context_app1_td.
 simpl; auto.
 apply JO_red_proj1_td.
 trivial.
 trivial.
 apply S_star with (y:=(E_apply (E_constant CONST_ret)
       (E_taggingleft
          (E_taggingleft
             (E_apply
                (E_apply (E_constant CONST_pair)
                   (v')) v))))).
 apply JO_red_context_app1_td.
 simpl; auto.
  apply JO_red_evalinl_td.
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
     (E_taggingleft
        (E_taggingleft (E_pair v' v)))))).
 apply JO_red_context_app1_td.
 simpl; auto.
 apply JO_red_evalinl_td.
 simpl; auto.
 apply JO_red_evalinl_td.
 simpl; auto.
 apply JO_red_inpair_td.
 simpl; auto.
 simpl; auto.
 apply S_star with (y:=(E_live_expr (LM_expr (E_taggingleft (E_taggingleft (E_pair v' v)))))).
 apply JO_red_ret_td.
 apply S_First.
 simpl;auto.
 apply star_refl.
Qed.


Lemma swapf_right_right : forall (v v' : expr), 
           is_value_of_expr v ->
           is_value_of_expr v' ->
           totalTauRed ( E_apply (swapf) (E_taggingright (E_taggingright ( E_pair v v' )) ) ) (E_live_expr(LM_expr(E_taggingright (E_taggingleft ( E_pair v' v )) ))).
Proof.
 intros.
 apply S_star with (y:=(subst_expr (E_taggingright (E_taggingright ( E_pair v v' ))) 0 swapbody )).
 apply JO_red_app_td.
 simpl.
 auto.
 simpl.
 apply S_star with (y:=(subst_expr   (E_taggingright ( E_pair v v' ))   2   swapbodyr )).
 apply JO_red_evalcaseinr_td.
 simpl; auto.
 apply S_star with (y:=(subst_expr    ( E_pair v v' )   6   swapbodyrl )).
 simpl.
 apply JO_red_evalcaseinr_td.
 simpl; auto.
 simpl.
 apply S_star with (y:=E_apply ( E_constant CONST_ret )  
                                   ( E_taggingright 
                                     ( E_taggingleft
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
 apply JO_red_evalinl_td.
 simpl; auto.
 apply JO_red_context_app1_td.
 simpl; auto.
 apply JO_red_proj1_td.
 trivial.
 trivial.
 apply S_star with (y:=(E_apply (E_constant CONST_ret)
       (E_taggingright
          (E_taggingleft
             (E_apply
                (E_apply (E_constant CONST_pair)
                   (v')) v))))).
 apply JO_red_context_app1_td.
 simpl; auto.
  apply JO_red_evalinr_td.
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
     (E_taggingright
        (E_taggingleft (E_pair v' v)))))).
 apply JO_red_context_app1_td.
 simpl; auto.
 apply JO_red_evalinr_td.
 simpl; auto.
 apply JO_red_evalinl_td.
 simpl; auto.
 apply JO_red_inpair_td.
 simpl; auto.
 simpl; auto.
 apply S_star with (y:=(E_live_expr (LM_expr (E_taggingright (E_taggingleft (E_pair v' v)))))).
 apply JO_red_ret_td.
 apply S_First.
 simpl;auto.
 apply star_refl.
Qed.


Lemma swapf_right_left : forall (v v' : expr), 
           is_value_of_expr v ->
           is_value_of_expr v' ->
           totalTauRed ( E_apply (swapf) (E_taggingright (E_taggingleft ( E_pair v v' )) ) ) (E_live_expr(LM_expr(E_taggingright (E_taggingright ( E_pair v' v )) ))).
Proof.
 intros.
 apply S_star with (y:=(subst_expr (E_taggingright (E_taggingleft ( E_pair v v' ))) 0 swapbody )).
 apply JO_red_app_td.
 simpl.
 auto.
 simpl.
 apply S_star with (y:=(subst_expr   (E_taggingleft ( E_pair v v' ))   2   swapbodyr )).
 apply JO_red_evalcaseinr_td.
 simpl; auto.
 apply S_star with (y:=(subst_expr    ( E_pair v v' )   5   swapbodyrr )).
 simpl.
 apply JO_red_evalcaseinl_td.
 simpl; auto.
 simpl.
 apply S_star with (y:=E_apply ( E_constant CONST_ret )  
                                   ( E_taggingright 
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
 apply JO_red_evalinr_td.
 simpl; auto.
 apply JO_red_context_app1_td.
 simpl; auto.
 apply JO_red_proj1_td.
 trivial.
 trivial.
 apply S_star with (y:=(E_apply (E_constant CONST_ret)
       (E_taggingright
          (E_taggingright
             (E_apply
                (E_apply (E_constant CONST_pair)
                   (v')) v))))).
 apply JO_red_context_app1_td.
 simpl; auto.
  apply JO_red_evalinr_td.
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
     (E_taggingright
        (E_taggingright (E_pair v' v)))))).
 apply JO_red_context_app1_td.
 simpl; auto.
 apply JO_red_evalinr_td.
 simpl; auto.
 apply JO_red_evalinr_td.
 simpl; auto.
 apply JO_red_inpair_td.
 simpl; auto.
 simpl; auto.
 apply S_star with (y:=(E_live_expr (LM_expr (E_taggingright (E_taggingright (E_pair v' v)))))).
 apply JO_red_ret_td.
 apply S_First.
 simpl;auto.
 apply star_refl.
Qed.

(*
Theorem fork_comm : forall (e e': livemodes), weakbisim (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (e))) (E_live_expr (e'))) (E_bind (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (e'))) (E_live_expr (e))) (swapf)).
Proof.
 intros.
 induction e; induction e'.
 apply weakbi.
 split.
 apply weaksim_gen.
 intros.
 inversion H.
 intuition.
 inversion H4.
 rewrite <- H7 in H0.
 inversion H0.
 exists ((E_apply
        (E_apply (E_constant CONST_fork)
           (E_live_expr ( (LM_comp rl0))))
        (E_live_expr (LM_expr (E_constant CONST_unit)))) >>= swapf).
 split.
 rewrite <- H12 in H6.
 apply lab_r.
 
Admitted. 
*)