Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Classical_Prop.


Load redTotalDetProp.







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
 apply S_star with (y:=E_apply ( E_constant CONST_ret )
                                    ( E_taggingleft 
                                     (
                                        (E_apply 
                                          ( E_apply (E_constant CONST_pair)  
                                                    (v') 
                                          ) 
                                          (E_apply (E_constant CONST_proj1) (E_pair v v')) 
                                        )
                                     ))).
 simpl.
 apply JO_red_context_app2_td.
 simpl.
 auto.
 intuition.
 apply JO_red_evalinl_td.
 simpl; auto.
 apply JO_red_context_app1_td.
 simpl; auto.
 apply JO_red_context_app2_td.
 simpl; auto.
 simpl; auto.
 apply JO_red_proj2_td.
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
 apply JO_red_context_app2_td.
 simpl; auto.
 simpl; auto.
 apply JO_red_evalinl_td.
 simpl; auto.
 apply JO_red_context_app2_td.
 simpl; auto.
 simpl; auto.
 apply JO_red_proj1_td.
 trivial.
 trivial.
 apply S_star with (y:=((E_apply (E_constant CONST_ret)
     ( E_taggingleft (
        ( (E_pair v' v))))))).
 apply JO_red_context_app2_td.
 simpl; auto.
 simpl; auto.
 apply JO_red_evalinl_td.
 simpl; auto.
 apply JO_red_inpair_td.
 simpl; auto.
 simpl; auto.
 apply S_star with (y:=(E_live_expr ( (E_taggingleft (((E_pair v' v))))))).
 apply JO_red_ret_td.
 apply S_First.
 simpl;auto.
 apply star_refl.
Qed.

Lemma swapf_right_b : forall (v v' : expr), 
           is_value_of_expr v ->
           is_value_of_expr v' ->
           totalTauRed ( (E_live_expr (  (E_taggingright (( E_pair v v' )))) ) >>= swapf) (E_live_expr((E_taggingleft( ( ( E_pair v' v )) )))).
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
 apply S_star with (y:=E_apply ( E_constant CONST_ret )  
                                   (  
                                     ( E_taggingright
                                        (E_apply 
                                          ( E_apply (E_constant CONST_pair)  
                                                    (v') 
                                          ) 
                                          (E_apply (E_constant CONST_proj1) (E_pair v v'))  
                                        )
                                     )
                                   )).
 simpl.
 apply JO_red_context_app2_td.
 simpl.
 auto.
 simpl; auto.
 apply JO_red_evalinr_td.
 simpl; auto.
 apply JO_red_context_app1_td.
 simpl; auto.
 apply JO_red_context_app2_td.
 simpl; auto.
 simpl; auto.
 apply JO_red_proj2_td.
 trivial.
 trivial.
 apply S_star with (y:=(E_apply (E_constant CONST_ret)
       (
          (E_taggingright
             (E_apply
                (E_apply (E_constant CONST_pair)
                   (v')) v))))).
 apply JO_red_context_app2_td.
 simpl; auto.
 simpl; auto.
  apply JO_red_evalinr_td.
 simpl; auto.
 apply JO_red_context_app2_td.
 simpl; auto.
 simpl; auto.
 apply JO_red_proj1_td.
 trivial.
 trivial.
 apply S_star with (y:=((E_apply (E_constant CONST_ret)
     (
        (E_taggingright (E_pair v' v)))))).
 apply JO_red_context_app2_td.
 simpl; auto.
 simpl; auto.
 apply JO_red_evalinr_td.
 simpl; auto.
 apply JO_red_inpair_td.
 simpl; auto.
 simpl; auto.
 apply S_star with (y:=(E_live_expr ( ((E_taggingright (E_pair v' v)))))).
 apply JO_red_ret_td.
 apply S_First.
 simpl;auto.
 apply star_refl.
Qed.

Lemma swapf_left_b : forall (v v' : expr), 
           is_value_of_expr v ->
           is_value_of_expr v' ->
           totalTauRed (  (E_live_expr((E_taggingleft ( ( E_pair v v' )) ))) >>= (swapf)) (E_live_expr(( (E_taggingright ( E_pair v' v )) ))).
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


Check star_ind.


Lemma fork_tau_step_behave_ee : forall (p q e : expr), tauStep (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( p)) ) (E_live_expr ( q))) e -> 
   ((exists (p' q' : expr), tauRed p p' /\ tauRed q q' /\ e = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( p')) ) (E_live_expr ( q')))) \/ 
  ((exists (p' vq : expr), is_value_of_expr vq /\ tauRed p p' /\ tauRed q vq /\ e = ((E_live_expr (  (  (E_taggingright  (E_pair  (E_live_expr ( p')) vq ) ) ) )))) \/ 
  ((exists (vp q' : expr), is_value_of_expr vp /\ tauRed p vp /\ tauRed q q' /\ e=((E_live_expr (  (E_taggingleft  (  (E_pair vp (E_live_expr ( q'))  ) ) ) ))))))) .
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
 apply red_not_value in H7; simpl in H7; intuition.
 apply red_not_value in H6; simpl in H6; intuition.
Qed.


Definition  fork_tau_step_ee : expr -> expr -> Prop := (fun b e => (forall (p q : expr), b=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( p)) ) (E_live_expr ( q))) -> 
   ((exists (p' q' : expr), tauRed p p' /\ tauRed q q' /\ e = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( p')) ) (E_live_expr ( q')))) \/ 
  ((exists (p' vq : expr), is_value_of_expr vq /\ tauRed p p' /\ tauRed q vq /\ e = ((E_live_expr (  (  (E_taggingright  (E_pair  (E_live_expr ( p')) vq ) ) ) )))) \/ 
  (
   (exists (vp q' : expr), is_value_of_expr vp /\ tauRed p vp /\ tauRed q q' /\ e=((E_live_expr (  (E_taggingleft  ( (E_pair vp (E_live_expr ( q'))  ) ) ) ))))))))) .


Lemma fork_tau_behave_ee_h : forall (b e : expr), tauRed b e -> (fork_tau_step_ee) b e.
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
 
Lemma fork_tau_behave_ee : forall (p q e : expr), tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( p)) ) (E_live_expr ( q))) e -> 
((exists (p' q' : expr), tauRed p p' /\ tauRed q q' /\ e = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( p')) ) (E_live_expr ( q')))) \/ 
  ((exists (p' vq : expr), is_value_of_expr vq /\ tauRed p p' /\ tauRed q vq /\ e = ((E_live_expr (  (  (E_taggingright  (E_pair  (E_live_expr ( p')) vq ) ) ) )))) \/ 
  (
   (exists (vp q' : expr), is_value_of_expr vp /\ tauRed p vp /\ tauRed q q' /\ e=((E_live_expr (  (E_taggingleft  (  (E_pair vp (E_live_expr ( q'))  ) ) ) ))))))) .
Proof.
 intros.
 apply fork_tau_behave_ee_h in H.
 specialize (H p q).
 apply H.
 reflexivity.
Qed.

Lemma fork_tau_behave_edge1 : forall  (e e' x : expr), tauRed e x -> ~ (is_value_of_expr e') -> tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e))) (E_live_expr ( e'))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x))) (E_live_expr ( e'))).
Proof. 
 intros.
 apply star_ind with (R:=tauStep)(X:=expr)(P:= (fun y z => tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( y))) (E_live_expr ( e'))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( z))) (E_live_expr ( e'))))).
 intros; apply star_refl.
 intros.
 apply S_star with (y:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( y))) (E_live_expr ( e')))).
 apply tStep with (s:=S_First).
 inversion H1.
 apply  JO_red_forkmove1 with (s:=s).
 assumption.
 assumption.
 assumption.
 assumption.
Qed.

Lemma fork_tau_push_ee_1 : forall  (e e' x : expr), tauRed e x -> ~ (is_value_of_expr e') -> tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e))) (E_live_expr ( e'))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x))) (E_live_expr ( e'))).
Proof. 
 intros.
 apply star_ind with (R:=tauStep)(X:=expr)(P:= (fun y z => tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( y))) (E_live_expr ( e'))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( z))) (E_live_expr ( e'))))).
 intros; apply star_refl.
 intros.
 apply S_star with (y:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( y))) (E_live_expr ( e')))).
 apply tStep with (s:=S_First).
 inversion H1.
 substs.
 apply  JO_red_forkmove1 with (s:=s).
 assumption.
 assumption.
 assumption.
 assumption.
Qed.

Lemma fork_tau_behave_edge2 : forall  (e e' x : expr), tauRed e' x -> ~ (is_value_of_expr e) -> tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e))) (E_live_expr ( e'))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e))) (E_live_expr ( x))).
Proof. 
 intros.
 apply star_ind with (R:=tauStep)(X:=expr)(P:= (fun y z => tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e))) (E_live_expr ( y))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e))) (E_live_expr ( z))))).
 intros; apply star_refl.
 intros.
 apply S_star with (y:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e))) (E_live_expr ( y)))).
 apply tStep with (s:=S_Second).
 inversion H1.
 apply  JO_red_forkmove2 with (s:=s).
 assumption.
 assumption.
 assumption.
 assumption.
Qed.

Lemma fork_tau_push_ee_2 : forall  (e e' x : expr), tauRed e' x -> ~ (is_value_of_expr e) ->  tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e))) (E_live_expr ( e'))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e))) (E_live_expr ( x))).
Proof. 
 intros.
 apply star_ind with (R:=tauStep)(X:=expr)(P:= (fun y z => tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e))) (E_live_expr ( y))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e))) (E_live_expr ( z))))).
 intros; apply star_refl.
 intros.
 apply S_star with (y:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e))) (E_live_expr ( y)))).
 apply tStep with (s:=S_Second).
 inversion H1.
 substs.
 apply  JO_red_forkmove2 with (s:=s).
 assumption.
 assumption.
 assumption.
 assumption.
Qed.
(*
Lemma fork_tau_push_ee_12 : forall  (e e' x y : expr), tauRed e' x -> tauRed e y -> tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e))) (E_live_expr ( e'))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( y))) (E_live_expr ( x))).
Proof. 
 intros.
 assert (He:=H0).
 apply fork_tau_push_ee_1 with (e':=e') in He.
 assert (He':=H).
 apply fork_tau_push_ee_2 with (e:=y) in He'.
 apply star_trans with (y:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( y)))
          (E_live_expr ( e')))).
 assumption.
 assumption.
Qed.
*)
Lemma fork_tau_swap_ee : forall (p q e : expr), tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( p)) ) (E_live_expr ( q))) e -> 
((exists (p' q' : expr), tauRed p p' /\ tauRed q q' /\ e = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( p')) ) (E_live_expr ( q')))
   /\ tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( q)) ) (E_live_expr ( p))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( q')) ) (E_live_expr ( p')))
  ) \/ 
  ((exists (p' vq : expr), is_value_of_expr vq /\ tauRed p p' /\ tauRed q vq /\ e = ((E_live_expr (  (  (E_taggingright  (E_pair  (E_live_expr ( p')) vq ) ) ) )))
   /\ tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( q)) ) (E_live_expr ( p))) ((E_live_expr (  (E_taggingleft  (  (E_pair vq (E_live_expr ( p'))  ) ) ) )))
  ) \/ 
  (
   (exists (vp q' : expr), is_value_of_expr vp /\ tauRed p vp /\ tauRed q q' /\ e=((E_live_expr (  (E_taggingleft  (  (E_pair vp (E_live_expr ( q'))  ) ) ) ))) /\ 
      tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( q)) ) (E_live_expr ( p))) ((E_live_expr (  (  (E_taggingright  (E_pair  (E_live_expr ( q')) vp ) ) ) )))
  )))) .
Proof.
 Check star_ind.
 specialize star_ind with (X:=expr)(R:=tauStep)(P:=
  fun x y => (forall (p q : expr), x = p # q -> (exists (p' q' : expr), ((y=p'#q' /\ tauRed (q#p) (q'#p'))\/(y=p'<#q' /\ is_value_of_expr p' /\ tauRed (q#p) (q'#>p'))\/(y=p'#>q' /\ is_value_of_expr q' /\ tauRed (q#p) (q'<#p')) ) ))).
 
 intros.
 assert ((forall x p q : expr,
     x = p # q ->
     exists p' q',
     x = p' # q' /\ tauRed (q # p) (q' # p') \/
     x = p' <# q' /\ is_value_of_expr p' /\ tauRed (q # p) (q' #> p') \/
     x = p' #> q' /\ is_value_of_expr q' /\ tauRed (q # p) (q' <# p'))).
 intros.
 exists p0 q0.
 left.
 intuition.
 apply star_refl.
 intuition.
 assert ((forall y x z : expr,
      tauStep x y ->
      star tauStep y z ->
      (forall p q : expr,
       y = p # q ->
       exists p' q',
       z = p' # q' /\ tauRed (q # p) (q' # p') \/
       z = p' <# q' /\ is_value_of_expr p' /\ tauRed (q # p) (q' #> p') \/
       z = p' #> q' /\ is_value_of_expr q' /\ tauRed (q # p) (q' <# p')) ->
      forall p q : expr,
      x = p # q ->
      exists p' q',
      z = p' # q' /\ tauRed (q # p) (q' # p') \/
      z = p' <# q' /\ is_value_of_expr p' /\ tauRed (q # p) (q' #> p') \/
      z = p' #> q' /\ is_value_of_expr q' /\ tauRed (q # p) (q' <# p'))).
 intros.
 substs.
 inversion H.
 substs.
 inversion H5.
 substs.
 specialize H4 with (p:=e'')(q:=q0).
 intuition.
 destruct H6.
 destruct H4.
 intuition.
 substs.
 exists x x0.
 left.
 intuition.
 apply H4.
 apply H in H1.
 apply fork_tau_behave_ee in H.
 intuition.
 left.
 destruct H0; destruct H.
 intuition.
 substs.
 exists x x0.
 splits.
 assumption.
 assumption.
 reflexivity.
 apply fork_tau_push_ee_12.
 assumption.
 assumption.
 destruct H; destruct H.
 intuition.
 substs.
 right.
 left.
 exists x x0.
 splits.
 assumption.
 assumption.
 assumption.
 reflexivity.
 apply star_S with (y:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x0)))
     (E_live_expr ( x)))).
 apply fork_tau_push_ee_12.
 assumption.
 assumption.
 apply tStep with (s:=S_First).
 apply JO_red_forkdeath1.
 assumption.
 destruct H; destruct H.
 intuition.
 substs.
 right.
 right.
 exists x x0.
 splits.
 assumption.
 assumption.
 assumption.
 reflexivity.
 apply star_S with (y:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x0)))
     (E_live_expr ( x)))).
 apply fork_tau_push_ee_12.
 assumption.
 assumption.
 apply tStep with (s:=S_Second).
 apply JO_red_forkdeath2.
 assumption.
Qed.




Lemma fork_lab_push_ee_1 : forall  (e e' x : expr) (l:label), labRed l e x ->  labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e))) (E_live_expr ( e'))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x))) (E_live_expr ( e'))).
Proof.
 intros.
 inversion H.
 intuition.
 substs.
 apply lab_r with (e1:= (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e1)))
     (E_live_expr ( e'))))(e2:= (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e2)))
     (E_live_expr ( e'))))(s:=S_First).
 splits.
 apply fork_tau_push_ee_1;[ assumption ].
 apply JO_red_forkmove1 with (s:=s);  assumption .
 apply fork_tau_push_ee_1; [ assumption ].
Qed.

Lemma fork_lab_push_ee_2 : forall  (e e' x : expr) (l:label), labRed l e' x -> labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e))) (E_live_expr ( e'))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e))) (E_live_expr ( x))).
Proof.
 intros.
 inversion H.
 intuition.
 substs.
 apply lab_r with (e1:= (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e)))
     (E_live_expr ( e1))))(e2:= (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e)))
     (E_live_expr ( e2))))(s:=S_Second).
 splits.
 apply fork_tau_push_ee_2;[ assumption ].
 apply JO_red_forkmove2 with (s:=s); assumption.
 apply fork_tau_push_ee_2; [ assumption ].
Qed.

Lemma fork_lab_push_ee_full1 : forall  (e e' x e'' : expr) (l:label), labRed l e x -> tauRed e' e'' -> labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e))) (E_live_expr ( e'))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x))) (E_live_expr ( e''))).
Proof.
 intros.
 apply fork_tau_push_ee_2 with (e:=e) in H0.
 apply fork_lab_push_ee_1 with (e':=e'') in H.
 inversion H.
 intuition.
 substs.
 apply lab_r with (e1:=e1)(e2:=e2)(s:=s).
 splits.
 apply star_trans with (y:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e)))
          (E_live_expr ( e'')))).
 assumption.
 assumption.
 assumption.
 assumption.
Qed.

Lemma fork_lab_push_ee_full2 : forall  (e e' x e'' : expr) (l:label), labRed l e' x -> tauRed e e'' -> labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e))) (E_live_expr ( e'))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e''))) (E_live_expr ( x))).
Proof.
 intros.
 apply fork_tau_push_ee_1 with (e':=e') in H0.
 apply fork_lab_push_ee_2 with (e:=e'') in H.
 inversion H.
 intuition.
 substs.
 apply lab_r with (e1:=e1)(e2:=e2)(s:=s).
 splits.
 apply star_trans with (y:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e'')))
          (E_live_expr ( e')))).
 assumption.
 assumption.
 assumption.
 assumption.
Qed.

Lemma fork_lab_behave_edge1 : forall  (e e' x : expr) (l:label), labRed l e x -> ~ (is_value_of_expr e') -> labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e))) (E_live_expr ( e'))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x))) (E_live_expr ( e'))).
Proof.
 intros.
 inversion H.
 intuition.
 substs.
 apply lab_r with (e1:= (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e1)))
     (E_live_expr ( e'))))(e2:= (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e2)))
     (E_live_expr ( e'))))(s:=S_First).
 splits.
 apply fork_tau_behave_edge1;[ assumption | assumption ].
 apply JO_red_forkmove1 with (s:=s);  assumption .
 apply fork_tau_behave_edge1; [ assumption |  assumption ].
Qed.

Lemma fork_tau_behave_edge12 : forall  (e e' x y : expr), tauRed e' x -> tauRed e y -> ~ is_value_of_expr e' -> ~ (is_value_of_expr e) -> ~ is_value_of_expr y -> ~ (is_value_of_expr x) -> tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e))) (E_live_expr ( e'))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( y))) (E_live_expr ( x))).
Proof. 
 intros.
 assert (He:=H0).
 apply fork_tau_behave_edge1 with (e':=e') in He.
 assert (He':=H).
 apply fork_tau_behave_edge2 with (e:=y) in He'.
 apply star_trans with (y:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( y)))
          (E_live_expr ( e')))).
 assumption.
 assumption.
 assumption.
 assumption.
Qed.




Lemma fork_lab_behave_edge2 : forall  (e e' x : expr) (l:label), labRed l e' x -> ~ (is_value_of_expr e) -> labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e))) (E_live_expr ( e'))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e))) (E_live_expr ( x))).
Proof.
 intros.
 inversion H.
 intuition.
 substs.
 apply lab_r with (e1:= (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e)))
     (E_live_expr ( e1))))(e2:= (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e)))
     (E_live_expr ( e2))))(s:=S_Second).
 splits.
 apply fork_tau_behave_edge2;[ assumption | assumption ].
 apply JO_red_forkmove2 with (s:=s); assumption.
 apply fork_tau_behave_edge2; [ assumption |  assumption ].
Qed.


Inductive fork_tau_ce_int_s : relation expr :=
 | fork_tau_ce_int_step : forall (e e' : expr) (l : label), tauStep e e' -> fork_tau_ce_int_s (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp l)))
          (E_live_expr ( e))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp l)))
          (E_live_expr ( e'))).
Inductive fork_tau_ce_ext_s : relation expr :=
 | fork_tau_ce_ext_step : forall (e e' : expr) (l : label), tauStep (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp l)))
          (E_live_expr ( e))) e' -> fork_tau_ce_ext_s (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp l)))
          (E_live_expr ( e))) e'.


Lemma fork_tau_behave_ce_h : forall (x y : expr), tauRed x y ->
       ((fun a b => 

    ((exists (expr5 : expr) (lab : label), 
         a= (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab))) (E_live_expr ( expr5))) ) 
          -> 
        (exists (expr5 : expr) (lab : label), 
           a=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab))) (E_live_expr ( expr5))) 
           /\ (exists ( e' : expr),tauRed expr5 e' /\
                 (
                  (
                   (b = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab))) (E_live_expr ( e'))))
                    \/
                   (b = E_live_expr ( (E_taggingright (E_pair (E_live_expr (E_comp lab)) e'))) /\ is_value_of_expr e')
                  )       
                 )
               )
        )
    )) x y).
Proof.
 apply star_ind.
 intros.
 destruct H.
 destruct H.
 substs.
 exists x0 x1.
 splits.
 reflexivity.
 exists x0.
 splits.
 apply star_refl.
 left.
 reflexivity.
 intros.
 destruct H2.
 destruct H2.
 substs.
 exists x0 x1.
 splits.
 reflexivity.
 inversion H.
 substs.
 inversion H2.
 substs.
 destruct H1.
 exists e'' x1.
 reflexivity.
 destruct H1.
 intuition.
 destruct H4.
 intuition.
 substs.
 simplify_eq H3; clear H3; intros; substs.
 exists x3.
 splits.
 apply S_star with (y:=x).
 apply tStep with (s:=s0).
 assumption.
 assumption.
 left.
 reflexivity.
 substs.
 simplify_eq H3; clear H3; intros; substs.
 exists x3.
 splits.
 apply S_star with (y:=x).
 apply tStep with (s:=s0).
 assumption.
 assumption.
 right.
 splits; [reflexivity | assumption].
 substs.
 apply taured_val_id in H0.
 substs.
 exists x0. 
 splits; [apply star_refl | right; splits; [ reflexivity | assumption ] ].
 simpl; auto.
 apply red_not_value in H9; simpl in H9; intuition.
 apply red_not_value in H8; simpl in H8; intuition.
Qed.


Lemma fork_tau_behave_ce : forall (expr5 e  : expr) (lab : label), tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab)))
          (E_live_expr ( expr5))) e -> (exists ( e' : expr),tauRed expr5 e' /\ ((  e = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab)))
          (E_live_expr ( e'))))\/(e = E_live_expr
       ( (E_taggingright (E_pair (E_live_expr (E_comp lab)) e'))) /\ is_value_of_expr e'))) .
Proof.
  intros.
  assert (
   (fun a b => 

    ((exists (expr5 : expr) (lab : label), 
         a= (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab))) (E_live_expr ( expr5))) ) 
          -> 
        (exists (expr5 : expr) (lab : label), 
           a=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab))) (E_live_expr ( expr5))) 
           /\ (exists ( e' : expr),tauRed expr5 e' /\
                 (
                  (
                   (b = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab))) (E_live_expr ( e'))))
                    \/
                   (b = E_live_expr ( (E_taggingright (E_pair (E_live_expr (E_comp lab)) e'))) /\ is_value_of_expr e')
                  )       
                 )
               )
        )
    )) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab)))
         (E_live_expr ( expr5))) e
  ).
  apply fork_tau_behave_ce_h.
  assumption.
  simpl in H0.
  destruct H0.
  exists expr5 lab; reflexivity.
  destruct H0.
  intuition.
  simplify_eq H1; clear H1; intros; substs.
  assumption.
Qed.


Lemma fork_tau_ec_push_h : forall (x y : expr), tauRed x y ->
       ((fun a b => 

    ((forall (lab : label), 
         tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( a))) (E_live_expr  (E_comp lab)))  (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( b))) (E_live_expr  (E_comp lab))) ) 
          
    )) x y).
Proof.
 apply star_ind.
 intros; apply star_refl.
 intros.
 apply S_star with (y:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( y)))
     (E_live_expr (E_comp lab)))).
 apply tStep with (s:=S_First).
 inversion H.
 
 apply JO_red_forkmove1 with (s:=s).
 assumption.
 apply H1.
Qed.

Lemma fork_tau_ce_push_h : forall (x y : expr), tauRed x y ->
       ((fun a b => 

    ((forall (lab : label), 
         tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab))) (E_live_expr   ( a)))  (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab))) (E_live_expr   ( b))) ) 
          
    )) x y).
Proof.
 apply star_ind.
 intros; apply star_refl.
 intros.
 apply S_star with (y:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab)))
     (E_live_expr  ( y)))).
 apply tStep with (s:=S_Second).
 inversion H.
 
 apply JO_red_forkmove2 with (s:=s).
 assumption.
 apply H1.
Qed.

Lemma fork_tau_swap_ce : forall (expr5 e  : expr) (lab : label), tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab)  ))
          (E_live_expr  ( expr5))) e -> (exists ( e' : expr),tauRed expr5 e' /\ ((  e = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab)))
          (E_live_expr   ( e'))) /\ tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr  ( expr5) ))
          (E_live_expr   (E_comp lab))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr   ( e')))
          (E_live_expr  (E_comp lab)))  )\/(e = E_live_expr
       ( (E_taggingright (E_pair (E_live_expr (E_comp lab)) e'))) /\ is_value_of_expr e' /\ tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr  ( expr5) ))
          (E_live_expr   (E_comp lab))) (E_live_expr
       ( (E_taggingleft (E_pair e' (E_live_expr  (E_comp lab)))))) ))) .
Proof.
intros.
 apply fork_tau_behave_ce in H.
 intuition.
 destruct H.
 intuition.
 substs.
 exists x.
 intuition.
 left.
 intuition.
 apply fork_tau_ec_push_h.
 assumption.
 substs.
 exists x.
 intuition.
 right.
 intuition. 
 assert (tauRed
  (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( expr5)  ))
     (E_live_expr (E_comp lab)))  (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x)  ))
     (E_live_expr (E_comp lab)))).
 apply fork_tau_ec_push_h.
 assumption.
 apply star_S with (y:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x)))
         (E_live_expr (E_comp lab)  ))).
 assumption.
 apply tStep with (s:=S_First).
 apply JO_red_forkdeath1.
 assumption.
Qed.

Lemma fork_tau_behave_ec_h : forall (x y : expr), tauRed x y ->
       ((fun a b => 

    ((exists (expr5 : expr) (lab : label), 
         a= (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( expr5))) (E_live_expr  (E_comp lab))) ) 
          -> 
        (exists (expr5 : expr) (lab : label), 
           a=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( expr5) )) (E_live_expr  (E_comp lab))) 
           /\ (exists ( e' : expr),tauRed expr5 e' /\
                 (
                  (
                   (b = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e') )) (E_live_expr  (E_comp lab))))
                    \/
                   (b = E_live_expr ( (E_taggingleft (E_pair e' (E_live_expr (E_comp lab))))) /\ is_value_of_expr e')
                  )       
                 )
               )
        )
    )) x y).
Proof.
 apply star_ind.
 intros.
 destruct H.
 destruct H.
 substs.
 exists x0 x1.
 splits.
 reflexivity.
 exists x0.
 splits.
 apply star_refl.
 left.
 reflexivity.
 intros.
 destruct H2.
 destruct H2.
 substs.
 exists x0 x1.
 splits.
 reflexivity.
 inversion H.
 substs.
 inversion H2.
 substs.
 destruct H1.
 exists e'' x1.
 reflexivity.
 destruct H1.
 intuition.
 destruct H4.
 intuition.
 substs.
 simplify_eq H3; clear H3; intros; substs.
 exists x3.
 splits.
 apply S_star with (y:=x).
 apply tStep with (s:=s0).
 assumption.
 assumption.
 left.
 reflexivity.
 substs.
 simplify_eq H3; clear H3; intros; substs.
 exists x3.
 splits.
 apply S_star with (y:=x).
 apply tStep with (s:=s0).
 assumption.
 assumption.
 right.
 splits; [reflexivity | assumption].
 substs.
 apply taured_val_id in H0.
 substs.
 exists x0. 
 splits; [apply star_refl | right; splits; [ reflexivity | assumption ] ].
 simpl; auto.
 apply red_not_value in H9; simpl in H9; intuition.
 apply red_not_value in H8; simpl in H8; intuition.
Qed.


Lemma fork_tau_behave_ec : forall (expr5 e  : expr) (lab : label), tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr  ( expr5) ))
          (E_live_expr (E_comp lab))) e -> (exists ( e' : expr),tauRed expr5 e' /\ ((  e = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e')))
          (E_live_expr  (E_comp lab))))\/(e = E_live_expr
       ( (E_taggingleft (E_pair e' (E_live_expr (E_comp lab))))) /\ is_value_of_expr e'))) .
Proof.
  intros.
  assert (
   (fun a b => 

    ((exists (expr5 : expr) (lab : label), 
         a= (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( expr5))) (E_live_expr  (E_comp lab))) ) 
          -> 
        (exists (expr5 : expr) (lab : label), 
           a=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( expr5))) (E_live_expr  (E_comp lab))) 
           /\ (exists ( e' : expr),tauRed expr5 e' /\
                 (
                  (
                   (b = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e'))) (E_live_expr (E_comp lab))))
                    \/
                   (b = E_live_expr ( (E_taggingleft (E_pair e' (E_live_expr (E_comp lab))))) /\ is_value_of_expr e')
                  )       
                 )
               )
        )
    )) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( expr5) ))
         (E_live_expr  (E_comp lab))) e
  ).
  apply fork_tau_behave_ec_h.
  assumption.
  simpl in H0.
  destruct H0.
  exists expr5 lab; reflexivity.
  destruct H0.
  intuition.
  simplify_eq H1; clear H1; intros; substs.
  assumption.
Qed.

Lemma fork_tau_swap_ec : forall (expr5 e  : expr) (lab : label), tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr  ( expr5) ))
          (E_live_expr (E_comp lab))) e -> (exists ( e' : expr),tauRed expr5 e' /\ ((  e = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e')))
          (E_live_expr  (E_comp lab))) /\ tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr   (E_comp lab)))
          (E_live_expr  ( expr5))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr   (E_comp lab)))
          (E_live_expr  ( e')))  )\/(e = E_live_expr
       ( (E_taggingleft (E_pair e' (E_live_expr (E_comp lab))))) /\ is_value_of_expr e' /\ tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr   (E_comp lab)))
          (E_live_expr  ( expr5))) (E_live_expr
       ( (E_taggingright (E_pair (E_live_expr (E_comp lab)) e')))) ))) .
Proof.
intros.
 apply fork_tau_behave_ec in H.
 intuition.
 destruct H.
 intuition.
 substs.
 exists x.
 intuition.
 left.
 intuition.
 apply fork_tau_ce_push_h.
 assumption.
 substs.
 exists x.
 intuition.
 right.
 intuition. 
 assert (tauRed
  (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab)))
     (E_live_expr ( expr5)))  (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab)))
     (E_live_expr ( x)))).
 apply fork_tau_ce_push_h.
 assumption.
 apply star_S with (y:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab)))
         (E_live_expr ( x)))).
 assumption.
 apply tStep with (s:=S_Second).
 apply JO_red_forkdeath2.
 assumption.
Qed.


Lemma fork_label_origin_ce : forall (expr5 e : expr) (lab l : label), labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab)))
          (E_live_expr ( expr5))) e -> ((l=lab) \/ (exists (e' : expr), labRed l expr5 e')).
Proof.
 intros.
 inversion H; intuition; substs.
 apply fork_tau_behave_ce in H4.
 substs.
 destruct H4.
 intuition.
 substs.
 inversion H0.
 substs.
 right.
 exists e''.
 apply lab_r with (e1:=x)(e2:=e'')(s:=s0).
 splits; [assumption | assumption | apply star_refl ].
 substs.
 left; reflexivity.
 apply red_not_value in H9; simpl in H9; intuition.
 apply red_not_value in H8; simpl in H8; intuition.
 substs.
 apply red_not_value in H0; simpl in H0; intuition.
Qed.

Lemma fork_label_behave_ce : forall (expr5 e : expr) (lab l : label), labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab)))
          (E_live_expr ( expr5))) e -> (
           ((l=lab) /\ (exists (e' : expr), tauRed expr5 e' /\ e=(E_live_expr ( (E_taggingleft (E_pair (E_constant (CONST_unit)) (E_live_expr ( e'))))))))
           \/
           ( (exists (e' : expr), labRed l expr5 e' /\ e=((E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab)))
          (E_live_expr ( e'))))))
           \/
           ( (exists (e' : expr), labRed l expr5 e' /\ e=(E_live_expr ( (E_taggingright (E_pair (E_live_expr (E_comp lab)) e')))) /\ is_value_of_expr e'))
          ).
Proof.
 intros.
 inversion H; intuition; substs.
 apply fork_tau_behave_ce in H4.
 substs.
 destruct H4.
 intuition.
 substs.
 inversion H0.
 substs.
 right.
 apply fork_tau_behave_ce in H6.
 substs.
 destruct H6.
 intuition.
 substs.
 left.
 exists x0.
 splits.
 apply lab_r with (e1:=x)(e2:=e'')(s:=s0).
 splits; [assumption | assumption | assumption ]. 
 reflexivity.
 substs.
 right.
 exists x0.
 splits.
 apply lab_r with (e1:=x)(e2:=e'')(s:=s0).
 splits; [assumption | assumption | assumption ]. 
 reflexivity.
 assumption.
 substs.
 left.
 splits.
 reflexivity.
 apply taured_val_id in H6; substs.
 exists x.
 splits; [assumption | reflexivity ].
 simpl; auto.
 apply red_not_value in H9; simpl in H9; intuition.
 apply red_not_value in H8; simpl in H8; intuition.
 substs.
 apply red_not_value in H0; simpl in H0; intuition.
Qed.

Lemma fork_label_swap_ec_ce : forall (expr5 e : expr) (lab l : label), labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab)))
          (E_live_expr ( expr5))) e -> (
           ((l=lab) /\ (exists (e' : expr), tauRed expr5 e' /\ e=(E_live_expr ( (E_taggingleft (E_pair (E_constant (CONST_unit)) (E_live_expr ( e')))))) /\
               labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( expr5)))
          (E_live_expr (E_comp lab))) (E_live_expr ( (E_taggingright (E_pair  (E_live_expr ( e')) (E_constant (CONST_unit))))))
                ))
           \/
           ( (exists (e' : expr), labRed l expr5 e' /\ e=((E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab)))
          (E_live_expr ( e')))) /\ labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( expr5)))
          (E_live_expr (E_comp lab))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e')))
          (E_live_expr (E_comp lab)))))
           \/
           ( (exists (e' : expr), labRed l expr5 e' /\ e=(E_live_expr ( (E_taggingright (E_pair (E_live_expr (E_comp lab)) e')))) /\ is_value_of_expr e' /\
             labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( expr5)))
          (E_live_expr (E_comp lab))) (E_live_expr ( (E_taggingleft (E_pair  e' (E_live_expr (E_comp lab))))))
           ))
          ).
Proof.
 intros.
 apply  fork_label_behave_ce in H.
 intuition.
 left.
 substs.
 destruct H1.
 intuition.
 substs.
 exists x.
 splits. assumption. reflexivity.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x)))
     (E_live_expr (E_comp lab))))(e2:=(E_live_expr
     (
        (E_taggingright
           (E_pair (E_live_expr ( x)) (E_constant CONST_unit))))))(s:=S_Second).
 splits.
 apply fork_tau_ec_push_h.
 assumption.
 apply JO_red_forkdocomp2.
 apply star_refl.
 right.
 left.
 destruct H.
 intuition; substs.
 exists x.
 splits.
 assumption.
 reflexivity.
 destruct H0.
 intuition.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e1)))
     (E_live_expr (E_comp lab))))(e2:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e2)))
     (E_live_expr (E_comp lab))))(s:=S_First).
 splits.
 apply fork_tau_ec_push_h.
 assumption.
 apply JO_red_forkmove1 with (s:=s).
 assumption.
 apply fork_tau_ec_push_h.
 assumption.
 right.
 right.
 destruct H.
 intuition.
 exists x.
 substs.
 splits.
 assumption.
 reflexivity.
 assumption.
 destruct H0.
 intuition.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e1)))
     (E_live_expr (E_comp lab))))(e2:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e2)))
     (E_live_expr (E_comp lab))))(s:=S_First).
 splits.
 apply fork_tau_ec_push_h.
 assumption.
 apply JO_red_forkmove1 with (s:=s).
 assumption.
 apply star_trans with (y:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e3)))
     (E_live_expr (E_comp lab)))).
 apply fork_tau_ec_push_h.
 assumption.
 apply S_star with (y:=(E_live_expr
     ( (E_taggingleft (E_pair e3 (E_live_expr (E_comp lab))))))).
 apply tStep with (s:=S_First).
 apply JO_red_forkdeath1.
 assumption.
 apply star_refl.
Qed.

Lemma fork_label_origin_ec : forall (expr5 e : expr) (lab l : label), labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( expr5)))
          (E_live_expr  (E_comp lab))) e -> ((l=lab) \/ (exists (e' : expr), labRed l expr5 e')).
Proof.
 intros.
 inversion H; intuition; substs.
 apply fork_tau_behave_ec in H4.
 substs.
 destruct H4.
 intuition.
 substs.
 inversion H0.
 substs.
 right.
 exists e''.
 apply lab_r with (e1:=x)(e2:=e'')(s:=s0).
 splits; [assumption | assumption | apply star_refl ].
 substs.
 left; reflexivity.
 apply red_not_value in H9; simpl in H9; intuition.
 apply red_not_value in H8; simpl in H8; intuition.
 substs.
 apply red_not_value in H0; simpl in H0; intuition.
Qed.


Lemma fork_label_behave_ec : forall (expr5 e : expr) (lab l : label), labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( expr5)))
          (E_live_expr  (E_comp lab))) e -> (
           ((l=lab) /\ (exists (e' : expr), tauRed expr5 e' /\ e=(E_live_expr ( (E_taggingright (E_pair  (E_live_expr ( e')) (E_constant (CONST_unit))))))))
           \/
           ( (exists (e' : expr), labRed l expr5 e' /\ e=((E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e')))
          (E_live_expr  (E_comp lab))))))
           \/
           ( (exists (e' : expr), labRed l expr5 e' /\ e=(E_live_expr ( (E_taggingleft (E_pair  e' (E_live_expr (E_comp lab)))))) /\ is_value_of_expr e'))
          ).
Proof.
 intros.
 inversion H; intuition; substs.
 apply fork_tau_behave_ec in H4.
 substs.
 destruct H4.
 intuition.
 substs.
 inversion H0.
 substs.
 right.
 apply fork_tau_behave_ec in H6.
 substs.
 destruct H6.
 intuition.
 substs.
 left.
 exists x0.
 splits.
 apply lab_r with (e1:=x)(e2:=e'')(s:=s0).
 splits; [assumption | assumption | assumption ]. 
 reflexivity.
 substs.
 right.
 exists x0.
 splits.
 apply lab_r with (e1:=x)(e2:=e'')(s:=s0).
 splits; [assumption | assumption | assumption ]. 
 reflexivity.
 assumption.
 substs.
 left.
 splits.
 reflexivity.
 apply taured_val_id in H6; substs.
 exists x.
 splits; [assumption | reflexivity ].
 simpl; auto.
 apply red_not_value in H9; simpl in H9; intuition.
 apply red_not_value in H8; simpl in H8; intuition.
 substs.
 apply red_not_value in H0; simpl in H0; intuition.
Qed.

Lemma fork_label_swap_ce_ec : forall (expr5 e : expr) (lab l : label), labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( expr5)))
          (E_live_expr (E_comp lab)))  e -> (
           ((l=lab) /\ (exists (e' : expr), tauRed expr5 e' /\ e= (E_live_expr ( (E_taggingright (E_pair  (E_live_expr ( e')) (E_constant (CONST_unit)))))) /\
               labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab)))
          (E_live_expr ( expr5))) (E_live_expr ( (E_taggingleft (E_pair (E_constant (CONST_unit)) (E_live_expr ( e'))))))
 
                ))
           \/
           ( (exists (e' : expr), labRed l expr5 e' /\ e= (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e'))) (E_live_expr (E_comp lab))) /\ labRed l 
(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab)))
          (E_live_expr ( expr5))) ((E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab)))
          (E_live_expr ( e'))))  ))
           \/
           ( (exists (e' : expr), labRed l expr5 e' /\ e= (E_live_expr ( (E_taggingleft (E_pair  e' (E_live_expr (E_comp lab)))))) /\ is_value_of_expr e' /\
             labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab)))
          (E_live_expr ( expr5)))  (E_live_expr ( (E_taggingright (E_pair (E_live_expr (E_comp lab)) e'))))
           ))
          ).
Proof.
 intros.
 apply  fork_label_behave_ec in H.
 intuition.
 left.
 substs.
 destruct H1.
 intuition.
 substs.
 exists x.
 splits. assumption. reflexivity.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab)))
     (E_live_expr ( x))))(e2:=(E_live_expr
     (
        (E_taggingleft
           (E_pair  (E_constant CONST_unit) (E_live_expr ( x)))))))(s:=S_First).
 splits.
 apply fork_tau_ce_push_h.
 assumption.
 apply JO_red_forkdocomp1.
 apply star_refl.
 right.
 left.
 destruct H.
 intuition; substs.
 exists x.
 splits.
 assumption.
 reflexivity.
 destruct H0.
 intuition.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab)))
     (E_live_expr  ( e1))))(e2:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab)))
     (E_live_expr  ( e2))))(s:=S_Second).
 splits.
 apply fork_tau_ce_push_h.
 assumption.
 apply JO_red_forkmove2 with (s:=s).
 assumption.
 apply fork_tau_ce_push_h.
 assumption.
 right.
 right.
 destruct H.
 intuition.
 exists x.
 substs.
 splits.
 assumption.
 reflexivity.
 assumption.
 destruct H0.
 intuition.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab)))
     (E_live_expr  ( e1))))(e2:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab)))
     (E_live_expr  ( e2))))(s:=S_Second).
 splits.
 apply fork_tau_ce_push_h.
 assumption.
 apply JO_red_forkmove2 with (s:=s).
 assumption.
 apply star_trans with (y:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab)))
     (E_live_expr  ( e3)))).
 apply fork_tau_ce_push_h.
 assumption.
 apply S_star with (y:=(E_live_expr
     ( (E_taggingright (E_pair (E_live_expr (E_comp lab)) e3))))).
 apply tStep with (s:=S_Second).
 apply JO_red_forkdeath2.
 assumption.
 apply star_refl.
Qed.



Lemma fork_tau_behave_cc : forall (e : expr) (lab1 lab2 : label), tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab1))) (E_live_expr (E_comp lab2))) e -> e= (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab1))) (E_live_expr (E_comp lab2))).
Proof.
 intros.
 inversion H.
 reflexivity.
 substs.
 inversion H0.
 substs.
 inversion H2.
 substs.
  apply red_not_value in H9; simpl in H9; intuition.
 apply red_not_value in H8; simpl in H8; intuition.
Qed.

Lemma fork_tau_swap_cc : forall (e : expr) (lab1 lab2 : label), tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab1))) (E_live_expr (E_comp lab2))) e -> (e= (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab1))) (E_live_expr (E_comp lab2)))
 /\ tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab2))) (E_live_expr (E_comp lab1))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab2))) (E_live_expr (E_comp lab1)))
).
Proof.
 intros.
 apply fork_tau_behave_cc in H.
 substs.
 intuition.
 apply star_refl.
Qed.

Lemma fork_label_origin_cc : forall (e : expr) (lab1 lab2 l : label), labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab1))) (E_live_expr (E_comp lab2))) e -> 
((l=lab1 /\ e = (E_live_expr
       (
          (E_taggingleft
             (E_pair (E_constant CONST_unit) (E_live_expr (E_comp lab2))))))) 
 \/ (l=lab2 /\ e =((E_live_expr
          (
             (E_taggingright
                (E_pair (E_live_expr (E_comp lab1)) (E_constant CONST_unit)))))) )).
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
 apply red_not_value in H9; simpl in H9; intuition.
 apply red_not_value in H8; simpl in H8; intuition.
 inversion H1; intuition; substs.
 inversion H3; intuition; substs.
 apply red_not_value in H12; simpl in H12; intuition.
 apply red_not_value in H11; simpl in H11; intuition.
Qed.

Lemma fork_label_swap_cc : forall (e : expr) (lab1 lab2 l : label), labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab1))) (E_live_expr (E_comp lab2))) e -> 
((l=lab1 /\ e = (E_live_expr
       (
          (E_taggingleft
             (E_pair (E_constant CONST_unit) (E_live_expr (E_comp lab2)))))) /\  
          labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab2))) (E_live_expr (E_comp lab1))) 
                ((E_live_expr
          (
             (E_taggingright
                (E_pair (E_live_expr (E_comp lab2)) (E_constant CONST_unit))))))
               ) 
 \/ (l=lab2 /\ e =((E_live_expr
          (
             (E_taggingright
                (E_pair (E_live_expr (E_comp lab1)) (E_constant CONST_unit)))))) /\
                labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab2))) (E_live_expr (E_comp lab1))) 
                    (E_live_expr
       (
          (E_taggingleft
             (E_pair (E_constant CONST_unit) (E_live_expr (E_comp lab1))))))
                )).
Proof.
 intros.
 inversion H; intuition; substs.
 inversion H4; intuition; substs.
 inversion H0; intuition; substs.
 left. splits. reflexivity.
 inversion H6. reflexivity. substs. inversion H1. substs.
 inversion H3.
 apply taured_val_id in H6; substs.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp lab2)))
     (E_live_expr (E_comp l))))(e2:=(E_live_expr
     (
        (E_taggingright
           (E_pair (E_live_expr (E_comp lab2)) (E_constant CONST_unit))))))(s:=S_Second).
 splits; [apply star_refl | apply JO_red_forkdocomp2 | apply star_refl].
 simpl; auto.
 right.
 splits. reflexivity.
 apply taured_val_id in H6.
 substs.
 reflexivity.
 simpl; auto.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp l)))
     (E_live_expr (E_comp lab1))))(e2:=(E_live_expr
     (
        (E_taggingleft
           (E_pair (E_constant CONST_unit) (E_live_expr (E_comp lab1)))))))(s:=S_First).
 splits; [apply star_refl | apply JO_red_forkdocomp1 | apply star_refl].
 apply red_not_value in H9; simpl in H9; intuition.
 apply red_not_value in H8; simpl in H8; intuition.
 inversion H1; intuition; substs.
 inversion H3; intuition; substs.
 apply red_not_value in H12; simpl in H12; intuition.
 apply red_not_value in H11; simpl in H11; intuition.
Qed.



(*

Lemma fork_tau_serialise1 : forall (p q p' q': expr), tauRed
       (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( p)))
          (E_live_expr ( q)))
       (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( p')))
          (E_live_expr ( q'))) -> tauRed
       (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( p)))
          (E_live_expr ( q)))
       (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( p')))
          (E_live_expr ( q))).
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
Lemma fork_label_origin_ee : forall (e' e e'' : expr) (l : label), labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e)) ) (E_live_expr ( e'))) e'' -> 
 ((exists (f : expr), labRed l e f /\ (
((exists ( q' : expr), tauRed e' q' /\ e'' = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( f)) ) (E_live_expr ( q')))) \/ 
  ((exists ( vq : expr), is_value_of_expr vq /\ tauRed e' vq /\ e'' = ((E_live_expr (  (  (E_taggingright  (E_pair  (E_live_expr ( f)) vq ) ) ) )))) \/ 
  (
   (exists ( q' : expr), is_value_of_expr f /\  tauRed e' q' /\ e''=((E_live_expr (  (E_taggingleft  (  (E_pair f (E_live_expr ( q'))  ) ) ) )))))))

)) 


\/ 
  (exists (f : expr), labRed l e' f /\ (
((exists (p'  : expr), tauRed e p' /\ e'' = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( p')) ) (E_live_expr ( f)))) \/ 
  ((exists (p'  : expr), is_value_of_expr f /\ tauRed e p'  /\ e'' = ((E_live_expr (  (  (E_taggingright  (E_pair  (E_live_expr ( p')) f ) ) ) )))) \/ 
  (
   (exists (vp : expr), is_value_of_expr vp /\ tauRed e vp  /\ e''=((E_live_expr (  (E_taggingleft  (  (E_pair vp (E_live_expr ( f))  ) ) ) ))))))) 

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
 

 apply red_not_value in H10; simpl in H10; intuition.
 substs.
 apply red_not_value in H9; simpl in H9; intuition.
 substs.
 elim H2; intros; clear H2.
 apply red_not_value in H1.
 destruct H0.
 destruct H0; destruct H0; intuition; substs; simpl in H1; intuition. 
 destruct H0.
 destruct H0; destruct H0; intuition; substs; simpl in H1; intuition.
Qed.

Lemma fork_label_swap_ee : forall (e' e e'' : expr) (l : label), labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e)) ) (E_live_expr ( e'))) e'' -> 
 ((exists (f : expr), labRed l e f /\ (
((exists ( q' : expr), tauRed e' q' /\ e'' = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( f)) ) (E_live_expr ( q'))) /\
   labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e')) ) (E_live_expr ( e)))  (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( q')) ) (E_live_expr ( f)))
   ) \/ 
  ((exists ( vq : expr), is_value_of_expr vq /\ tauRed e' vq /\ e'' = ((E_live_expr (  (  (E_taggingright  (E_pair  (E_live_expr ( f)) vq ) ) ) ))) /\
    labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e')) ) (E_live_expr ( e))) ((E_live_expr (  (E_taggingleft  (  (E_pair vq (E_live_expr ( f))  ) ) ) )))
  ) \/ 
  (
   (exists ( q' : expr), is_value_of_expr f /\  tauRed e' q' /\ e''=((E_live_expr (  (E_taggingleft  (  (E_pair f (E_live_expr ( q'))  ) ) ) ))) /\
     labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e')) ) (E_live_expr ( e))) ((E_live_expr (  (  (E_taggingright  (E_pair  (E_live_expr ( q')) f ) ) ) )))
   ))))

)) 


\/ 
  (exists (f : expr), labRed l e' f /\ (
((exists (p'  : expr), tauRed e p' /\ e'' = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( p')) ) (E_live_expr ( f)))  /\
 labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e')) ) (E_live_expr ( e))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( f)) ) (E_live_expr ( p')))
 ) \/ 
  ((exists (p'  : expr), is_value_of_expr f /\ tauRed e p'  /\ e'' = ((E_live_expr (  (  (E_taggingright  (E_pair  (E_live_expr ( p')) f ) ) ) )))  /\
   labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e')) ) (E_live_expr ( e))) ((E_live_expr (  (E_taggingleft  (  (E_pair f (E_live_expr ( p'))  ) ) ) )))
  ) \/ 
  (
   (exists (vp : expr), is_value_of_expr vp /\ tauRed e vp  /\ e''=((E_live_expr (  (E_taggingleft  (  (E_pair vp (E_live_expr ( f))  ) ) ) ))) /\
    labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e')) ) (E_live_expr ( e)))  ((E_live_expr (  (  (E_taggingright  (E_pair  (E_live_expr ( f)) vp ) ) ) )))
   )))) 

))).
Proof.
 intros.
 apply fork_label_origin_ee in H.
 intuition.
 destruct H0.
 left.
 exists x.
 intuition.
 destruct H.
 left. 
 exists x0.
 intuition.
 substs.
 apply fork_lab_push_ee_full2.
 assumption.
 assumption.
 right.
 left.
 destruct H1.
 exists x0.
 intuition.
 substs.
 assert (labRed l
  (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e')))
     (E_live_expr ( e))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x0)))
     (E_live_expr ( x)))).
 apply fork_lab_push_ee_full2.
 assumption.
 assumption.
 inversion H2.
 intuition.
 substs.
 apply lab_r with (e1:=e1)(e2:=e2)(s:=s).
 intuition.
 apply star_S with (y:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x0)))
          (E_live_expr ( x)))).
 assumption.
 apply tStep with (s:=S_First).
 apply JO_red_forkdeath1.
 assumption.
 right.
 right.
 destruct H1.
 exists x0.
 intuition.
 substs.
 assert (labRed l
  (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e')))
     (E_live_expr ( e))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x0)))
     (E_live_expr ( x)))).
 apply fork_lab_push_ee_full2.
 assumption.
 assumption.
 inversion H2.
 intuition.
 substs.
 apply lab_r with (e1:=e1)(e2:=e2)(s:=s).
 intuition.
 apply star_S with (y:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x0)))
          (E_live_expr ( x)))).
 assumption.
 apply tStep with (s:=S_Second).
 apply JO_red_forkdeath2.
 assumption.


 right.
 destruct H0.
 exists x.
 intuition.
 destruct H.
 left. 
 exists x0.
 intuition.
 substs.
 apply fork_lab_push_ee_full1.
 assumption.
 assumption.
 right.
 left.
 destruct H1.
 exists x0.
 intuition.
 substs.
 assert (labRed l
  (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e')))
     (E_live_expr ( e))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x)))
     (E_live_expr ( x0)))).
 apply fork_lab_push_ee_full1.
 assumption.
 assumption.
 inversion H2.
 intuition.
 substs.
 apply lab_r with (e1:=e1)(e2:=e2)(s:=s).
 intuition.
 apply star_S with (y:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x)))
          (E_live_expr ( x0)))).
 assumption.
 apply tStep with (s:=S_First).
 apply JO_red_forkdeath1.
 assumption.
 right.
 right.
 destruct H1.
 exists x0.
 intuition.
 substs.
 assert (labRed l
  (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e')))
     (E_live_expr ( e))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x)))
     (E_live_expr ( x0)))).
 apply fork_lab_push_ee_full1.
 assumption.
 assumption.
 inversion H2.
 intuition.
 substs.
 apply lab_r with (e1:=e1)(e2:=e2)(s:=s).
 intuition.
 apply star_S with (y:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x)))
          (E_live_expr ( x0)))).
 assumption.
 apply tStep with (s:=S_Second).
 apply JO_red_forkdeath2.
 assumption.
Qed. 

Lemma fork_tau_swap_total : forall (p q : livemodes) (e : expr) , tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p))) (E_live_expr ( q))) e ->
        (
         ((exists (p' q' : livemodes), e = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p'))) (E_live_expr ( q'))) /\
              tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (q)))(E_live_expr ( p))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (q'))) (E_live_expr ( p')))
          )
          )
             
          \/
         (
            (exists (p' : expr) (q': livemodes),is_value_of_expr p' /\ e= ((E_live_expr (  (E_taggingleft  (  (E_pair p' (E_live_expr (q'))  ) ) ) ))) /\ 
              tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (q)))(E_live_expr ( p))) ((E_live_expr (  (E_taggingright  (  (E_pair (E_live_expr (q')) p'  ) ) ) )))
             )
            \/
            ((exists (q' : expr) (p': livemodes),is_value_of_expr q' /\ e= ((E_live_expr (  (E_taggingright  (  (E_pair (E_live_expr (p')) q' ) ) ) ))) /\ 
              tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (q)))(E_live_expr ( p))) ((E_live_expr (  (E_taggingleft  (  (E_pair q' (E_live_expr (p')) ) ) ) ))) 
             )
            )
          )
        ).
Proof.
 intros.
 induction p; induction q.
 apply fork_tau_swap_cc in H.
 intuition.
 substs.
 left.
 exists (E_comp lab) (E_comp lab0).
 intuition.
 apply fork_tau_swap_ce in H.
 intuition.
 destruct H.
 intuition.
 substs.
 left.
 exists (E_comp lab) ( x).
 intuition.
 substs.
 right.
 right.
 exists  x (E_comp lab) .
 intuition.
 apply fork_tau_swap_ec in H.
 intuition.
 destruct H.
 intuition.
 substs.
 left.
 exists  ( x) (E_comp lab).
 intuition.
 substs.
 right.
 left.
 exists  x (E_comp lab) .
 intuition.
 apply fork_tau_swap_ee in H.
 intuition.
 destruct H0.
 destruct H.
 intuition.
 substs.
 left.
 exists ( x)( x0).
 intuition.
 right.
 right.
 destruct H.
 destruct H.
 intuition.
 substs.
 exists x0 ( x).
 intuition.
 right.
 left.
 destruct H.
 destruct H.
 exists (x) ( x0).
 intuition.
Qed.

Lemma fork_tau_behave_total : forall (p q : livemodes) (e : expr) , tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p))) (E_live_expr ( q))) e ->
        (
         ((exists (p' q' : livemodes), e = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p'))) (E_live_expr ( q')))
          )
          )
             
          \/
         (
            (exists (p' : expr) (q': livemodes),is_value_of_expr p' /\ e= ((E_live_expr (  (E_taggingleft  (  (E_pair p' (E_live_expr (q'))  ) ) ) ))) 
             )
            \/
            ((exists (q' : expr) (p': livemodes),is_value_of_expr q' /\ e= ((E_live_expr (  (E_taggingright  (  (E_pair (E_live_expr (p')) q' ) ) ) ))) 
             )
            )
          )
        ).
Proof.
 intros.
 apply fork_tau_swap_total in H.
 intuition.
 left.
 destruct H0.
 destruct H.
 exists x x0.
 intuition.
 right.
 left.
 destruct H. destruct H.
 exists x x0.
 intuition.
 right; right.
 destruct H; destruct H.
 exists x x0.
 intuition.
Qed.

Lemma fork_label_swap_total : forall (p q : livemodes) (e : expr) (l : label), labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p))) (E_live_expr ( q))) e ->
        (
         ((exists (p' q' : livemodes), e = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p'))) (E_live_expr ( q'))) /\
              labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (q)))(E_live_expr ( p))) (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (q'))) (E_live_expr ( p')))
          )
          )
             
          \/
         (
            (exists (p' : expr) (q': livemodes),is_value_of_expr p' /\ e= ((E_live_expr (  (E_taggingleft  (  (E_pair p' (E_live_expr (q'))  ) ) ) ))) /\ 
              labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (q)))(E_live_expr ( p))) ((E_live_expr (  (E_taggingright  (  (E_pair (E_live_expr (q')) p'  ) ) ) )))
             )
            \/
            ((exists (q' : expr) (p': livemodes),is_value_of_expr q' /\ e= ((E_live_expr (  (E_taggingright  (  (E_pair (E_live_expr (p')) q' ) ) ) ))) /\ 
              labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (q)))(E_live_expr ( p))) ((E_live_expr (  (E_taggingleft  (  (E_pair q' (E_live_expr (p')) ) ) ) ))) 
             )
            )
          )
        ).
Proof.
 intros.
 induction p; induction q.
 apply fork_label_swap_cc in H.
 intuition.
 substs.
 right.
 left.
 exists (E_constant CONST_unit) (E_comp lab0).
 intuition.
 simpl; auto.
 substs.
 right.
 right.
 exists (E_constant CONST_unit) (E_comp lab).
 intuition.
 simpl; auto.
 apply fork_label_swap_ec_ce in H.
 intuition.
 destruct H1.
 substs.
 intuition.
 substs.
 right.
 left.
 exists (E_constant CONST_unit) ( x).
 intuition.
 simpl; auto.
 left.
 destruct H.
 intuition. substs.
 exists (E_comp lab) ( x).
 intuition.
 right.
 right.
 destruct H.
 intuition.
 substs.
 exists x (E_comp lab).
 intuition.
 apply fork_label_swap_ce_ec in H.
 intuition.
 destruct H1.
 substs.
 intuition.
 substs.
 right.
 right.
 exists (E_constant CONST_unit) ( x).
 intuition.
 simpl; auto.
 left.
 destruct H.
 intuition. substs.
 exists  ( x) (E_comp lab).
 intuition.
 right.
 left.
 destruct H.
 intuition.
 substs.
 exists x (E_comp lab).
 intuition.
 apply fork_label_swap_ee in H.
 intuition.
 destruct H0.
 intuition.
 destruct H.
 intuition.
 substs.
 left.
 exists ( x)( x0).
 intuition.
 right.
 right.
 destruct H1.
 intuition.
 substs.
 exists x0 ( x).
 intuition.
 right.
 left.
 destruct H1.
 exists (x) ( x0).
 intuition.
 destruct H0.
 intuition.
 destruct H.
 intuition.
 substs.
 left.
 exists ( x0)( x).
 intuition.
 right.
 right.
 destruct H1.
 intuition.
 substs.
 exists x ( x0).
 intuition.
 right.
 left.
 destruct H1.
 exists (x0) ( x).
 intuition.
Qed.
 
Lemma fork_lab_behave : forall (p q : livemodes) (e : expr) (l : label), labRed l (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p))) (E_live_expr ( q))) e ->
        (
         ((exists (p' q' : livemodes), e = (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p'))) (E_live_expr ( q'))) 
          )
          )
             
          \/
         (
            (exists (p' : expr) (q': livemodes),is_value_of_expr p' /\ e= ((E_live_expr (  (E_taggingleft  (  (E_pair p' (E_live_expr (q'))  ) ) ) ))) 
             )
            \/
            ((exists (q' : expr) (p': livemodes),is_value_of_expr q' /\ e= ((E_live_expr (  (E_taggingright  (  (E_pair (E_live_expr (p')) q' ) ) ) )))  
             )
            )
          )
        ).
Proof.
 intros.
 apply fork_label_swap_total in H.
 intuition.
 left.
 destruct H0.
 destruct H.
 exists x x0.
 intuition.
 right.
 left.
 destruct H. destruct H.
 exists x x0.
 intuition.
 right; right.
 destruct H; destruct H.
 exists x x0.
 intuition.
Qed.


Lemma bind_tau_behave_back_h : forall (x y : expr), tauRed x y -> ((fun x y => (exists (e e' : expr), x = (e >>= e') ) -> (exists (e e' : expr), x = (e >>= e') /\ ((exists (f : expr), tauRed e f /\ y = (f >>= e')) \/ (exists (f : expr), tauRed e (E_live_expr ( f)) /\ ((exists (f' : expr ), (tauRed f f' /\ y=(((E_live_expr ( f')))>>=e') ) \/ (tauRed f f' /\ is_value_of_expr f' /\ tauRed (E_apply e' f') y))))) )   ) x y). 
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
       tauRed e (E_live_expr ( f)) /\
       (exists f',
        tauRed f f' /\ z = E_live_expr ( f') >>= e'0 \/
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
     E_live_expr ( e') >>= x1 = e >>= e'0 /\
     ((exists f, tauRed e f /\ z = f >>= e'0) \/
      (exists f,
       tauRed e (E_live_expr ( f)) /\
       (exists f',
        tauRed f f' /\ z = E_live_expr ( f') >>= e'0 \/
        tauRed f f' /\ is_value_of_expr f' /\ tauRed (E_apply e'0 f') z)))).
 apply H1.
 exists (E_live_expr ( e')) (x1).
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

Lemma bind_lab_behave_back_h : forall (e e' y : expr) (l : label), labRed l (e >>= e') y -> 
   (( ( (
            (exists (f : expr), labRed l e f /\ tauRed (f >>= e') y)
            \/
            (exists (f : expr), tauRed e (E_live_expr ( f)) /\ 
               ((exists (f' : expr ), 
                  (labRed l f f' /\ tauRed (((E_live_expr ( f')))>>=e') y ) 
                   \/ 
                  (tauRed f f' /\ is_value_of_expr f' /\ labRed l (E_apply e' f') y)
                 )  
                )
            )
            \/
            (tauRed e (E_live_expr (E_comp l)) /\ tauRed (E_apply e' (E_constant CONST_unit)) y
            )
          ) )   )). 
Proof.
 intros.
 inversion H.
 intuition.
 apply bind_tau_behave_back_h in H4.
 destruct H4.
 destruct H4.
 intuition.
 substs.
 destruct H4.
 intuition.
 substs.
 simplify_eq H5; clear H5; intros; substs.
 inversion H0.
 substs.
 apply bind_tau_behave_back_h in H6.
 destruct H6.
 destruct H1.
 intuition.
 simplify_eq H3; clear H3; intros; substs.
 destruct H1.
 intuition.
 substs.
 left.
 exists x0.
 intuition.
 apply lab_r with (e1:=x1)(e2:=x2)(s:=s).
 intuition.
 apply star_refl.
 simplify_eq H3; clear H3; intros; substs.
 destruct H1.
 intuition.
 substs.
 destruct H4.
 intuition.
 substs.
 left.
 exists (E_live_expr ( x0)).
 intuition.
 apply lab_r with (e1:=x1)(e2:=x2)(s:=s).
 intuition.
 apply bind_tau_behave_front_boxed with (e':=x3) in H1.
 assumption.
 left.
 exists (E_live_expr ( x0)).
 intuition.
 apply lab_r with (e1:=x1)(e2:=x2)(s:=s).
 intuition.
 apply star_trans with (y:=(E_live_expr ( x4) >>= x3)).
 apply bind_tau_behave_front_boxed with (e':=x3) in H1.
 assumption.
 apply S_star with (y:=(E_apply x3 x4)).
 apply tStep with (s:=S_First).
 apply JO_red_dobind.
 assumption.
 assumption.
 exists e' x0.
 reflexivity.
 substs.
 right.
 left.
 exists e.
 splits.
 assumption.
 exists e'.
 left.
 intuition.
 apply lab_r with (e1:=e)(e2:=e')(s:=s).
 intuition.
 apply star_refl.
 apply star_refl.
 substs.
 right.
 right.
 intuition.
 simplify_eq H5; clear H5; intros; substs.
 destruct H4.
 intuition.
 destruct H3.
 intuition.
 substs.
 right.
 left.
 exists x1.
 intuition.
 inversion H0.
 apply red_not_value in H9; simpl in H9; intuition.
 substs.
 exists e'.
 left.
 intuition.
 apply lab_r with (e1:=x2)(e2:=e')(s:=s).
 intuition.
 apply star_refl.
 right.
  left.
 exists x1.
 intuition.
 exists x2.
 right.
 intuition.
 apply lab_r with (e1:=e1)(e2:=e2)(s:=s).
 intuition.
 substs.
 exists e e'.
 reflexivity.
Qed.




Lemma fork_swap_bind_lab_behave : forall (p q : livemodes) (e : expr) (l : label), labRed l ((E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( p)))
          (E_live_expr ( q))) >>= swapf) e ->
           (
            (exists (p' q' : livemodes), tauRed ((E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( p')))
          (E_live_expr ( q'))) >>= swapf) e /\  labRed l ((E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( p)))
          (E_live_expr ( q)))) ((E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( p')))
          (E_live_expr ( q')))))
            \/
            (exists (a : livemodes), labRed l ((E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( p)))
          (E_live_expr ( q)))) (E_live_expr a) /\ tauRed ((E_live_expr a) >>= swapf ) e)
           ).
Proof.
 intros.
 apply bind_lab_behave_back_h in H.
 intuition.
 destruct H0.
 intuition.
 assert (K:=H0).
 apply fork_label_swap_total in H0.
 intuition.
 destruct H.
 destruct H.
 intuition.
 substs.
 left.
 exists x0 x1.
 intuition.
 destruct H0.
 destruct H.
 intuition.
 substs.
 right.
 exists ( (E_taggingleft (E_pair x0 (E_live_expr x1)))).
 intuition.
 destruct H0.
 destruct H.
 intuition.
 substs.
 right.
 exists ( (E_taggingright (E_pair (E_live_expr x1) x0))).
 intuition.
 destruct H.
 intuition.
 destruct H1.
 intuition.
 induction p; induction q.
 apply fork_tau_behave_cc in H0.
 discriminate H0.
 apply fork_tau_behave_ce in H0.
 intuition.
 destruct H0.
 intuition.
 discriminate H0.
 simplify_eq H3; clear H3; intros; substs.
 apply labred_not_val in H.
 simpl in H; intuition.
 apply fork_tau_behave_ec in H0.
 intuition.
 destruct H0.
 intuition.
 discriminate H0.
 simplify_eq H3; clear H3; intros; substs.
 apply labred_not_val in H.
 simpl in H; intuition.
 apply fork_tau_behave_ee in H0.
 intuition.
 destruct H1.
 destruct H0.
 intuition.
 discriminate H4.
 destruct H0.
 destruct H0.
 intuition.
 simplify_eq H5; clear H5; intros; substs.
 apply labred_not_val in H.
 simpl in H; intuition.
 destruct H0.
 destruct H0.
 intuition.
 simplify_eq H5; clear H5; intros; substs.
 apply labred_not_val in H.
 simpl in H; intuition.
 
 induction p; induction q.
 apply fork_tau_behave_cc in H0.
 discriminate H0.
 apply fork_tau_behave_ce in H0.
 intuition.
 destruct H0.
 intuition.
 discriminate H0.
 simplify_eq H4; clear H4; intros; substs.
 apply taured_val_id in H.
 substs.
 assert (totalTauRed ( E_apply (swapf) (E_taggingright (( E_pair (E_live_expr (E_comp lab)) x1 )) ) ) (E_live_expr((E_taggingleft( ( ( E_pair x1 (E_live_expr (E_comp lab)) )) ))))).
 apply swapf_right.
 simpl; auto.
 assumption.
 assert (~(labRed l
       (E_apply swapf
          (E_taggingright (E_pair (E_live_expr (E_comp lab)) x1))) e)).
 apply ttr_val_not_labred with (v:=(E_live_expr
         ( (E_taggingleft (E_pair x1 (E_live_expr (E_comp lab))))))).
 intuition.
 simpl; auto.
 intuition.
 simpl; auto.
 apply fork_tau_behave_ec in H0.
 intuition.
 destruct H0.
 intuition.
 discriminate H0.
 simplify_eq H4; clear H4; intros; substs.
 apply taured_val_id in H.
 substs.
 assert (totalTauRed ( E_apply (swapf) (E_taggingleft (( E_pair x1 (E_live_expr (E_comp lab)) )) ) ) (E_live_expr((E_taggingright( ( ( E_pair (E_live_expr (E_comp lab)) x1 )) ))))).
 apply swapf_left.
 simpl; auto.
 simpl; auto.
 assert (~(labRed l
       (E_apply swapf (E_taggingleft (E_pair x1 (E_live_expr (E_comp lab)))))
       e)).
 apply ttr_val_not_labred with (v:=((E_live_expr
         ( (E_taggingright (E_pair (E_live_expr (E_comp lab)) x1)))))).
 intuition.
 simpl; auto.
 intuition.
 simpl; auto.
 apply fork_tau_behave_ee in H0.
 intuition.
 destruct H2.
 destruct H0.
 intuition.
 discriminate H5.
 destruct H0.
 destruct H0.
 intuition.
 simplify_eq H6; clear H6; intros; substs.
 apply taured_val_id in H.
 substs.
 assert (totalTauRed ( E_apply (swapf) (E_taggingright (( E_pair (E_live_expr ( x1)) x2 )) ) ) (E_live_expr((E_taggingleft( ( ( E_pair x2 (E_live_expr ( x1)) )) ))))).
 apply swapf_right.
 simpl; auto.
 assumption.
 assert (~(labRed l
       (E_apply swapf (E_taggingright (E_pair (E_live_expr ( x1)) x2)))
       e)).
 apply ttr_val_not_labred with (v:=((E_live_expr
         ( (E_taggingleft (E_pair x2 (E_live_expr ( x1)))))))).
 intuition.
 simpl; auto.
 intuition.
 simpl; auto.
 destruct H0.
 destruct H0.
 intuition.
 simplify_eq H6; clear H6; intros; substs.
 apply taured_val_id in H.
 substs.
 assert (totalTauRed ( E_apply (swapf) (E_taggingleft (( E_pair x1 (E_live_expr ( x2)) )) ) ) (E_live_expr((E_taggingright( ( ( E_pair (E_live_expr ( x2)) x1 )) ))))).
 apply swapf_left.
 simpl; auto.
 simpl; auto.
 assert (~(labRed l
       (E_apply swapf (E_taggingleft (E_pair x1 (E_live_expr ( x2)))))
       e)).
 apply ttr_val_not_labred with (v:=((E_live_expr
         ( (E_taggingright (E_pair (E_live_expr ( x2)) x1)))))).
 intuition.
 simpl; auto.
 intuition.
 simpl; auto.
 
 induction p; induction q.
 apply fork_tau_behave_cc in H0.
 discriminate H0.
 apply fork_tau_behave_ce in H0.
 intuition.
 destruct H0.
 intuition.
 discriminate H.
 discriminate H2.
 apply fork_tau_behave_ec in H0.
 intuition.
 destruct H0.
 intuition.
 discriminate H.
 discriminate H2.
 apply fork_tau_behave_ee in H0.
 intuition.
 destruct H.
 destruct H.
 intuition.
 discriminate H3.
 destruct H0.
 destruct H.
 intuition.
 discriminate H4.
 destruct H0.
 destruct H.
 intuition.
 discriminate H4.
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




(*
Lemma fork_tau_swap_ee_non_val : forall (p q p' q': expr), (~ (is_value_of_expr p)) -> (~(is_value_of_expr q)) ->  (~ (is_value_of_expr p')) -> (~(is_value_of_expr q')) ->  tauRed
       (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( p)))
          (E_live_expr ( q)))
       (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( p')))
          (E_live_expr ( q'))) -> tauRed
       (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( q)))
          (E_live_expr ( p)))
       (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( q')))
          (E_live_expr ( p'))).
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
     E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e'')))
       (E_live_expr (x1)) =
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
 exists ( e'') (x1) x2 x3.
 splits; [reflexivity | reflexivity].
 destruct H3. destruct H3; destruct H3; destruct H3.
 intuition.
 simplify_eq H4.
 simplify_eq H3.
 intros.
 substs.
 clear H3.
 clear H4.
 apply S_star with (y:=((E_apply (E_apply (E_constant CONST_fork) (E_live_expr (x0)))
          (E_live_expr ( e''))))).
 apply tStep with (s:=S_Second).
 apply JO_red_forkmove2 with (s:=s0).
 intuition.
 assumption.
 substs.
 assert (exists p q p' q',
     E_apply (E_apply (E_constant CONST_fork) (E_live_expr x0))
       (E_live_expr ( e'')) =
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
 exists (x0) ( e'') x2 x3.
 splits; [reflexivity | reflexivity ].
 destruct H3; destruct H3; destruct H3; destruct H3.
 intuition.
 substs.
 simplify_eq H4; simplify_eq H3; intros; substs; clear H4; clear H3.
 apply S_star with (y:=((E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e'')))
     (E_live_expr (x))))).
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
 apply fork_label_swap_ec_ce in H.
 intuition.
 destruct H4; intuition.
 discriminate H2.
 destruct H; intuition.
 simplify_eq H; clear H; intros; substs.
 assumption.
 destruct H.
 intuition.
 discriminate H.
 induction q.
 substs. 
 apply fork_label_swap_ce_ec in H.
 intuition.
 destruct H4; intuition.
 discriminate H2.
 destruct H; intuition.
 simplify_eq H; clear H; intros; substs.
 assumption.
 destruct H.
 intuition.
 discriminate H.
 assert (K:=H1).
 apply fork_tau_behave_ee in H1.
 intuition.
 destruct H2. destruct H1.
 intuition.
 substs.
 inversion H0.
 substs.
  apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x0)))
       (E_live_expr ( x))))(e2:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x0)))
       (E_live_expr ( e''))))(s:=S_Second).
 substs.
 splits.
 apply fork_comm_taured.
 assumption.
 apply JO_red_forkmove2 with (s:=s0).
 assumption.
 apply fork_comm_taured.
 assumption.
 substs.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x0)))
       (E_live_expr ( x))))(e2:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e'')))
       (E_live_expr ( x))))(s:=S_First).
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
 exists ((
     (E_taggingleft
        (E_pair (E_constant CONST_unit) (E_live_expr (E_comp lab0)))))).
 reflexivity.
 exists (E_comp l) (E_comp lab0).
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
 exists ((
            (E_taggingright
               (E_pair (E_live_expr (E_comp lab)) (E_constant CONST_unit))))).
 reflexivity.
 exists (E_comp lab) (E_comp l).
 left.
 splits.
 exists S_Second.
 assumption.
 apply star_refl.
 simpl; auto.
 substs.
 apply red_not_value in H7; simpl in H7; intuition.
 apply red_not_value in H8; simpl in H8; intuition.
 admit.
 (*
 apply fork_tau_behave_ce in H1.
 substs.
 intuition; substs.
 inversion H0.
 substs.
 apply taured_val_id in H3.
 substs.
 right.
 splits.
 exists (
     (E_taggingleft
        (E_pair (E_constant CONST_unit) (E_live_expr ( expr5))))).
 reflexivity.
 exists (E_comp l) ( expr5).
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
 *)
 admit.
 (*
 apply fork_tau_behave_ec in H1.
 intuition; substs.
 inversion H0.
 substs.
 apply taured_val_id in H3; substs.
 right.
 splits.
 exists (
     (E_taggingright
        (E_pair (E_live_expr ( expr5)) (E_constant CONST_unit)))).
 reflexivity.
 exists ( expr5) (E_comp l).
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
 *)
 
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
 exists ( x1) ( x2); reflexivity.
 destruct H3. destruct H3.
 intuition; substs.
 
 
 right.
 splits.
 exists ( (E_taggingright (E_pair (E_live_expr ( x1)) x2))).
 reflexivity.
 exists ( ( e'')) ( x0).
 right.
 splits.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x)))
         (E_live_expr ( x0))))(e2:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e'')))
       (E_live_expr ( x0))))(s:=S_First).
 splits; [ assumption | assumption | apply star_refl ].
 assumption.
  destruct H3. destruct H3.
 intuition; substs.
  right.
 splits.
  exists ( (E_taggingleft (E_pair x1 (E_live_expr ( x2))))); reflexivity.
 exists ( ( e'')) ( x0).
 right.
 splits.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x)))
         (E_live_expr ( x0))))(e2:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e'')))
       (E_live_expr ( x0))))(s:=S_First).
 splits; [ assumption | assumption | apply star_refl ].
 assumption.
 substs.


 assert (L:=H3).
 apply fork_tau_behave_ee in H3.
 intuition.
 destruct H4. destruct H3.
 intuition; substs.
 left.
 exists ( x1) ( x2); reflexivity.
 destruct H3. destruct H3.
 intuition; substs.
 
 
 right.
 splits.
 exists ( (E_taggingright (E_pair (E_live_expr ( x1)) x2))).
 reflexivity.
 exists ( ( x)) ( e'').
 right.
 splits.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x)))
         (E_live_expr ( x0))))(e2:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x)))
       (E_live_expr ( e''))))(s:=S_Second).
 splits; [ assumption | assumption | apply star_refl ].
 assumption.
  destruct H3. destruct H3.
 intuition; substs.
  right.
 splits.
  exists ( (E_taggingleft (E_pair x1 (E_live_expr ( x2))))); reflexivity.
 exists ( ( x)) ( e'').
 right.
 splits.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x)))
         (E_live_expr ( x0))))(e2:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x)))
       (E_live_expr ( e''))))(s:=S_Second).
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
 exists ( (E_taggingright (E_pair  (E_live_expr q) v))).
 splits.
 apply JO_red_forkdeath2.
 assumption.
 apply swapf_right_b.
 simpl; auto.
 assumption.
 subst.
 exists (S_First)  ( (E_taggingleft (E_pair v' (E_live_expr p) ))).
 splits. 
 apply JO_red_forkdeath1.
 assumption.
 apply swapf_left_b.
 assumption.
 simpl; auto.
 substs.
 exists S_Second.
 exists ( (E_taggingright (E_pair  (E_live_expr q) (E_constant CONST_unit)))).
 splits.
 apply JO_red_forkdocomp2.
 apply swapf_right_b.
 simpl; auto.
 simpl; auto.
 subst.
 exists (S_First)  ( (E_taggingleft (E_pair (E_constant CONST_unit) (E_live_expr p) ))).
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
     E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e'')))
       (E_live_expr (x1)) =
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
 exists ( e'') (x1) x2; splits; [reflexivity | reflexivity ].
 destruct H3; destruct H3; destruct H3; destruct H3; intuition.
  simplify_eq H4; simplify_eq H3; intros; substs; clear H3; clear H4.
 exists ( e) (x0) x3 x4.
   splits.
 reflexivity.
 reflexivity.

 apply S_star with (y:=((E_apply (E_apply (E_constant CONST_fork) (E_live_expr (x0)))
          (E_live_expr ( e''))) >>= swapf )).
 apply tStep with (s:=S_Second).
 apply JO_red_evalbind.
 apply JO_red_forkmove2 with (s:=s0).
 assumption.
 assumption.
 apply S_star with (y:=((E_apply (E_apply (E_constant CONST_fork) (E_live_expr (x0)))
          (E_live_expr ( e''))))).
 apply tStep with (s:=S_Second).
 apply JO_red_forkmove2 with (s:=s0).
 assumption.
 assumption.
 assumption.
 substs.

 assert ( exists p q lm lm',
     E_apply (E_apply (E_constant CONST_fork) (E_live_expr (x0)))
       (E_live_expr ( e'')) =
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
 exists (x0) ( e'') x2.
 splits; [reflexivity | reflexivity].
 destruct H3; destruct H3; destruct H3; destruct H3; intuition.
 simplify_eq H4; simplify_eq H3; intros; substs.
 clear H3; clear H4.
 exists (x) ( e') x3 x4.
   splits.
 reflexivity.
 reflexivity.
 apply S_star with (y:=((E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e'')))
          (E_live_expr (x))) >>= swapf )).
 apply tStep with (s:=S_First).
 apply JO_red_evalbind.
 apply JO_red_forkmove1 with (s:=s0).
 assumption.
 assumption.
 apply S_star with (y:=((E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e'')))
          (E_live_expr (x))))).
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
 
 exists ( v) x1 x2 x0.
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
 
  exists x0 ( v') x2 x1.
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




Lemma fork_swap_tau_behave : forall (e : expr )( p q : livemodes ), tauRed (E_bind (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p))) (E_live_expr (q))) (swapf)) e ->
                                 ((exists (p' q' : livemodes), e = (E_bind (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p'))) (E_live_expr (q'))) (swapf)) /\ tauRed (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p))) (E_live_expr (q)))  (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p'))) (E_live_expr (q'))) ) \/ 
                                 ((exists (lm : livemodes),  tauRed ( (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p))) (E_live_expr (q)))) (E_live_expr lm) /\ totalTauRed ((E_live_expr lm) >>= swapf) e /\ ((exists (v : expr) (l : livemodes), is_value_of_expr v /\ lm = (
          (
             (E_taggingleft
                (E_pair v (E_live_expr (l)))))) ) \/ (exists (v : expr) (l : livemodes), is_value_of_expr v /\ lm = (
          (
             (E_taggingright
                (E_pair (E_live_expr (l)) v)))) )))) ).
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
 exists (E_comp lab) (E_comp lab0).
 splits; [reflexivity | apply star_refl].
 admit. 
 admit.
 (*apply fork_tau_behave_ce in H1.
 intuition.
 substs.
 left.
 exists (E_comp lab) ( expr5).
 splits; [reflexivity | apply star_refl].
 substs.
 right.
 exists ( (E_taggingright (E_pair (E_live_expr (E_comp lab)) expr5))).
 splits.
 assumption.
 apply star_refl.
 apply fork_tau_behave_ec in H1.
 intuition.
 substs.
 left.
 exists ( expr5) (E_comp lab).
 splits; [reflexivity | apply star_refl].
 substs. 
 right.
 exists ( (E_taggingleft (E_pair expr5 (E_live_expr (E_comp lm))))).
 splits.
 assumption. 
 apply star_refl. *)
 assert (L:=H1).
 apply fork_tau_behave_ee in H1.
 intuition.
 destruct H0; destruct H0; intuition; substs.
 left.
 exists ( x0) ( x1).
 splits; [reflexivity | assumption].
 destruct H1; destruct H0; intuition; substs.
 right.
 exists (( (E_taggingright (E_pair (E_live_expr ( x0)) x1)))).
 splits.
 assumption.
 apply star_refl.
 right.
 exists x1 ( x0).
 splits.
 assumption.
 reflexivity.
 destruct H1; destruct H0; intuition; substs.
 right.
 exists ( (E_taggingleft (E_pair x0 (E_live_expr ( x1))))).
 splits.
 assumption.
 apply star_refl.
 left.
 exists x0 ( x1).
 splits.
 assumption.
 reflexivity.
 destruct H0.  intuition; substs.
 destruct H3.
 intuition.
 substs.
 simplify_eq H1. clear H1; intros; substs.
 assert (L:=H).
 right.
 exists ( x2).
 splits.
 induction p; induction q.
 admit.
 admit.
 admit.
 apply fork_tau_behave_ee in H2.
 intuition.
 destruct H1.
 destruct H1.
 intuition.
 discriminate H4.
 destruct
 apply bind_tau_behave_back_h in H.
 destruct H.
 destruct H.
 intuition.
 simplify_eq H1; clear H1; intros; substs.
 destruct H.
 intuition.
 simplify_eq H3; clear H3; intros; substs.
 assumption.
 simplify_eq H1; clear H1; intros; substs.
 destruct H.
 intuition.
 destruct H3.
 intuition.
 simplify_eq H4; clear H4; intros; substs.
 assumption.
 destruct H3.
 assumption.
 apply taured_val_id in H0.
 substs.
 exists ( x2).
 splits.
 assumption.
 apply star_refl.
 
 induction p.
 induction q.
 apply fork_tau_behave_cc in H2.
 discriminate H2.
 admit.
  
 (*
 apply fork_tau_behave_ce in H2.
 intuition.
 discriminate H1.
 simplify_eq H2; intros; substs; simpl; auto. *)

 induction q.
 admit.
 (*
  apply fork_tau_behave_ec in H2.
 intuition.
 discriminate H1.
 simplify_eq H2; intros; substs; auto.
 simpl; auto. 
 *)
 apply fork_tau_behave_ee in H2.
 intuition.
 destruct H0.
 destruct H0.
 intuition.
 discriminate H3.
 destruct H1.
 destruct H0.
 intuition.
 right.
 simplify_eq H4; intros; clear H4.
 substs.
 exists x0 ( x).
 splits.
 assumption.
 reflexivity.
 destruct H1.
 destruct H0.
 intuition.
 simplify_eq H4; intros; clear H4.
 substs.
 left.
 exists x ( x0).
 splits.
 assumption.
 reflexivity.
 destruct H1.
 destruct H0.
 intuition.
 
 destruct H1; destruct H1; intuition.
 discriminate H4.
 destruct H2; destruct H1; intuition.
 simplify_eq H5; intros; substs; simpl; auto.
 destruct H2; destruct H1; intuition.
 simplify_eq H5; intros; substs; simpl; auto.
 simplify_eq H1; intros; substs; simpl; auto.
 
 right.
 exists ( x2).
 clear H1.
 assert (L:=H2).
 induction p.
 induction q.
 
 apply fork_tau_behave_cc in H2.
 discriminate H2.
 admit.
 (*
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
          (E_taggingright (E_pair (E_live_expr (E_comp lab)) expr5))) (E_live_expr
     ( (E_taggingleft (E_pair expr5 (E_live_expr (E_comp lab)) ))))) /\ tauRed
       (E_apply swapf
          (E_taggingright (E_pair (E_live_expr (E_comp lab)) expr5))) e).
 splits.
 apply swapf_right.
 simpl; auto.
 assumption.
 assumption.
 apply ttau_prefix in H0.
 intuition.
 apply S_star with (y:=(E_apply swapf
          (E_taggingright (E_pair (E_live_expr (E_comp lab)) expr5)))).
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
 simpl; auto. *)
 induction q.
 admit.
 (*
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
          (E_taggingleft (E_pair expr5 (E_live_expr (E_comp lab))))) (E_live_expr
     ( (E_taggingright (E_pair  (E_live_expr (E_comp lab)) expr5 ))))) /\ tauRed
       (E_apply swapf
          (E_taggingleft (E_pair expr5 (E_live_expr (E_comp lab))))) e).
 splits.
 apply swapf_left.
 simpl; auto.
 simpl; auto.
 assumption.
 apply ttau_prefix in H0.
 intuition.
 apply S_star with (y:=(E_apply swapf
          (E_taggingleft (E_pair expr5 (E_live_expr (E_comp lab)))))).
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
 simpl; auto. *)
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
       (E_apply swapf (E_taggingright (E_pair (E_live_expr ( x)) x0))) (E_live_expr
     ( (E_taggingleft (E_pair x0 (E_live_expr  ( x))  ))))) /\ tauRed
       (E_apply swapf (E_taggingright (E_pair (E_live_expr ( x)) x0)))
       e).
 splits.
 apply swapf_right.
 simpl; auto.
 simpl; auto.
 assumption.
 apply ttau_prefix in H0.
 intuition.
 apply S_star with (y:=(E_apply swapf (E_taggingright (E_pair (E_live_expr ( x)) x0)))).
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
       (E_apply swapf (E_taggingleft (E_pair x (E_live_expr ( x0)) ))) (E_live_expr
     ( (E_taggingright (E_pair  (E_live_expr  ( x0)) x  ))))) /\ tauRed
       (E_apply swapf (E_taggingleft (E_pair x (E_live_expr ( x0)) )))
       e).
 splits.
 apply swapf_left.
 simpl; auto.
 simpl; auto.
 assumption.
 apply ttau_prefix in H0.
 intuition.
 apply S_star with (y:=(E_apply swapf (E_taggingleft (E_pair x (E_live_expr ( x0)) )))).
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
                                 ((exists (lm : livemodes),  labRed l ( (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (p))) (E_live_expr (q)))) (E_live_expr lm) /\ totalTauRed ((E_live_expr lm) >>= swapf) e /\ 
((exists (v : expr) (l : livemodes), is_value_of_expr v /\ lm = (
          (
             (E_taggingleft
                (E_pair v (E_live_expr (l)))))) ) \/ (exists (v : expr) (l : livemodes), is_value_of_expr v /\ lm = (
          (
             (E_taggingright
                (E_pair (E_live_expr (l)) v)))) )))) ).
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
 exists x x1.
 splits.
 reflexivity.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e0)))
          (E_live_expr (x0))))(e2:= E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e'')))
       (E_live_expr (x0)))(s:=S_First).
 splits; [assumption | assumption | assumption ].
 destruct H1.
 right.
 exists x.
 splits.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e0)))
       (E_live_expr (x0))))(e2:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e'')))
       (E_live_expr (x0))))(s:=S_First). splits.
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
 exists x0 x1.
 splits.
 reflexivity.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (x)))
       (E_live_expr ( e'0))))(e2:= ( E_apply (E_apply (E_constant CONST_fork) (E_live_expr (x)))
       (E_live_expr ( e''))))(s:=S_Second).
 splits; [assumption | assumption | assumption ].
 destruct H1.
 right.
 exists x0.
 splits.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (x)))
       (E_live_expr ( e'0))))(e2:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (x)))
       (E_live_expr ( e''))))(s:=S_Second). splits.
 assumption.
 assumption.
 intuition.
 intuition.
 substs.

 right.
 exists  (
          (
             (E_taggingleft
                (E_pair (E_constant CONST_unit) (E_live_expr (x0)))))).
 splits.
 apply lab_r with (e1:=( E_apply (E_apply (E_constant CONST_fork) (E_live_expr (E_comp l)))
       (E_live_expr (x0))))(e2:=(E_live_expr
       (
          (E_taggingleft
             (
                (E_pair (E_constant CONST_unit) (E_live_expr (x0))))))))(s:=(S_First)).
 splits.
 assumption.
 assumption.
 apply star_refl.
 assert ((totalTauRed (E_live_expr
          (
             (E_taggingleft
                (
                   (E_pair (E_constant CONST_unit) (E_live_expr (x0)))))) >>=
        swapf) (E_live_expr
          (
             (
                (E_taggingright
                   (E_pair  (E_live_expr (x0)) (E_constant CONST_unit))))) )) /\ (tauRed
       (E_live_expr
          (
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
 exists ((
          (E_taggingright
             (E_pair (E_live_expr (x)) (E_constant CONST_unit))))).
 splits.
 apply lab_r with (e1:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr (x)))
       (E_live_expr (E_comp l))))(e2:=( E_live_expr
       (
          (E_taggingright
             (E_pair (E_live_expr (x)) (E_constant CONST_unit))))))(s:=S_Second). splits.
 assumption.
 assumption.
 apply star_refl.
 assert ((totalTauRed
       (E_live_expr
          (
             (E_taggingright
                (E_pair (E_live_expr (x)) (E_constant CONST_unit)))) >>=
        swapf) (E_live_expr
          (
            (E_taggingleft
             (
                (E_pair  (E_constant CONST_unit) (E_live_expr (x)))))) )) /\ (tauRed
       (E_live_expr
          (
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
 admit.
 (*
  apply fork_tau_behave_ce in H2.
 intuition.
  discriminate H1.
 simplify_eq H2; intros; substs.
 assert (totalTauRed
       (E_live_expr
          (
             (E_taggingright (E_pair (E_live_expr (E_comp lab)) expr5))) >>=
        swapf) (E_live_expr
          (
             (E_taggingleft (E_pair expr5 (E_live_expr (E_comp lab))))) )).
 apply swapf_right_b.
 simpl; auto.
 assumption.
 apply ttau_midpoint  with (e':=(E_live_expr
          ( (E_taggingleft (E_pair expr5 (E_live_expr (E_comp lab))))))) in H3.
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
 *)
 admit. (*
 apply fork_tau_behave_ec in H2.
 intuition.
  discriminate H1.
 simplify_eq H2; clear H2; intros; substs.
 assert (totalTauRed
       (E_live_expr
          (
             (E_taggingleft (E_pair expr5 (E_live_expr (E_comp lab)) ))) >>=
        swapf) (E_live_expr
          (
             (E_taggingright (E_pair (E_live_expr (E_comp lab)) expr5))) )).
 apply swapf_left_b.
 simpl; auto.
 simpl; auto.
 apply ttau_midpoint  with (e':=(E_live_expr
          ( (E_taggingright (E_pair (E_live_expr (E_comp lab)) expr5))))) in H3.
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
 *)
 
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
          ( (E_taggingright (E_pair (E_live_expr ( x0)) x1))) >>=
        swapf) (E_live_expr
          (
             (E_taggingleft
                (
                   (E_pair x1 (E_live_expr ( x0)))))))) /\ (tauRed
       (E_live_expr
          ( (E_taggingright (E_pair (E_live_expr ( x0)) x1))) >>=
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
          (
             (E_taggingleft
                ( (E_pair x0 (E_live_expr ( x1)))))) >>=
        swapf) (E_live_expr
          (
             (
                (E_taggingright (E_pair (E_live_expr ( x1)) x0 )))))) /\ (tauRed
       (E_live_expr
          (
             (E_taggingleft
                ( (E_pair x0 (E_live_expr ( x1)))))) >>=
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



Lemma fork_comm_taured_ee_laststep_h : forall (x y : expr), tauRed x y -> ((fun x y => 
   ( exists ( e e' : expr) (lm : livemodes),  
       x = (E_apply
         (E_apply (E_constant CONST_fork) (E_live_expr ( e')))
         (E_live_expr ( e))) /\
       y = (E_live_expr  lm)) -> 
( exists (e e' : expr) (lm : livemodes), 
       x = (E_apply
         (E_apply (E_constant CONST_fork) (E_live_expr ( e')))
         (E_live_expr ( e))) /\ 
       y = (E_live_expr  lm) /\
       (exists (p q : expr), tauRed x (E_apply
         (E_apply (E_constant CONST_fork) (E_live_expr ( q)))
         (E_live_expr ( p))) /\ tauStep (E_apply
         (E_apply (E_constant CONST_fork) (E_live_expr ( q)))
         (E_live_expr ( p))) (E_live_expr  lm) )))x y ).
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
      (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x1)))
         (E_live_expr ( x0))) y).
 apply S_star with (y:=y).
 assumption.
 apply star_refl.
 apply fork_tau_behave_ee in H2.
 intuition.
 destruct H3. destruct H2.
 intuition. 
 substs.
 assert (exists e e' lm,
     E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x)))
       (E_live_expr ( x3)) =
     E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( e')))
       (E_live_expr ( e)) /\
     E_live_expr x2 = E_live_expr lm /\
     (exists p q,
      tauRed
        (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x)))
           (E_live_expr ( x3)))
        (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( q)))
           (E_live_expr ( p))) /\
      tauStep
        (E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( q)))
           (E_live_expr ( p))) (E_live_expr lm))).
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
 apply S_star with  (y:=(E_apply (E_apply (E_constant CONST_fork) (E_live_expr ( x5)))
          (E_live_expr ( x4)))).
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

*)
Inductive fork_comm_rel :  relation expr := 
 | forkee_start : forall (e e' : livemodes), fork_comm_rel (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (e))) (E_live_expr (e'))) (E_bind (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (e'))) (E_live_expr (e))) (swapf))
 | forkee_tau : forall  ( lm lm' : livemodes) (e : expr),  totalTauRed (E_bind ((E_live_expr lm')) (swapf)) (E_live_expr lm) /\  totalTauRed (E_bind ((E_live_expr lm')) (swapf)) e  -> fork_comm_rel (E_live_expr lm) e.


Lemma fork_comm_rel_value_equal : forall (vp vq : expr), is_value_of_expr vp -> is_value_of_expr vq -> fork_comm_rel vp vq -> vp=vq.
Proof.
 intros.
 inversion H1.
 substs.
 simpl in H; intuition.
 substs.
 intuition.
 assert ((totalTauRed vq (E_live_expr lm)) \/ (totalTauRed (E_live_expr lm) vq)).
 apply ttau_midpoint with (e:=(E_live_expr lm' >>= swapf)).
 assumption.
 assumption.
 intuition.
 apply tau_incl_totalTau in H5.
 apply taured_val_id in H5.
 substs; intuition.
 assumption.
 apply tau_incl_totalTau in H5.
 apply taured_val_id in H5.
 substs; intuition.
 assumption.
Qed.

Lemma fork_comm_rel_tau_bisim : forall (p q : expr), fork_comm_rel p q -> ((forall (p' : expr), tauRed  p p' -> (exists (q' : expr), tauRed  q q' /\ fork_comm_rel p' q') ) /\ (forall (q' : expr), tauRed  q q' -> (exists (p' : expr), tauRed  p p' /\ fork_comm_rel p' q') )).
Proof.
 intros.
 intuition.
 inversion H.
 substs.

 apply fork_tau_swap_total in H0.
 intuition.
 destruct H1.
 destruct H0.
 intuition.
 substs.
 exists ((E_apply (E_apply (E_constant CONST_fork) (E_live_expr x0)) (E_live_expr x) >>=
   swapf)).
 split.
 apply bind_tau_behave_front.
 assumption.
 apply forkee_start.
 destruct H0.
 destruct H0.
 intuition.
 substs.
 exists (((E_live_expr ( (E_taggingright (E_pair (E_live_expr x0) x)))))>>=swapf).
 split.
 apply bind_tau_behave_front.
 assumption.
 apply forkee_tau with (lm':=( (E_taggingright (E_pair (E_live_expr x0) x)))).
 split.
 apply swapf_right_b.
 simpl; auto.
 simpl; auto.
 apply star_refl.
 destruct H0.
 destruct H0.
 intuition.
 substs.
 exists ((E_live_expr ( (E_taggingleft (E_pair x (E_live_expr x0)))))>>=swapf).
 split.
 apply bind_tau_behave_front.
 assumption.
 apply forkee_tau with (lm':=( ( (E_taggingleft (E_pair x (E_live_expr x0)))))).
 split.
 apply swapf_left_b.
 simpl; auto.
 simpl; auto.
 apply star_refl.
 intuition.
 substs.
 assert ((totalTauRed q (E_live_expr lm)) \/ (totalTauRed (E_live_expr lm) q)).
 apply ttau_midpoint with (e:=(E_live_expr lm' >>= swapf)).
 assumption.
 assumption.
 intuition.
 exists (E_live_expr lm).
 split.
 apply tau_incl_totalTau in H2.
 assumption.
 apply taured_val_id in H0.
 substs.
 apply forkee_tau with (lm' := lm').
 intuition.
 simpl; auto.
 apply tau_incl_totalTau in H2.
 apply taured_val_id in H2.
 substs.
 exists (E_live_expr lm).
 split.
 apply star_refl.
 apply taured_val_id in H0.
 substs.
 apply forkee_tau with (lm':=lm').
 intuition.
 simpl; auto.
 simpl; auto.

 inversion H.
 substs.
 apply bind_tau_behave_back_h in H0.
 destruct H0.
 destruct H0.
 intuition.
 destruct H0.
 intuition.
 simplify_eq H1; clear H1; intros; substs.

 apply fork_tau_swap_total in H2.
 intuition.
 destruct H0.
 destruct H0.
 intuition.
 substs.
 exists ((E_apply (E_apply (E_constant CONST_fork) (E_live_expr x0)) (E_live_expr x))).
 split.
 assumption.
 apply forkee_start.
 destruct H1.
 destruct H0.
 intuition.
 substs.
 exists (((E_live_expr ( (E_taggingright (E_pair (E_live_expr x0) x)))))).
 split.
 assumption.
 apply forkee_tau with (lm':=( (E_taggingleft (E_pair x (E_live_expr x0))))).
 split.
 apply swapf_left_b.
 simpl; auto.
 simpl; auto.
 apply star_refl.
 destruct H1.
 destruct H0.
 intuition.
 substs.
 exists ((E_live_expr ( (E_taggingleft (E_pair x (E_live_expr x0)))))).
 split.
 assumption.
 apply forkee_tau with (lm':=( (E_taggingright (E_pair (E_live_expr x0) x)))).
 split.
 apply swapf_right_b.
 simpl; auto.
 simpl; auto.
 apply star_refl.
 destruct H0.
 simplify_eq H1; clear H1; intros; substs.
 intuition.
 apply fork_tau_swap_total in H1.
 intuition.
 destruct H0; destruct H0. destruct H0; discriminate H0.
 destruct H1; destruct H0; destruct H0. destruct H1; simplify_eq H1; clear H1; intros; substs.
 exists (E_live_expr ( (E_taggingright (E_pair (E_live_expr x0) x)))).
 intuition.
 destruct H2.
 intuition.
 substs.
 apply taured_val_id in H1.
 substs.
 apply forkee_tau with (lm':=( (E_taggingleft (E_pair x (E_live_expr x0))))).
 intuition.
 apply swapf_left_b.
 assumption.
 simpl; auto.
 apply star_refl.
 simpl; auto.
 apply taured_val_id in H1.
 substs.
 apply forkee_tau with (lm':=( (E_taggingleft (E_pair x (E_live_expr x0))))).
 intuition.
 apply swapf_left_b.
 assumption.
 simpl; auto.
 assert (totalTauRed
  (E_apply swapf ( ( (E_taggingleft (E_pair x (E_live_expr x0)))))
   ) (E_live_expr ( (E_taggingright (E_pair (E_live_expr x0) x))))).
 apply swapf_left.
 assumption.
 simpl; auto.
 assert ((totalTauRed (E_apply swapf (E_taggingleft (E_pair x (E_live_expr x0)))) q' /\ totalTauRed q' (E_live_expr ( (E_taggingright (E_pair (E_live_expr x0) x))))) \/ (tauRed (E_live_expr ( (E_taggingright (E_pair (E_live_expr x0) x)))) q')).
 apply ttau_prefix.
 intuition.
 intuition.
 apply S_star with (y:=(E_apply swapf (E_taggingleft (E_pair x (E_live_expr x0))))).
 apply JO_red_dobind_td.
 apply S_First.
 simpl; auto.
 assumption.
 apply taured_val_id in H6.
 substs.
 apply swapf_left_b.
 assumption.
 simpl; auto.
 simpl; auto.
 simpl; auto.
 destruct H1; destruct H0; destruct H0. destruct H1; simplify_eq H1; clear H1; intros; substs.
 exists ((E_live_expr ( (E_taggingleft (E_pair x (E_live_expr x0)))))).
 intuition.
 destruct H2.
 intuition.
 substs.
 apply taured_val_id in H1.
 substs.
 apply forkee_tau with (lm':=( (E_taggingright (E_pair (E_live_expr x0) x)))).
 intuition.
 apply swapf_right_b.
 simpl; auto.
 assumption.
 
 apply star_refl.
 simpl; auto.
 apply taured_val_id in H1.
 substs.
 apply forkee_tau with (lm':=( (E_taggingright (E_pair (E_live_expr x0) x)))).
 intuition.
 apply swapf_right_b.
 simpl; auto.
 assumption.
 assert (totalTauRed
  (E_apply swapf ( ( (E_taggingright (E_pair (E_live_expr x0) x))))
   ) (E_live_expr ( (E_taggingleft (E_pair x (E_live_expr x0) ))))).
 apply swapf_right.
 simpl; auto.
 assumption.
 assert ((totalTauRed (E_apply swapf (E_taggingright (E_pair (E_live_expr x0) x))) q' /\ totalTauRed q' (E_live_expr ( (E_taggingleft (E_pair x (E_live_expr x0)))))
                 \/ (tauRed (E_live_expr ( (E_taggingleft (E_pair x (E_live_expr x0))))) q'))).
 apply ttau_prefix.
 intuition.
 intuition.
 apply S_star with (y:=(E_apply swapf (E_taggingright (E_pair (E_live_expr x0) x)))).
 apply JO_red_dobind_td.
 apply S_First.
 simpl; auto.
 simpl; auto.

 apply taured_val_id in H6.
 substs.
 apply swapf_right_b.
 simpl; auto.
 simpl; auto.
 simpl; auto.
 simpl; auto.
 exists (E_apply (E_apply (E_constant CONST_fork) (E_live_expr e')) (E_live_expr e)) swapf.
 reflexivity.
 substs.
 exists (E_live_expr lm).
 intuition.
 apply star_refl.
 apply forkee_tau with (lm':=lm').
 intuition.
 assert ((totalTauRed q (E_live_expr lm) \/ totalTauRed (E_live_expr lm) q)).
 apply ttau_midpoint with (e:=(E_live_expr lm' >>= swapf)).
 assumption.
 assumption.
 intuition.
 assert (((totalTauRed q q' /\ totalTauRed q' (E_live_expr lm)) \/ (tauRed (E_live_expr lm) q'))).
 apply ttau_prefix.
 intuition.
 intuition.
 apply star_trans with (y:=q).
 assumption.
 assumption.
 apply taured_val_id in H5.
 substs.
 assumption.
 simpl; auto.
 apply tau_incl_totalTau in H4.
 apply taured_val_id in H4.
 substs.
 apply taured_val_id in H0.
 substs.
 assumption.
 simpl; auto.
 simpl; auto.
Qed.
 


Theorem fork_comm_rel_lab_bisim : forall (p q : expr), fork_comm_rel p q -> ((forall (l : label) (p' : expr), labRed l p p' -> (exists (q' : expr), labRed l q q' /\ fork_comm_rel p' q') ) /\ (forall (l : label) (q' : expr), labRed l q q' -> (exists (p' : expr), labRed l p p' /\ fork_comm_rel p' q') )).
Proof. 
 intros.
 splits.
 induction H.
 intros.
 apply fork_label_swap_total in H.
 intuition.
 destruct H0.
 destruct H.
 intuition.
 substs.
 apply bind_lab_behave_front with (e':=swapf) in H1.
 exists (E_apply (E_apply (E_constant CONST_fork) (E_live_expr x0))
          (E_live_expr x) >>= swapf).
 intuition.
 apply forkee_start.
 destruct H.
 destruct H. 
 intuition.
 substs.
 exists (E_live_expr ( (E_taggingleft (E_pair x (E_live_expr x0))))).
 apply bind_lab_behave_front with (e':=swapf) in H2.
 assert (totalTauRed (E_live_expr ( (E_taggingright (E_pair (E_live_expr x0) x))) >>=
   swapf) (E_live_expr ( (E_taggingleft (E_pair x (E_live_expr x0)))))).
 apply swapf_right_b.
 simpl; auto.
 assumption.
 intuition.
 inversion H2.
 substs.
 apply lab_r with (e1:=e1)(e2:=e2)(s:=s).
 intuition.
 apply star_trans with (y:=(E_live_expr ( (E_taggingright (E_pair (E_live_expr x0) x))) >>=
        swapf)).
 assumption.
 apply tau_incl_totalTau.
 assumption.
 apply forkee_tau with (lm':=( (E_taggingright (E_pair (E_live_expr x0) x)))).
 intuition.
 destruct H.
 destruct H.
 intuition.
 substs.
 exists (E_live_expr ( (E_taggingright (E_pair (E_live_expr x0) x)))).
 apply bind_lab_behave_front with (e':=swapf) in H2.
 assert (totalTauRed (E_live_expr ( (E_taggingleft (E_pair x (E_live_expr x0) ))) >>=
   swapf) (E_live_expr ( (E_taggingright (E_pair (E_live_expr x0) x))))).
 apply swapf_left_b.
 simpl; auto.
 simpl; auto.
 intuition.
 inversion H2.
 substs.
 apply lab_r with (e1:=e1)(e2:=e2)(s:=s).
 intuition.
 apply star_trans with (y:=(E_live_expr ( (E_taggingleft (E_pair x (E_live_expr x0)))) >>=
        swapf)).
 assumption.
 apply tau_incl_totalTau.
 assumption.
 apply forkee_tau with (lm':=( (E_taggingleft (E_pair x (E_live_expr x0))))).
 intuition.
 substs.
 intuition.
 apply labred_not_val in H.
 simpl in H; intuition.

 intros.
 inversion H.
 substs.
 apply fork_swap_bind_lab_behave in H0.
 intuition.
 destruct H1.
 destruct H0.
 intuition.
 apply bind_tau_behave_back_h in H1.
 intuition.
 destruct H1.
 destruct H0.
 intuition.
 simplify_eq H1; clear H1; intros; substs.
 destruct H0.
 intuition.
 substs.
 
 apply fork_label_swap_total in H2.
 intuition.
 destruct H0.
 destruct H0.
 intuition.
 simplify_eq H2; clear H2; intros; substs.
 Check fork_tau_swap_total.
 apply fork_tau_swap_total in H1.
 intuition.
 destruct H0.
 destruct H0.
 intuition.
 substs.
 exists ((E_apply (E_apply (E_constant CONST_fork) (E_live_expr x0))
          (E_live_expr x))).
 intuition.
 inversion H3.
 apply lab_r with (e1:=e1)(e2:=e2)(s:=s).
 intuition.
 substs.
 apply star_trans with (y:= (E_apply (E_apply (E_constant CONST_fork) (E_live_expr x3))
          (E_live_expr x2))); intuition.
 apply forkee_start.
 destruct H1.
 destruct H0.
 intuition.
 substs.
 exists (E_live_expr ( (E_taggingright (E_pair (E_live_expr x0) x)))).
 intuition.
 inversion H3.
 apply lab_r with (e1:=e1)(e2:=e2)(s:=s).
 intuition.
 substs.
 apply star_trans with (y:= (E_apply (E_apply (E_constant CONST_fork) (E_live_expr x3))
          (E_live_expr x2))); intuition.
 apply forkee_tau with (lm':=( ( (E_taggingleft (E_pair x (E_live_expr x0)))))).
 intuition.
 apply swapf_left_b.
 assumption.
 simpl; auto.
 apply star_refl.
 destruct H1.
 destruct H0.
 intuition.
 substs.
 exists (E_live_expr ( (E_taggingleft (E_pair x (E_live_expr x0))))).
 intuition.
 inversion H3.
 apply lab_r with (e1:=e1)(e2:=e2)(s:=s).
 intuition.
 substs.
 apply star_trans with (y:= (E_apply (E_apply (E_constant CONST_fork) (E_live_expr x3))
          (E_live_expr x2))); intuition.
 apply forkee_tau with (lm':=( ( (E_taggingright (E_pair (E_live_expr x0) x))))).
 intuition.
 apply swapf_right_b.
 simpl;auto.
 assumption.
 apply star_refl.
 destruct H2.
 destruct H0.
 intuition.
 discriminate H0.
 destruct H2.
 destruct H0.
 intuition.
 discriminate H0.
 simplify_eq H1; clear H1; intros; substs.
 destruct H0.
 intuition.

 apply fork_label_swap_total in H2.
 intuition.
 destruct H0.
 destruct H0.
 intuition.
 simplify_eq H2; clear H2; intros; substs.
 Check fork_tau_swap_total.
 apply fork_tau_swap_total in H1.
 intuition.
 destruct H0.
 destruct H0.
 intuition.
 discriminate H1.
 destruct H1.
 destruct H0.
 intuition.
 simplify_eq H0; clear H0; intros; substs.
 destruct H3.
 intuition.
 substs.
 apply taured_val_id in H0.
 substs.
 exists (E_live_expr ( (E_taggingright (E_pair (E_live_expr x0) x)))).
 intuition.
 inversion H4.
 apply lab_r with (e1:=e1)(e2:=e2)(s:=s).
 intuition.
 substs.
 apply star_trans with (y:= (E_apply (E_apply (E_constant CONST_fork) (E_live_expr x3))
          (E_live_expr x2))); intuition.
 apply forkee_tau with (lm':=( ( (E_taggingleft (E_pair x (E_live_expr x0)))))).
 intuition.
 apply swapf_left_b.
 assumption.
 simpl; auto.
 apply star_refl.
 simpl; auto.
 apply taured_val_id in H0.
 substs.
 exists (E_live_expr ( (E_taggingright (E_pair (E_live_expr x0) x)))).
 intuition.
 inversion H4.
 apply lab_r with (e1:=e1)(e2:=e2)(s:=s).
 intuition.
 substs.
 apply star_trans with (y:= (E_apply (E_apply (E_constant CONST_fork) (E_live_expr x3))
          (E_live_expr x2))); intuition.
 apply forkee_tau with (lm':=( ( (E_taggingleft (E_pair x (E_live_expr x0)))))).
 intuition.
 apply swapf_left_b.
 assumption.
 simpl; auto.
 assert ( totalTauRed
  (E_apply 
   swapf ( (E_taggingleft (E_pair x (E_live_expr x0))))) ( E_live_expr(((E_taggingright (E_pair (E_live_expr x0) x)))))).
 apply swapf_left.
 assumption.
 simpl; auto.
 assert ((totalTauRed (E_apply swapf (E_taggingleft (E_pair x (E_live_expr x0))))
       (E_live_expr ( (E_taggingright (E_pair (E_live_expr x0) x)))))/\(tauRed (E_apply swapf (E_taggingleft (E_pair x (E_live_expr x0)))) q')).
 intuition.
 apply ttau_prefix in H3.
 intuition.
 apply S_star with (y:=(E_apply swapf (E_taggingleft (E_pair x (E_live_expr x0))))). 
 apply JO_red_dobind_td.
 apply S_First.
 simpl; auto.
 assumption.
 apply taured_val_id in H7.
 substs.
 apply swapf_left_b.
 assumption. 
 simpl; auto.
 simpl; auto.
 simpl; auto.

 destruct H1.
 destruct H0.
 intuition.
 simplify_eq H0; clear H0; intros; substs.
 destruct H3.
 intuition.
 substs.
 apply taured_val_id in H0.
 substs.
 exists (E_live_expr ( (E_taggingleft (E_pair x (E_live_expr x0))))).
 intuition.
 inversion H4.
 apply lab_r with (e1:=e1)(e2:=e2)(s:=s).
 intuition.
 substs.
 apply star_trans with (y:= (E_apply (E_apply (E_constant CONST_fork) (E_live_expr x3))
          (E_live_expr x2))); intuition.
 apply forkee_tau with (lm':=( ( (E_taggingright (E_pair (E_live_expr x0) x))))).
 intuition.
 apply swapf_right_b.
 simpl;auto.
 assumption.
 apply star_refl.
 simpl; auto.
 apply taured_val_id in H0.
 substs.
 exists (E_live_expr ( (E_taggingleft (E_pair x (E_live_expr x0))))).
 intuition.
 inversion H4.
 apply lab_r with (e1:=e1)(e2:=e2)(s:=s).
 intuition.
 substs.
 apply star_trans with (y:= (E_apply (E_apply (E_constant CONST_fork) (E_live_expr x3))
          (E_live_expr x2))); intuition.
 apply forkee_tau with (lm':=( ( (E_taggingright (E_pair (E_live_expr x0) x))))).
 intuition.
 apply swapf_right_b.
 simpl; auto.
 assumption.
 assert ( totalTauRed
  (E_apply 
   swapf ( (E_taggingright (E_pair (E_live_expr x0) x)))) ( E_live_expr(((E_taggingleft (E_pair x (E_live_expr x0) )))))).
 apply swapf_right.
 simpl; auto.
 assumption.
 assert ((totalTauRed (E_apply swapf (E_taggingright (E_pair (E_live_expr x0) x)))
       (E_live_expr ( (E_taggingleft (E_pair x (E_live_expr x0))))))/\(tauRed (E_apply swapf (E_taggingright (E_pair (E_live_expr x0) x))) q')).
 intuition.
 apply ttau_prefix in H3.
 intuition.
 apply S_star with (y:=(E_apply swapf (E_taggingright (E_pair  (E_live_expr x0) x)))). 
 apply JO_red_dobind_td.
 apply S_First.
 simpl; auto.
 assumption.
 apply taured_val_id in H7.
 substs.
 apply swapf_right_b.
 
  
 simpl; auto.
 simpl; auto.
 simpl; auto.
 simpl; auto.
 destruct H2.
 destruct H0.
 intuition.
 discriminate H0.
 destruct H2.
 destruct H0.
 intuition.
 discriminate H0.
 exists (E_apply (E_apply (E_constant CONST_fork) (E_live_expr x)) (E_live_expr x0)) (swapf).
 reflexivity.
 
 destruct H1.
 intuition.
 apply fork_label_swap_total in H1.
 intuition.
 destruct H0.
 destruct H0.
 intuition. 
 discriminate H1.
 destruct H1.
 destruct H0.
 intuition.
 simplify_eq H0; clear H0; intros; substs. 
 assert (totalTauRed (E_live_expr ( (E_taggingleft (E_pair x0 (E_live_expr x1) ))) >>=
   swapf) (E_live_expr ( (E_taggingright (E_pair (E_live_expr x1) x0))))).
 apply swapf_left_b.
 simpl; auto.
 simpl; auto.
 assert (totalTauRed (E_live_expr ( (E_taggingleft (E_pair x0 (E_live_expr x1) ))) >>=
   swapf) (E_live_expr ( (E_taggingright (E_pair (E_live_expr x1) x0)))) /\ (tauRed
       (E_live_expr ( (E_taggingleft (E_pair x0 (E_live_expr x1)))) >>=
        swapf) q')).
 intuition.
 apply ttau_prefix in H3.
 intuition.
 exists (E_live_expr ( (E_taggingright (E_pair (E_live_expr x1) x0)))).
 intuition.
 apply forkee_tau with (lm':=( ( (E_taggingleft (E_pair x0 (E_live_expr x1)))))).
 intuition.
 apply taured_val_id in H5.
 substs.
 exists (E_live_expr ( (E_taggingright (E_pair (E_live_expr x1) x0)))).
 intuition.
 apply forkee_tau with (lm':=( ( (E_taggingleft (E_pair x0 (E_live_expr x1)))))).
 intuition.
 simpl; auto.
 destruct H1.
 destruct H0.
 intuition.
 simplify_eq H0; clear H0; intros; substs. 
 assert (totalTauRed (E_live_expr ( (E_taggingright (E_pair (E_live_expr x1) x0 ))) >>=
   swapf) (E_live_expr ( (E_taggingleft (E_pair x0 (E_live_expr x1) ))))).
 apply swapf_right_b.
 simpl; auto.
 simpl; auto.
 assert (totalTauRed (E_live_expr ( (E_taggingright (E_pair (E_live_expr x1) x0 ))) >>=
   swapf) (E_live_expr ( (E_taggingleft (E_pair x0 (E_live_expr x1) )))) /\ (tauRed
       (E_live_expr ( (E_taggingright (E_pair (E_live_expr x1) x0))) >>=
        swapf) q')).
 intuition.
 apply ttau_prefix in H3.
 intuition.
 exists (E_live_expr ( (E_taggingleft (E_pair x0 (E_live_expr x1))))).
 intuition.
 apply forkee_tau with (lm':=( ( (E_taggingright (E_pair (E_live_expr x1) x0))))).
 intuition.
 apply taured_val_id in H5.
 substs.
 exists (E_live_expr ( (E_taggingleft (E_pair x0 (E_live_expr x1))))).
 intuition.
 apply forkee_tau with (lm':=( ( (E_taggingright (E_pair (E_live_expr x1) x0))))).
 intuition.
 simpl; auto.
  
 substs.
 intuition.
 assert (~(labRed l (E_live_expr lm' >>= swapf) q')).
 apply ttr_val_not_labred with (v:=(E_live_expr lm)).
 intuition.
 simpl; auto.
 assert (labRed l (E_live_expr lm' >>= swapf) q').
 inversion H0.
 intuition.
 apply lab_r with (e1:=e1)(e2:=e2)(s:=s).
 intuition.
 apply star_trans with (y:=q).
 apply tau_incl_totalTau.
 intuition.
 assumption.
 intuition.
Qed.

Lemma fork_comm_rel_vewbsm : isExprRelationValueEqualWeakBisimilarity fork_comm_rel.
Proof.
 unfold isExprRelationValueEqualWeakBisimilarity.
 split.
 unfold  isExprRelationWeakBisimilarity.
 intros.
 intuition.
 specialize fork_comm_rel_lab_bisim with (p:=p)(q:=q).
 intuition.
 specialize fork_comm_rel_lab_bisim with (p:=p)(q:=q).
 intuition.
 specialize fork_comm_rel_tau_bisim with (p:=p)(q:=q).
 intuition.
 specialize fork_comm_rel_tau_bisim with (p:=p)(q:=q).
 intuition.
 apply fork_comm_rel_value_equal.
Qed.

Theorem fork_comm_vewbsm : forall (e e' : livemodes), isExprValueEqualWeaklyBisimilar (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (e))) (E_live_expr (e'))) (E_bind (E_apply (E_apply (E_constant CONST_fork) (E_live_expr (e'))) (E_live_expr (e))) (swapf)).
Proof.
 intros.
 apply isexprvalueequalweaklybisimilar.
 exists fork_comm_rel.
 split.
 apply fork_comm_rel_vewbsm.
 apply forkee_start.
Qed.


Lemma fork_assoc_tau_step_int : forall (a a' b b' c c' : livemodes), tauStep (( (a # b)) # c) (( (a' # b')) # c')   ->
 tauStep (a # (  ( b # c ) ) ) (a' # (  ( b' # c' ) )).
Proof.
 intros.
 inversion H.
 substs.
 inversion H0.
 substs.
 inversion H5.
 substs.
 apply tStep with (s:=S_First).
 apply JO_red_forkmove1 with (s:=s).
 assumption.
 substs.
 apply tStep with (s:=S_Second).
 apply JO_red_forkmove2 with (s:=S_First).
 apply JO_red_forkmove1 with (s:=s).
 assumption.
 apply red_not_value in H9; simpl in H9; intuition.
 apply red_not_value in H6; simpl in H6; intuition.
 substs.
 apply tStep with (s:=S_Second).
 apply JO_red_forkmove2 with (s:=S_Second).
 substs.
 apply JO_red_forkmove2 with (s:=s0).
 assumption.
 apply red_not_value in H9; simpl in H9; intuition.
 apply red_not_value in H5; simpl in H5; intuition.
Qed.


Lemma fork_tau_assoc_total : forall (a b c : livemodes) (e : expr) , tauRed (( (a # b)) # c) e ->
        (
          (exists (a' b' c' : livemodes), e = ( (a' # b')) # c' /\ tauRed (a # ( (b # c))) (a' # ( (b' # c'))))
          \/
          (exists (a' b' : livemodes) (c' : expr), e = ( (a' # b')) #> c' /\ is_value_of_expr c' /\ tauRed (a # ( (b # c))) (a' #> ( (b' #> c'))))
          \/
          (exists (a' c' : livemodes) (b' : expr), e = ( (a' #> b')) <# c' /\ is_value_of_expr b' /\   tauRed (a # ( (b # c))) (a' #> ( (b' <# c'))))
          \/
          (exists (a' c' : livemodes) (b' : expr), e = ( (a' #> b')) # c' /\ is_value_of_expr b'/\  tauRed (a # ( (b # c))) (a' # (  (b' <# c'))) /\  tauRed (a # ( (b # c))) (a' # (  ( ( b') # c'))) )
          \/
          (exists (b' c' : livemodes) (a' : expr), e = ( (a' <# b')) # c' /\ is_value_of_expr a' /\  tauRed (a # ( (b # c))) (  a' <# (  (b' # c'))) /\ tauRed (a # ( (b # c))) (  ( a') # (  (b' # c'))) )
          \/
          (exists (b' c' : livemodes) (a' : expr), e = ( (a' <# b')) <# c' /\ is_value_of_expr a' /\  tauRed (a # ( (b # c))) (a' <# (  (b' # c'))))
          \/
          (exists (a' : livemodes) (b' c' : expr), e = ( (a' #> b')) #> c' /\ is_value_of_expr b' /\ is_value_of_expr c'  /\  tauRed (a # ( (b # c))) (a' #> ( (( b') #> c'))) /\ tauRed (a # ( (b # c))) (a' # (  (( b') # ( c')))) )
          \/
          (exists ( b'  : livemodes) (a' c' : expr), e = ( (a' <# b')) #> c' /\ is_value_of_expr a' /\ is_value_of_expr c'  /\  tauRed (a # ( (b # c))) (a' <# (  (b' #> c'))) /\  tauRed (a # ( (b # c))) (( a') # ((  (b' # ( c'))))))
        ).
Proof.
 intros.
 assert (L:=H).
 induction a; induction b; induction c.
 apply fork_tau_behave_ec in H.
 destruct H.
 intuition.
 substs.
 left.
 apply fork_tau_behave_cc in H0.
 substs.
 exists (E_comp lab) (E_comp lab0) (E_comp lab1 ).
 intuition.
 apply star_refl.
 apply fork_tau_behave_cc in H0.
 substs.
 simpl in H2; intuition.
 (* E(CC) E *)
 apply fork_tau_behave_ee in H.
 intuition.
 destruct H0.
 destruct H.
 intuition.
 substs.
 apply fork_tau_behave_cc in H0.
 substs.
 left.
 exists (E_comp lab) (E_comp lab0) ( x0).
 intuition.
 apply fork_tau_ce_push_h.
 apply fork_tau_ce_push_h.
 assumption.

 destruct H.
 destruct H.
 intuition.
 substs.
 apply fork_tau_behave_cc in H.
 substs.
 branch 2.
 exists (E_comp lab) (E_comp lab0) ( x0).
 intuition.
 apply star_trans with (y:=(E_comp lab #  (E_comp lab0 #> x0))).
 apply fork_tau_ce_push_h.
 apply star_trans with (y:=(E_comp lab0 #  x0)).
 apply fork_tau_ce_push_h.
 assumption.
 apply S_star with (y:=(E_comp lab0 #> x0)).
 apply tStep with (s:=S_Second).
 apply JO_red_forkdeath2.
 assumption.
 apply star_refl.
 apply S_star with (y:=(E_comp lab #> (E_comp lab0 #> x0))).
 apply tStep with (s:=S_Second).
 apply JO_red_forkdeath2.
 simpl; auto.
 apply star_refl.

 destruct H.
 destruct H.
 intuition.
 substs.
 apply fork_tau_behave_cc in H.
 substs.
 simpl in H0; intuition.
 (* E(CE) C *)
 apply fork_tau_behave_ec in H.
 destruct H.
 intuition.
 substs.
 apply fork_tau_behave_ce in H0.
 destruct H0.
 intuition.
 substs.
 intuition.
 left.
 exists (E_comp lab) ( x0) ( E_comp lab0).
 intuition.
 apply fork_tau_ce_push_h.
 apply fork_tau_ec_push_h.
 assumption.
 substs.
 branch 4.
 exists (E_comp lab) (E_comp lab0) x0.
 intuition.
 apply fork_tau_ce_push_h.
 apply star_S with (y:=( x0 # E_comp lab0)).
 apply fork_tau_ec_push_h.
 assumption.
 apply tStep with (s:=S_First).
 apply JO_red_forkdeath1.
 assumption.
 apply fork_tau_ce_push_h.
 apply fork_tau_ec_push_h.
 assumption.
 substs.
 apply fork_tau_behave_ce in H0.
 destruct H0.
 intuition.
 substs.
 simpl in H2.
 intuition.
 substs.
 branch 3.
 exists (E_comp lab) (E_comp lab0) x0.
 intuition.
 apply star_trans with (y:=(E_comp lab #  ( x0 <# E_comp lab0))).
 apply fork_tau_ce_push_h.
 apply star_trans with (y:=( x0 # E_comp lab0)).
 apply fork_tau_ec_push_h.
 assumption.
 apply S_star with (y:=(x0 <# E_comp lab0)).
 apply tStep with (s:=S_First).
 apply JO_red_forkdeath1.
 assumption.
 apply star_refl.
 apply S_star with (y:= (E_comp lab #> (x0 <# E_comp lab0))).
 apply tStep with (s:=S_Second).
 apply JO_red_forkdeath2.
 simpl; auto.
 apply star_refl.
 

 (* E(CE) E *)
 apply fork_tau_behave_ee in H.
 intuition.
 destruct  H0.
 destruct H.
 intuition.
 substs.
 apply fork_tau_behave_ce in H0.
 destruct H0.
 intuition.
 substs.
 left.
 exists (E_comp lab) ( x1) ( x0).
 intuition.
 apply fork_tau_ce_push_h.
 apply fork_tau_push_ee_12.
 assumption.
 assumption.
 substs.
 branch 4.
 exists (E_comp lab) ( x0) (x1).
 intuition.
 apply fork_tau_ce_push_h.
 apply star_S with (y:=( x1 #  x0)).
 apply fork_tau_push_ee_12.
 assumption.
 assumption.
 apply tStep with (s:=S_First).
 apply JO_red_forkdeath1.
 assumption.
 apply fork_tau_ce_push_h.
 apply fork_tau_push_ee_12.
 assumption.
 assumption.
 destruct H.
 destruct H.
 intuition.
 substs.
 apply fork_tau_behave_ce in H.
 destruct H.
 intuition.
 substs.
 branch 2.
 exists (E_comp lab) ( x1) ( x0).
 intuition.
 apply star_trans with (y:=(E_comp lab #  ( x1 #> x0))).
 apply fork_tau_ce_push_h.
 apply star_trans with (y:=( x1 #  x0)).
 apply fork_tau_push_ee_12.
 assumption.
 assumption.
 apply S_star with (y:=( x1 #> x0)).
 apply tStep with (s:=S_Second).
 apply JO_red_forkdeath2.
 assumption.
 apply star_refl.
 apply S_star with (y:=(E_comp lab #> ( x1 #> x0))).
 apply tStep with (s:=S_Second).
 apply JO_red_forkdeath2.
 simpl; auto.
 apply star_refl.
 
 substs.
 branch 7.
 exists (E_comp lab) (x1) (x0).
 intuition.
 apply star_S with (y:=(E_comp lab #  ( x1 #> x0))).
 apply fork_tau_ce_push_h.
 apply star_S with (y:=( x1 #  x0)).
 apply fork_tau_push_ee_12.
 assumption.
 assumption.
 apply tStep with (s:=S_Second).
 apply JO_red_forkdeath2.
 assumption.
 apply tStep with (s:=S_Second).
 apply JO_red_forkdeath2.
 simpl; auto.
 apply fork_tau_ce_push_h.
 apply fork_tau_push_ee_12.
 assumption.
 assumption.
 destruct H.
 destruct H.
 intuition.
 substs.
 apply fork_tau_behave_ce in H.
 destruct H.
 intuition.
 substs.
 simpl in H0; intuition.
 substs.
 branch 3.
 exists (E_comp lab) ( x0) (x1).
 intuition.
 apply star_S with (y:=(E_comp lab # ( (x1 <#  x0)))).
 apply fork_tau_ce_push_h.
 apply star_S with (y:=( x1 #  x0)).
 apply fork_tau_push_ee_12.
 assumption.
 assumption.
 apply tStep with (s:=S_First).
 apply JO_red_forkdeath1.
 assumption.
 apply tStep with (s:=S_Second).
 apply JO_red_forkdeath2.
 simpl; auto.

 (* E(EC) C *)
 apply fork_tau_behave_ec in H.
 destruct H.
 intuition.
 substs.
 apply fork_tau_behave_ec in H0.
 destruct H0.
 intuition.
 substs.
 intuition.
 left.
 exists  ( x0) (E_comp lab) ( E_comp lab0).
 intuition.
 apply fork_tau_push_ee_1.
 assumption.
 substs.
 branch 5.
 exists (E_comp lab) (E_comp lab0) x0.
 intuition.
 apply star_S with (y:=( x0 #  (E_comp lab # E_comp lab0))).
 apply fork_tau_push_ee_12.
 apply star_refl.
 assumption.
 apply tStep with (s:=S_First).
 apply JO_red_forkdeath1.
 assumption.
 apply fork_tau_push_ee_12.
 apply star_refl.
 assumption.
 
 substs.
 apply fork_tau_behave_ec in H0.
 destruct H0.
 intuition.
 substs.
 simpl in H2.
 intuition.
 substs.
 branch 6.
 exists (E_comp lab) (E_comp lab0) x0.
 intuition.
 apply star_S with (y:=( x0 #  (E_comp lab # E_comp lab0))).
 apply fork_tau_push_ee_12.
 apply star_refl.
 assumption.
 apply tStep with (s:=S_First).
 apply JO_red_forkdeath1.
 assumption.
 (* E(EC) E *)
 apply fork_tau_behave_ee in H.
 intuition.
 destruct  H0.
 destruct H.
 intuition.
 substs.
 apply fork_tau_behave_ec in H0.
 destruct H0.
 intuition.
 substs.
 left.
 exists ( x1) (E_comp lab) ( x0).
 intuition.
 apply fork_tau_push_ee_12.
 apply fork_tau_ce_push_h.
 assumption.
 assumption.
 substs.
 branch 5.
 exists (E_comp lab) ( x0) (x1).
 intuition.
 apply star_S with (y:=( x1 #  (E_comp lab #  x0))).
 apply fork_tau_push_ee_12.
 apply fork_tau_ce_push_h.
 assumption.
 assumption.
 apply tStep with (s:=S_First).
 apply JO_red_forkdeath1.
 assumption.
 apply fork_tau_push_ee_12.
 apply fork_tau_ce_push_h.
 assumption.
 assumption.
 destruct H.
 destruct H.
 intuition.
 substs.
 apply fork_tau_behave_ec in H.
 destruct H.
 intuition.
 substs.
 branch 2.
 exists ( x1) (E_comp lab) ( x0).
 intuition.
 apply star_trans with (y:=( x1 #  (E_comp lab #> x0))).
 apply fork_tau_push_ee_12.
 apply star_trans with (y:=(E_comp lab #  x0)).
 apply fork_tau_ce_push_h.
 assumption.
 apply S_star with (y:=(E_comp lab #> x0)).
 apply tStep with (s:=S_Second).
 apply JO_red_forkdeath2.
 assumption.
 apply star_refl.
 assumption.
 apply S_star with (y:=( x1 #> (E_comp lab #> x0))).
 apply tStep with (s:=S_Second).
 apply JO_red_forkdeath2.
 simpl; auto.
 apply star_refl.
 substs.
 branch 8.
 exists (E_comp lab) (x1) (x0).
 intuition.
 apply star_S with (y:=(( x1) #  (E_comp lab #> x0))).
 apply fork_tau_push_ee_12.
 apply star_S with (y:=(E_comp lab #  x0)).
 apply fork_tau_ce_push_h.
 assumption.
 apply tStep with (s:=S_Second); apply JO_red_forkdeath2; assumption.
 assumption.
 apply tStep with (s:=S_First); apply JO_red_forkdeath1; assumption.
 apply fork_tau_push_ee_12.
 apply fork_tau_ce_push_h.
 assumption.
 assumption.
 destruct H.
 destruct H.
 intuition.
 substs.
 apply fork_tau_behave_ec in H.
 destruct H.
 intuition.
 substs.
 simpl in H0; intuition.
 substs.
 branch 6.
 exists (E_comp lab) ( x0) (x1).
 intuition.
 apply star_S with (y:=( x1 #  (E_comp lab #  x0))).
 apply fork_tau_push_ee_12.
 apply fork_tau_ce_push_h; assumption.
 assumption.
 apply tStep with (s:=S_First); apply JO_red_forkdeath1;  assumption.
 (* E(EE) C *)
 apply fork_tau_behave_ec in H.
 destruct H.
 intuition.
 substs.
 apply fork_tau_behave_ee in H0.
 intuition.
 destruct H.
 destruct H.
 intuition.
 substs.
 left.
 exists  ( x0) ( x1) ( E_comp lab).
 intuition.
 apply fork_tau_push_ee_12.
 apply fork_tau_ec_push_h.
 assumption.
 assumption.
 destruct H0.
 destruct H.
 intuition.
 substs.
 branch 4.
 exists ( x0) (E_comp lab) x1.
 intuition.
 apply fork_tau_push_ee_12.
 apply star_S with (y:=( x1 # E_comp lab)).
 apply fork_tau_ec_push_h.
 assumption.
 apply tStep with (s:=S_First).
 apply JO_red_forkdeath1.
 assumption.
 assumption.
 apply fork_tau_push_ee_12.
 apply fork_tau_ec_push_h.
 assumption.
 assumption.
 destruct H0.
 destruct H.
 intuition.
 substs.
 branch 5.
 exists ( x1) (E_comp lab) x0.
 intuition.
 apply star_S with (y:=( x0 #  ( x1 # E_comp lab))).
 apply fork_tau_push_ee_12.
 apply fork_tau_ec_push_h; assumption.
 assumption.
 apply tStep with (s:=S_First).
 apply JO_red_forkdeath1.
 assumption.
 apply fork_tau_push_ee_12.
 apply fork_tau_ec_push_h.
 assumption.
 assumption.
 substs.
 apply fork_tau_behave_ee in H0.
 intuition.
 destruct H.
 destruct H.
 intuition.
 substs.
 simpl in H2; intuition.
 destruct H0.
 destruct H.
 intuition.
 substs.
 branch 3.
 exists ( x0) (E_comp lab) x1.
 intuition.
 apply star_S with (y:=( x0 # ( (x1 <# E_comp lab)))).
 apply fork_tau_push_ee_12.
 apply star_S with (y:=( x1 # E_comp lab)).
 apply fork_tau_ec_push_h.
 assumption.
 apply tStep with (s:=S_First).
 apply JO_red_forkdeath1.
 assumption.
 assumption.
 apply tStep with (s:=S_Second).
 apply JO_red_forkdeath2.
 simpl; auto.
 
 destruct H0.
 destruct H.
 intuition.
 substs.
 branch 6.
 exists ( x1) (E_comp lab) x0.
 intuition.
 apply star_S with (y:=( x0 #  ( x1 # E_comp lab))).
 apply fork_tau_push_ee_12.
 apply fork_tau_ec_push_h; assumption.
 assumption.
 apply tStep with (s:=S_First).
 apply JO_red_forkdeath1.
 assumption.
 (* E(EE) E *)
 apply fork_tau_behave_ee in H.
 intuition.
 destruct  H0.
 destruct H.
 intuition.
 substs.
 apply fork_tau_behave_ee in H0.
 intuition.
 destruct H1.
 destruct H0.
 intuition.
 substs.
 left.
 exists ( x1) ( x2) ( x0).
 intuition.
 apply fork_tau_push_ee_12.
 apply fork_tau_push_ee_12.
 assumption.
 assumption.
 assumption.
 destruct H0.
 destruct H0.
 intuition.
 substs.
 branch 4.
 exists ( x1) ( x0) (x2).
 intuition.
 apply fork_tau_push_ee_12.
 apply star_S with (y:=( x2 #  x0)).
 apply fork_tau_push_ee_12.
 assumption.
 assumption.
 apply tStep with (s:=S_First).
 apply JO_red_forkdeath1.
 assumption.
 assumption.
 apply fork_tau_push_ee_12.
 apply fork_tau_push_ee_12.
 assumption. 
 assumption.
 assumption.
 destruct H0.
 destruct H0.
 intuition.
 substs.
 branch 5.
 exists ( x2) ( x0) x1.
 intuition.
 apply star_S with (y:=( x1 #  ( x2 #  x0))).
 apply fork_tau_push_ee_12.
 apply fork_tau_push_ee_12.
 assumption.
 assumption.
 assumption.
 apply tStep with (s:=S_First).
 apply JO_red_forkdeath1.
 assumption.
 apply fork_tau_push_ee_12.
 apply fork_tau_push_ee_12.
 assumption. 
 assumption.
 assumption.
 destruct H.
 destruct H.
 intuition.
 substs.
 apply fork_tau_behave_ee in H.
 intuition.
 destruct H2.
 destruct H.
 intuition.
 substs.
 branch 2.
 exists ( x1) ( x2) ( x0).
 intuition.
 apply star_S with (y:=( x1 #  ( x2 #> x0))).
 apply fork_tau_push_ee_12.
 apply star_S with (y:=( x2 #  x0)).
 apply fork_tau_push_ee_12.
 assumption.
 assumption.
 apply tStep with (s:=S_Second).
 apply JO_red_forkdeath2.
 assumption.
 assumption.
 apply tStep with (s:=S_Second).
 apply JO_red_forkdeath2.
 simpl; auto.

 destruct H.
 destruct H.
 intuition.
 substs.
 branch 7.
 exists ( x1) (x2) (x0).
 intuition.
 apply star_S with (y:=( x1 #  ( x2 #> x0))).
 apply fork_tau_push_ee_12.
 apply star_S with (y:=( x2 #  x0)).
 apply fork_tau_push_ee_12.
 assumption.
 assumption.
 apply tStep with (s:=S_Second).
 apply JO_red_forkdeath2.
 assumption.
 assumption.
 apply tStep with (s:=S_Second).
 apply JO_red_forkdeath2.
 simpl; auto.
 apply fork_tau_push_ee_12.
 apply fork_tau_push_ee_12.
 assumption.
 assumption.
 assumption.
 destruct H.
 destruct H.
 intuition.
 substs.
 branch 8.
 exists ( x2) x1 x0.
 intuition.
 apply star_S with (y:=(( x1) #  ( x2 #> x0))).
 apply fork_tau_push_ee_12.
 apply star_S with (y:=( x2 #  x0)).
 apply fork_tau_push_ee_12.
 assumption.
 assumption.
 apply tStep with (s:=S_Second); apply JO_red_forkdeath2; assumption.
 assumption.
 apply tStep with (s:=S_First); apply JO_red_forkdeath1; assumption.
 apply fork_tau_push_ee_12.
 apply fork_tau_push_ee_12.
 assumption.
 assumption.
 assumption.
 destruct H.
 destruct H.
 intuition.
 substs.
 apply fork_tau_behave_ee in H.
 intuition.
 destruct H2.
 destruct H.
 intuition.
 substs.
 simpl in H0; intuition.
 destruct H.
 destruct H.
 intuition.
 substs.
 branch 3.
 exists ( x1) ( x0) (x2).
 intuition.
 apply star_trans with (y:= ( x1 # ( (x2 <#  x0)))).
 apply fork_tau_push_ee_12.
 apply star_trans with (y:=( x2 #  x0)).
 apply fork_tau_push_ee_12.
 assumption.
 assumption.
 apply S_star with (y:=(x2 <#  x0)).
 apply tStep with (s:=S_First).
 apply JO_red_forkdeath1.
 assumption.
 apply star_refl.
 assumption.
 apply S_star with (y:= ( x1 #> (x2 <#  x0))).
 apply tStep with (s:=S_Second).
 apply JO_red_forkdeath2.
 simpl; auto.
 apply star_refl.
 destruct H.
 destruct H.
 intuition.
 substs.
 branch 6.
 exists ( x2) ( x0) x1.
 intuition.
 apply star_S with (y:=( x1 #  ( x2 #  x0))).
 apply fork_tau_push_ee_12.
 apply fork_tau_push_ee_12.
 assumption.
 assumption.
 assumption.
 apply tStep with (s:=S_First).
 apply JO_red_forkdeath1.
 assumption.
Qed.

Lemma fork_lab_assoc_total : forall (a b c : livemodes) (e : expr) (l : label) , labRed l (( (a # b)) # c) e ->
        (
          (exists (a' b' c' : livemodes), e = ( (a' # b')) # c' /\ labRed l (a # ( (b # c))) (a' # ( (b' # c'))))
          \/
          (exists (a' b' : livemodes) (c' : expr), e = ( (a' # b')) #> c' /\ is_value_of_expr c' /\ labRed l (a # ( (b # c))) (a' #> ( (b' #> c'))))
          \/
          (exists (a' c' : livemodes) (b' : expr), e = ( (a' #> b')) <# c' /\ is_value_of_expr b' /\   labRed l  (a # ( (b # c))) (a' #> ( (b' <# c'))))
          \/
          (exists (a' c' : livemodes) (b' : expr), e = ( (a' #> b')) # c' /\ is_value_of_expr b'/\  labRed l (a # ( (b # c))) (a' # (  (b' <# c'))) )
          \/
          (exists (b' c' : livemodes) (a' : expr), e = ( (a' <# b')) # c' /\ is_value_of_expr a' /\  labRed l (a # ( (b # c))) (  a' <# (  (b' # c'))) )
          \/
          (exists (b' c' : livemodes) (a' : expr), e = ( (a' <# b')) <# c' /\ is_value_of_expr a' /\  labRed l (a # ( (b # c))) (a' <# (  (b' # c'))))
          \/
          (exists (a' : livemodes) (b' c' : expr), e = ( (a' #> b')) #> c' /\ is_value_of_expr b' /\ is_value_of_expr c'  /\  labRed l (a # ( (b # c))) (a' #> ( (( b') #> c'))))
          \/
          (exists ( b'  : livemodes) (a' c' : expr), e = ( (a' <# b')) #> c' /\ is_value_of_expr a' /\ is_value_of_expr c'  /\  labRed l (a # ( (b # c))) (a' <# (  (b' #> c'))))
          \/
          (exists (x : livemodes) (q' : expr), e = ( (x #> (E_constant CONST_unit))) #> q' /\ tauRed (a #  (b # c)) (x #  (E_comp l #  q')) /\ is_value_of_expr q' /\ labRed l (a #  (b # c)) (x #> (E_constant CONST_unit <# ( q'))))
        ).
Proof.
 intros.
 inversion H.
 substs.
 intuition.
 apply fork_tau_assoc_total in H1.
 intuition.
 (* B1 *)
 destruct H2.
 destruct H1.
 destruct H1.
 destruct H1.
 substs.
 inversion H0.
 (* B1 - L1 *)
 substs.
 inversion H8.
 (* B1 - L1 - L1 *)
 substs.
 apply fork_tau_assoc_total in H3.
 intuition.
 branch 1.
 destruct H1 as [ a' H1 ]; destruct H1 as [ b' H1 ]; destruct H1 as [ c' H1 ]; exists a' b' c';
 intuition;
 apply lab_r with (e1:=( e0 #  (x0 # x1)))  (e2:=( e''0 #  (x0 # x1))) (s:=S_First);
 intuition;
 apply JO_red_forkmove1 with (s:=s);
 auto.
 branch 2;
 destruct H3 as [ a' H1 ]; destruct H1 as [ b' H1 ]; destruct H1 as [ c' H1 ];
 exists a' b' c';
 intuition;
 apply lab_r with (e1:=( e0 #  (x0 # x1)))  (e2:=( e''0 #  (x0 # x1))) (s:=S_First);
 intuition;
 apply JO_red_forkmove1 with (s:=s);
 auto.
 branch 3;
 destruct H1 as [ a' H1 ]; destruct H1 as [ b' H1 ]; destruct H1 as [ c' H1 ];
 exists a' b' c';
 intuition;
 apply lab_r with (e1:=( e0 #  (x0 # x1)))  (e2:=( e''0 #  (x0 # x1))) (s:=S_First);
 intuition;
 apply JO_red_forkmove1 with (s:=s);
 auto.
 branch 4;
 destruct H3 as [ a' H1 ]; destruct H1 as [ b' H1 ]; destruct H1 as [ c' H1 ];
 exists a' b' c';
 intuition;
 apply lab_r with (e1:=( e0 #  (x0 # x1)))  (e2:=( e''0 #  (x0 # x1))) (s:=S_First);
 intuition;
 apply JO_red_forkmove1 with (s:=s);
 auto.
 branch 5.
 destruct H1 as [ a' H1 ]; destruct H1 as [ b' H1 ]; destruct H1 as [ c' H1 ].
 exists a' b' c'.
 intuition.
 apply lab_r with (e1:=( e0 #  (x0 # x1)))  (e2:=( e''0 #  (x0 # x1))) (s:=S_First).
 intuition.
 apply JO_red_forkmove1 with (s:=s).
 auto.
 branch 6.
 destruct H3 as [ a' H1 ]; destruct H1 as [ b' H1 ]; destruct H1 as [ c' H1 ].
 exists a' b' c'.
 intuition.
 apply lab_r with (e1:=( e0 #  (x0 # x1)))  (e2:=( e''0 #  (x0 # x1))) (s:=S_First).
 intuition.
 apply JO_red_forkmove1 with (s:=s).
 auto.
 branch 7.
 destruct H1 as [ a' H1 ]; destruct H1 as [ b' H1 ]; destruct H1 as [ c' H1 ].
 exists a' b' c'.
 intuition.
 apply lab_r with (e1:=( e0 #  (x0 # x1)))  (e2:=( e''0 #  (x0 # x1))) (s:=S_First).
 intuition.
 apply JO_red_forkmove1 with (s:=s).
 auto.
 branch 8.
 destruct H1 as [ a' H1 ]; destruct H1 as [ b' H1 ]; destruct H1 as [ c' H1 ].
 left.
 exists a' b' c'.
 intuition.
 apply lab_r with (e1:=( e0 #  (x0 # x1)))  (e2:=( e''0 #  (x0 # x1))) (s:=S_First).
 intuition.
 apply JO_red_forkmove1 with (s:=s).
 auto.
 (* B1 - L1 - L2 *)
 substs.
 apply fork_tau_assoc_total in H3.
 intuition.
 branch 1;
 destruct H1 as [ a' H1 ]; destruct H1 as [ b' H1 ]; destruct H1 as [ c' H1 ]; exists a' b' c';
 intuition;
 apply lab_r with (e1:=(x #  ( e' # x1)))  (e2:=(x #  ( e''0 # x1))) (s:=S_Second);
 intuition;
 apply JO_red_forkmove2 with (s:=S_First);
 apply JO_red_forkmove1 with (s:=s);
 auto.
 branch 2;
 destruct H3 as [ a' H1 ]; destruct H1 as [ b' H1 ]; destruct H1 as [ c' H1 ]; exists a' b' c';
 intuition;
 apply lab_r with (e1:=(x #  ( e' # x1)))  (e2:=(x #  ( e''0 # x1))) (s:=S_Second);
 intuition;
 apply JO_red_forkmove2 with (s:=S_First);
 apply JO_red_forkmove1 with (s:=s);
 auto.
  branch 3;
 destruct H1 as [ a' H1 ]; destruct H1 as [ b' H1 ]; destruct H1 as [ c' H1 ]; exists a' b' c';
 intuition;
 apply lab_r with (e1:=(x #  ( e' # x1)))  (e2:=(x #  ( e''0 # x1))) (s:=S_Second);
 intuition;
 apply JO_red_forkmove2 with (s:=S_First);
 apply JO_red_forkmove1 with (s:=s);
 auto.
  branch 4;
 destruct H3 as [ a' H1 ]; destruct H1 as [ b' H1 ]; destruct H1 as [ c' H1 ]; exists a' b' c';
 intuition;
 apply lab_r with (e1:=(x #  ( e' # x1)))  (e2:=(x #  ( e''0 # x1))) (s:=S_Second);
 intuition;
 apply JO_red_forkmove2 with (s:=S_First);
 apply JO_red_forkmove1 with (s:=s);
 auto.
  branch 5;
 destruct H1 as [ a' H1 ]; destruct H1 as [ b' H1 ]; destruct H1 as [ c' H1 ]; exists a' b' c';
 intuition;
 apply lab_r with (e1:=(x #  ( e' # x1)))  (e2:=(x #  ( e''0 # x1))) (s:=S_Second);
 intuition;
 apply JO_red_forkmove2 with (s:=S_First);
 apply JO_red_forkmove1 with (s:=s);
 auto.
  branch 6;
 destruct H3 as [ a' H1 ]; destruct H1 as [ b' H1 ]; destruct H1 as [ c' H1 ]; exists a' b' c';
 intuition;
 apply lab_r with (e1:=(x #  ( e' # x1)))  (e2:=(x #  ( e''0 # x1))) (s:=S_Second);
 intuition;
 apply JO_red_forkmove2 with (s:=S_First);
 apply JO_red_forkmove1 with (s:=s);
 auto.
  branch 7;
 destruct H1 as [ a' H1 ]; destruct H1 as [ b' H1 ]; destruct H1 as [ c' H1 ]; exists a' b' c';
 intuition;
 apply lab_r with (e1:=(x #  ( e' # x1)))  (e2:=(x #  ( e''0 # x1))) (s:=S_Second);
 intuition;
 apply JO_red_forkmove2 with (s:=S_First);
 apply JO_red_forkmove1 with (s:=s);
 auto.
  branch 8; left;
 destruct H1 as [ a' H1 ]; destruct H1 as [ b' H1 ]; destruct H1 as [ c' H1 ]; exists a' b' c';
 intuition;
 apply lab_r with (e1:=(x #  ( e' # x1)))  (e2:=(x #  ( e''0 # x1))) (s:=S_Second);
 intuition;
 apply JO_red_forkmove2 with (s:=S_First);
 apply JO_red_forkmove1 with (s:=s);
 auto.
 (* B1 - L1 - L3 *)
 substs.
 induction x1.
 apply fork_tau_behave_ec in H3.
 destruct H3.
 intuition.
 substs.
 apply taured_val_id in H3.
 substs.
 branch 5.
 exists x0 (E_comp lab) (E_constant CONST_unit).
 intuition.
 simpl; auto.
 apply lab_r with (e1:=(E_comp l #  (x0 # E_comp lab))) (e2:=(E_constant CONST_unit <#  (x0 # E_comp lab))) (s:=S_First).
 intuition.
 apply JO_red_forkdocomp1.
 apply star_refl.
 simpl; auto.
 apply taured_val_id in H3.
 substs.
 branch 6.
 exists x0 (E_comp lab) (E_constant CONST_unit).
 intuition.
 apply lab_r with (e1:=(E_comp l #  (x0 # E_comp lab))) (e2:=(E_constant CONST_unit <#  (x0 # E_comp lab))) (s:=S_First).
 intuition.
 apply JO_red_forkdocomp1.
 apply star_refl.
 simpl; auto.
 apply fork_tau_behave_ee in H3.
 intuition.
 substs.
 destruct H1 as [p' H1]; destruct H1 as [q' H1]; destruct H1 as [ H1 H3 ]; destruct H3 as [ H3 H4 ]; substs.
 apply taured_val_id in H1; substs.
 branch 5.
 exists x0 ( q') (E_constant CONST_unit).
 intuition.
 simpl; auto.
 apply lab_r with (e1:=(E_comp l #  (x0 #  q'))) (e2:=(E_constant CONST_unit <#  (x0 #  q')))(s:=S_First).
 intuition.
 apply star_trans with (y:=(E_comp l #  (x0 #  expr5))).
 assumption.
 apply fork_tau_ce_push_h.
 induction x0.
 apply fork_tau_ce_push_h.
 assumption.
 apply fork_tau_push_ee_2.
 assumption.
 apply JO_red_forkdocomp1.
 apply star_refl.
 simpl; auto.
 destruct H3 as [p' H1]; destruct H1 as [q' H1]; destruct H1 as [ H1 H3 ]; destruct H3 as [ H3 H4 ]; destruct H4 as [ H4 H5 ]; substs.
 apply taured_val_id in H3; substs.
 branch 8. left.
 exists x0 (E_constant CONST_unit) q'.
 intuition.
 simpl; auto.
 apply lab_r with (e1:=(E_comp l #  (x0 #> q')))(e2:=(E_constant CONST_unit <#  (x0 #> q')))(s:=S_First).
 intuition.
 apply star_trans with (y:=(E_comp l #  (x0 #  expr5))).
 assumption.
 apply star_S with (y:=(E_comp l #  (x0 #  q'))).
 apply fork_tau_ce_push_h.
 induction x0.
 apply fork_tau_ce_push_h.
 assumption.
 apply fork_tau_push_ee_2.
 assumption.
 apply tStep with (s:=S_Second).
 apply JO_red_forkmove2 with (s:=S_Second).
 apply JO_red_forkdeath2.
 assumption.
 apply JO_red_forkdocomp1.
 apply star_refl.
 simpl; auto.
 destruct H3 as [p' H1]; destruct H1 as [q' H1]; destruct H1 as [ H1 H3 ]; destruct H3 as [ H3 H4 ]; destruct H4 as [ H4 H5 ]; substs.
 apply taured_val_id in H3; substs.
 branch 6.
 exists x0 ( q') (E_constant CONST_unit).
 intuition.
 apply lab_r with (e1:=(E_comp l #  (x0 #  q')))(e2:=(E_constant CONST_unit <#  (x0 #  q')))(s:=S_First).
 intuition.
 apply star_trans with (y:=(E_comp l #  (x0 #  expr5))).
 assumption.
 apply fork_tau_ce_push_h.
 induction x0.
 apply fork_tau_ce_push_h.
 assumption.
 apply fork_tau_push_ee_2.
 assumption.
 apply JO_red_forkdocomp1.
 apply star_refl.
 simpl; auto.
 (* B1 - L1 - L4 *)
 substs.
 induction x1.
 apply fork_tau_behave_ec in H3.
 destruct H3.
 intuition.
 substs.
 apply taured_val_id in H3.
 substs.
 branch 4.
 exists x (E_comp lab) (E_constant CONST_unit).
 intuition.
 simpl; auto.
 apply lab_r with (e1:=(x #  (E_comp l # E_comp lab)))(e2:=(x #  (E_constant CONST_unit <# E_comp lab)))(s:=S_Second).
 intuition.
 apply JO_red_forkmove2 with (s:=S_First).
 apply JO_red_forkdocomp1.
 apply star_refl.
 simpl; auto.
 apply taured_val_id in H3.
 substs.
 branch 3.
 exists x (E_comp lab) (E_constant CONST_unit).
 intuition.
 simpl; auto.
 apply lab_r with (e1:=(x #  (E_comp l # E_comp lab)))(e2:=(x #  (E_constant CONST_unit <# E_comp lab)))(s:=S_Second).
 intuition.
 apply JO_red_forkmove2 with (s:=S_First).
 apply JO_red_forkdocomp1.
 apply S_star with (y:=(x #> (E_constant CONST_unit <# E_comp lab))).
 apply tStep with (s:=S_Second).
 apply JO_red_forkdeath2.
 simpl; auto.
 apply star_refl.
 simpl; auto.
 apply fork_tau_behave_ee in H3.
 intuition.
 substs.
 destruct H1 as [p' H1]; destruct H1 as [q' H1]; destruct H1 as [ H1 H3 ]; destruct H3 as [ H3 H4 ]; substs.
 apply taured_val_id in H1; substs.
 branch 4.
 exists x ( q') (E_constant CONST_unit).
 intuition.
 simpl; auto.
 apply lab_r with (e1:=(x #  (E_comp l #  q'))) (e2:=(x #  (E_constant CONST_unit <#  q')))(s:=S_Second).
 intuition.
 apply star_trans with (y:=(x #  (E_comp l #  expr5))).
 assumption.
 induction x.
 apply fork_tau_ce_push_h.
 apply fork_tau_ce_push_h.
 assumption.
 apply fork_tau_push_ee_2.
 apply fork_tau_ce_push_h.
 assumption.
 apply JO_red_forkmove2 with (s:=S_First).
 apply JO_red_forkdocomp1.
 apply star_refl.
 simpl; auto.
 destruct H3 as [p' H1]; destruct H1 as [q' H1]; destruct H1 as [ H1 H3 ]; destruct H3 as [ H3 H4 ]; destruct H4 as [ H4 H5 ]; substs.
 apply taured_val_id in H3; substs.
 branch 8. right.
 exists x q'.
 intuition.
 simpl; auto.
 assert (tauRed (a #  (b # c)) (x #  (E_comp l #  q'))).
 apply star_trans with (y:=(x #  (E_comp l #  expr5))).
 assumption.
 induction x.
 apply fork_tau_ce_push_h.
 apply fork_tau_ce_push_h.
 assumption.
 apply fork_tau_push_ee_2.
 apply fork_tau_ce_push_h.
 assumption.
 assumption.
 apply lab_r with (e1:=(x # ( ( (E_comp l) #  q'))))(e2:=(x #  ( (E_constant CONST_unit) <#  q')))(s:=S_Second).
 intuition.
 apply star_trans with (y:=(x #  (E_comp l #  expr5))).
 assumption.
 induction x.
 apply fork_tau_ce_push_h.
 apply fork_tau_ce_push_h.
 assumption.
 apply fork_tau_push_ee_2.
 apply fork_tau_ce_push_h.
 assumption.
 apply JO_red_forkmove2 with (s:=S_First).
 apply JO_red_forkdocomp1.
 apply S_star with (y:=(x #> (E_constant CONST_unit <#  q'))).
 apply tStep with (s:=S_Second).
 apply JO_red_forkdeath2.
 simpl; auto.
 apply star_refl.
 simpl; auto. 
 destruct H3 as [p' H1]; destruct H1 as [q' H1]; destruct H1 as [ H1 H3 ]; destruct H3 as [ H3 H4 ]; destruct H4 as [ H4 H5 ]; substs.
 apply taured_val_id in H3; substs.
 branch 3.
 exists x ( q') (E_constant CONST_unit).
 intuition.
 apply lab_r with (e1:=(x #  (E_comp l #  q')))(e2:=(x # (((E_constant CONST_unit) <#  q'))))(s:=S_Second).
 intuition.
 apply star_trans with (y:=(x #  (E_comp l #  expr5))).
 assumption.
 induction x.
 apply fork_tau_ce_push_h.
 apply fork_tau_ce_push_h.
 assumption.
 apply fork_tau_push_ee_2.
 apply fork_tau_ce_push_h.
 assumption.
 apply JO_red_forkmove2 with (s:=S_First).
 apply JO_red_forkdocomp1.
 apply  S_star with (y:=(x #> (E_constant CONST_unit <#  q'))).
 apply tStep with (s:=S_Second).
 apply JO_red_forkdeath2.
 simpl;auto.
 apply star_refl.
 simpl; auto.
 (* B1 - L1 - L5 *)
 apply red_not_value in H10; simpl in H10; intuition.
 (* B1 - L1 - L6 *)
 apply red_not_value in H9; simpl in H9; intuition.
 (* B1 - L2 *)
 substs.
 apply fork_tau_assoc_total in H3.
 intuition.
 branch 1.
 destruct H1 as [ a' H1 ]; destruct H1 as [ b' H1 ]; destruct H1 as [ c' H1 ]; exists a' b' c';
 intuition.
 apply lab_r with (e1:=( x #  (x0 #  e')))  (e2:=(x #  (x0 #  e''))) (s:=S_Second);
 intuition.
 apply JO_red_forkmove2 with (s:=S_Second).
 apply JO_red_forkmove2 with (s:=s0).
 auto.
 branch 2;
 destruct H3 as [ a' H1 ]; destruct H1 as [ b' H1 ]; destruct H1 as [ c' H1 ]; exists a' b' c';
 intuition.
 apply lab_r with (e1:=( x #  (x0 #  e')))  (e2:=(x #  (x0 #  e''))) (s:=S_Second);
 intuition.
 apply JO_red_forkmove2 with (s:=S_Second).
 apply JO_red_forkmove2 with (s:=s0).
 auto.
 branch 3;
 destruct H1 as [ a' H1 ]; destruct H1 as [ b' H1 ]; destruct H1 as [ c' H1 ]; exists a' b' c';
 intuition.
 apply lab_r with (e1:=( x #  (x0 #  e')))  (e2:=(x #  (x0 #  e''))) (s:=S_Second);
 intuition.
 apply JO_red_forkmove2 with (s:=S_Second).
 apply JO_red_forkmove2 with (s:=s0).
 auto.
 branch 4;
 destruct H3 as [ a' H1 ]; destruct H1 as [ b' H1 ]; destruct H1 as [ c' H1 ]; exists a' b' c';
 intuition.
 apply lab_r with (e1:=( x #  (x0 #  e')))  (e2:=(x #  (x0 #  e''))) (s:=S_Second);
 intuition.
 apply JO_red_forkmove2 with (s:=S_Second).
 apply JO_red_forkmove2 with (s:=s0).
 auto.
 branch 5.
 destruct H1 as [ a' H1 ]; destruct H1 as [ b' H1 ]; destruct H1 as [ c' H1 ]; exists a' b' c';
 intuition.
 apply lab_r with (e1:=( x #  (x0 #  e')))  (e2:=(x #  (x0 #  e''))) (s:=S_Second);
 intuition.
 apply JO_red_forkmove2 with (s:=S_Second).
 apply JO_red_forkmove2 with (s:=s0).
 auto.
 branch 6.
 destruct H3 as [ a' H1 ]; destruct H1 as [ b' H1 ]; destruct H1 as [ c' H1 ]; exists a' b' c';
 intuition.
 apply lab_r with (e1:=( x #  (x0 #  e')))  (e2:=(x #  (x0 #  e''))) (s:=S_Second);
 intuition.
 apply JO_red_forkmove2 with (s:=S_Second).
 apply JO_red_forkmove2 with (s:=s0).
 auto.
 branch 7.
 destruct H1 as [ a' H1 ]; destruct H1 as [ b' H1 ]; destruct H1 as [ c' H1 ]; exists a' b' c';
 intuition.
 apply lab_r with (e1:=( x #  (x0 #  e')))  (e2:=(x #  (x0 #  e''))) (s:=S_Second);
 intuition.
 apply JO_red_forkmove2 with (s:=S_Second).
 apply JO_red_forkmove2 with (s:=s0).
 auto.
 branch 8.
 left.
 destruct H1 as [ a' H1 ]; destruct H1 as [ b' H1 ]; destruct H1 as [ c' H1 ]; exists a' b' c';
 intuition.
 apply lab_r with (e1:=( x #  (x0 #  e')))  (e2:=(x #  (x0 #  e''))) (s:=S_Second);
 intuition.
 apply JO_red_forkmove2 with (s:=S_Second).
 apply JO_red_forkmove2 with (s:=s0).
 auto.
 (* B1 - L3 *)
 substs.
 apply taured_val_id in H3.
 substs.
 branch 2.
 exists x x0 (E_constant CONST_unit).
 intuition.
 simpl; auto.
 apply lab_r with (e1:=(x #  (x0 # E_comp l))) (e2:=(x #  (x0 #> E_constant CONST_unit))) (s:=S_Second).
 intuition.
 apply JO_red_forkmove2 with (s:=S_Second).
 apply JO_red_forkdocomp2.
 apply S_star with (y:=(x #> (x0 #> E_constant CONST_unit))).
 apply tStep with (s:=S_Second).
 apply JO_red_forkdeath2.
 simpl; auto.
 auto.
 simpl; auto.
 (* B1 - L4 *)
 apply red_not_value in H9; simpl in H9; intuition.
 (* B1 - L5 *)
 apply red_not_value in H8; simpl in H8; intuition.
 (* B2 *)
 destruct H1.
 destruct H1.
 destruct H1.
 destruct H1.
 substs.
 apply red_not_value in H0; simpl in H0; intuition.
 (* B3 *)
 destruct H2.
 destruct H1.
 destruct H1.
 destruct H1.
 substs.
 apply red_not_value in H0; simpl in H0; intuition.
 (* B4  (a' #> b') # c' *)
 destruct H1.
 destruct H1.
 destruct H1.
 destruct H1.
 substs.
 inversion H0.
 (* B4 - L1 *)
 substs.
 apply red_not_value in H8; simpl in H8; intuition.
 (* B4 - L2 *)
 substs.
 apply fork_tau_behave_ee in H3.
 intuition.
  (* B4-L2-T1 *)
  destruct H4.
  destruct H3.
  destruct H3.
  destruct H4.
  substs.
  apply taured_val_id in H3.
  substs.
  branch 4.
  exists x ( x2) x1.
  intuition.
  apply lab_r with (e1:=( x #  ( x1 #  e')))(e2:=( x #  ( x1 #  e'')))(s:=S_Second).
 intuition.
 apply JO_red_forkmove2 with (s:=S_Second).
  apply JO_red_forkmove2 with (s:=s0).
 assumption.
 apply star_trans with (y:=( x #  ( x1 #  x2))).
 induction x.
 apply fork_tau_ce_push_h.
 apply fork_tau_push_ee_2.
 assumption.
 
 apply fork_tau_push_ee_2.
 apply fork_tau_push_ee_12.
 assumption.
 apply star_refl.
 apply S_star with (y:=(x #  (x1 <#  x2))).
 apply tStep with (s:=S_Second).
 apply JO_red_forkmove2 with (s:=S_First).
 apply JO_red_forkdeath1.
 simpl; auto.
 apply star_refl.
 simpl; auto.
  (* B4-L2-T2 *)
  destruct H3.
  destruct H3.
  destruct H3.
  destruct H4.
  destruct H6.
  substs.
  apply taured_val_id in H4.
  substs.
  branch 7.
  exists x x1 x2.
  intuition.
  apply lab_r with (e1:=(x #  ( x1 #  e')))(e2:=(x #  ( x1 #  e'')))(s:=S_Second).
 intuition.
 apply JO_red_forkmove2 with (s:=S_Second).
  apply JO_red_forkmove2 with (s:=s0).
 assumption.
 apply star_trans with (y:=(x #  ( x1 #  x2))).
 
 induction x.
 apply fork_tau_ce_push_h.
 apply fork_tau_push_ee_2.
 
 assumption.
 apply fork_tau_push_ee_2.
 apply fork_tau_push_ee_2.
 assumption.
 apply S_star with (y:=( x #  ( x1 #> x2))).
 apply tStep with (s:=S_Second).
 apply JO_red_forkmove2 with (s:=S_Second).
 apply JO_red_forkdeath2.
 assumption.
 apply S_star with (y:=(x #> ( x1 #> x2))).
 apply tStep with (s:=S_Second).
 apply JO_red_forkdeath2.
 simpl; auto.
 simpl; auto.
 simpl; auto.
  (* B4-L2-T3 *)
  destruct H3.
  destruct H3.
  destruct H3.
  destruct H4.
  destruct H6.
  substs.
  apply taured_val_id in H4.
  substs.
  branch 3.
  exists x ( x2) x1.
  intuition.
  apply lab_r with (e1:=(x #  ( x1 #  e')))(e2:=(x #  ( x1 #  e'')))(s:=S_Second).
 intuition.
 apply JO_red_forkmove2 with (s:=S_Second).
  apply JO_red_forkmove2 with (s:=s0).
 assumption.
 apply star_trans with (y:=(x #  ( x1 #  x2))).

 induction x.
 apply fork_tau_ce_push_h.
  apply fork_tau_push_ee_2.
 assumption.
 apply fork_tau_push_ee_2.
  apply fork_tau_push_ee_2.
 assumption.
 apply S_star with (y:=(x #  (x1 <#  x2))).
 apply tStep with (s:=S_Second).
 apply JO_red_forkmove2 with (s:=S_First).
 apply JO_red_forkdeath1.
 assumption.
 apply S_star with (y:=(x #> (x1 <#  x2))).
 apply tStep with (s:=S_Second).
 apply JO_red_forkdeath2.
 assumption.
 simpl; auto.
 simpl; auto.
 (* B4 - L3 *)
 substs.
 branch 7.
 apply taured_val_id in H3.
 substs.
 exists x x1 (E_constant CONST_unit).
 intuition.
 simpl; auto.
 apply lab_r with (e1:=(x #  ( x1 # E_comp l)))(e2:=(x #  ( x1 #> (E_constant CONST_unit))))(s:=S_Second).
 intuition.
 apply JO_red_forkmove2 with (s:=S_Second).
 apply JO_red_forkdocomp2.
 apply S_star with (y:=(x #> ( x1 #> E_constant CONST_unit))).
 apply tStep with (s:=S_Second).
 apply JO_red_forkdeath2.
 simpl; auto.
 apply star_refl.
 simpl; auto.
 (* B4 - L4 *)
 substs.
 apply red_not_value in H9; simpl in H9; intuition.
 (* B4 - L5 *)
 apply red_not_value in H8; simpl in H8; intuition.
 (* B5 *)
 destruct H2.
 destruct H1.
 destruct H1.
 destruct H1.
 substs.
 inversion H0.
 (* B5 - L1 *)
 substs.
 apply red_not_value in H8; simpl in H8; intuition.
 (* B5 - L2 *)
 substs.
 apply fork_tau_behave_ee in H3.
 intuition.
  (* B5-L2-T1 *)
  destruct H4.
  destruct H3.
  destruct H3.
  destruct H4.
  substs.
  apply taured_val_id in H3.
  substs.
  branch 5.
  exists x ( x2) x1.
  intuition.
  apply lab_r with (e1:=( x1 #  (x #  e')))(e2:=( x1 #  (x #  e'')))(s:=S_Second).
 intuition.
 apply JO_red_forkmove2 with (s:=S_Second).
  apply JO_red_forkmove2 with (s:=s0).
 assumption.
 apply star_trans with (y:=( x1 #  (x #  x2))).
 apply fork_tau_push_ee_12.
 induction x.
 apply fork_tau_ce_push_h.
 assumption.
 apply fork_tau_push_ee_2.
 assumption.
 apply star_refl.
 apply S_star with (y:=(x1 <#  (x #  x2))).
 apply tStep with (s:=S_First).
 apply JO_red_forkdeath1.
 simpl; auto.
 apply star_refl.
 simpl; auto.
  (* B5-L2-T2 *)
  destruct H3.
  destruct H3.
  destruct H3.
  destruct H4.
  destruct H6.
  substs.
  apply taured_val_id in H4.
  substs.
  branch 8.
  left.
  exists x x1 x2.
  intuition.
  apply lab_r with (e1:=( x1 #  (x #  e')))(e2:=( x1 #  (x #  e'')))(s:=S_Second).
 intuition.
 apply JO_red_forkmove2 with (s:=S_Second).
  apply JO_red_forkmove2 with (s:=s0).
 assumption.
 apply star_trans with (y:=( x1 #  (x #  x2))).
 apply fork_tau_push_ee_12.
 induction x.
 apply fork_tau_ce_push_h.
 assumption.
 apply fork_tau_push_ee_2.
 assumption.
 apply star_refl.
 apply S_star with (y:=( ( x1) #  (x #> x2))).
 apply tStep with (s:=S_Second).
 apply JO_red_forkmove2 with (s:=S_Second).
 apply JO_red_forkdeath2.
 assumption.
 apply S_star with (y:=(  x1 <#  (x #> x2))).
 apply tStep with (s:=S_First).
 apply JO_red_forkdeath1.
 assumption.
 simpl; auto.
 simpl; auto.
  (* B5-L2-T3 *)
  destruct H3.
  destruct H3.
  destruct H3.
  destruct H4.
  destruct H6.
  substs.
  apply taured_val_id in H4.
  substs.
  branch 6.
  exists x ( x2) x1.
  intuition.
  apply lab_r with (e1:=( x1 #  (x #  e')))(e2:=( x1 #  (x #  e'')))(s:=S_Second).
 intuition.
 apply JO_red_forkmove2 with (s:=S_Second).
  apply JO_red_forkmove2 with (s:=s0).
 assumption.
 apply star_trans with (y:=( x1 #  (x #  x2))).
 apply fork_tau_push_ee_12.
 induction x.
 apply fork_tau_ce_push_h.
 assumption.
 apply fork_tau_push_ee_2.
 assumption.
 apply star_refl.
 apply S_star with (y:=( x1 <#  (x #  x2))).
 apply tStep with (s:=S_First).
 apply JO_red_forkdeath1.
 assumption.
 simpl; auto.
 simpl; auto.
 (* B5 - L3 *)
 substs.
 branch 8.
 apply taured_val_id in H3.
 substs.
 left.
 exists x x1 (E_constant CONST_unit).
 intuition.
 simpl; auto.
 apply lab_r with (e1:=( x1 #  (x # E_comp l)))(e2:=(( x1) #  ( x #> (E_constant CONST_unit))))(s:=S_Second).
 intuition.
 apply JO_red_forkmove2 with (s:=S_Second).
 apply JO_red_forkdocomp2.
 apply S_star with (y:=(x1 <#  (x #> E_constant CONST_unit))).
 apply tStep with (s:=S_First).
 apply JO_red_forkdeath1.
 simpl; auto.
 apply star_refl.
 simpl; auto.
 (* B5 - L4 *)
 substs.
 apply red_not_value in H9; simpl in H9; intuition.
 (* B4 - L5 *)
 apply red_not_value in H8; simpl in H8; intuition.
 (* B6 *)
 destruct H1.
 destruct H1.
 destruct H1.
 destruct H1.
 substs.
 apply red_not_value in H0; simpl in H0; intuition.
 (* B7 *)
 destruct H2.
 destruct H1.
 destruct H1.
 destruct H1.
 substs.
 apply red_not_value in H0; simpl in H0; intuition.
 (* B8 *)
 destruct H2.
 destruct H1.
 destruct H1.
 destruct H1.
 substs.
 apply red_not_value in H0; simpl in H0; intuition.
Qed.

Lemma fork_tau_behave_v1 : forall (v e' : expr) (e : livemodes), is_value_of_expr v -> tauRed (( v)# e) e' ->  
      (
      (exists (f : livemodes), e' = ( v) <# f /\ ((exists (g g' :expr ), e =  g /\ tauRed g g' /\ f =  g')  \/ (exists (l : label),e = E_comp l /\ f = e ) ))
      \/ 
      (exists (f : livemodes), e' = ( v)# f  /\ ((exists (g g' :expr ), e =  g /\ tauRed g g' /\ f =  g')  \/ (exists (l : label),e = E_comp l /\ f = e ) ))
      \/ 
      (exists (f : expr), e' = ( v) #> f   /\ ((exists (g :expr ), e =  g /\ tauRed g f /\ is_value_of_expr f)  ))
      ).
Proof.
 intros.
 induction e.
 apply fork_tau_behave_ec in H0.
 destruct H0.
 intuition.
 substs.
 apply taured_val_id in H1.
 substs.
 branch 2.
 exists (E_comp lab).
 intuition.
 right.
 exists lab.
 intuition.
 assumption.
 substs.
 left.
 apply taured_val_id in H1.
 substs.
 exists (E_comp lab).
 intuition.
 right.
 exists lab; intuition.
 assumption. 
 apply fork_tau_behave_ee in H0.
 intuition.
 destruct H1; destruct H0; intuition.
 substs.
 apply taured_val_id in H1; substs.
 branch 2.
 exists ( x0).
 intuition.
 left.
 exists expr5 x0.
 intuition.
 assumption.
 destruct H0; destruct H0; intuition; substs.
 apply taured_val_id in H0.
 substs.
 branch 3.
 exists x0.
 intuition.
 exists expr5; intuition.
 assumption.
 destruct H0; destruct H0; intuition; substs.
 apply taured_val_id in H0.
 substs.
 branch 1.
 exists ( x0).
 intuition.
 left.
 exists expr5 x0; intuition.
 assumption.
Qed.


Lemma fork_tau_behave_v2 : forall (v e' : expr) (e : livemodes), is_value_of_expr v -> tauRed (e # ( v)) e' ->  
      (
      (exists (f : livemodes), e' = f #> v /\ ((exists (g g' :expr ), e =  g /\ tauRed g g' /\ f =  g')  \/ (exists (l : label),e = E_comp l /\ f = e ) ))
      \/ 
      (exists (f : livemodes), e' = f # ( v)  /\ ((exists (g g' :expr ), e =  g /\ tauRed g g' /\ f =  g')  \/ (exists (l : label),e = E_comp l /\ f = e ) ))
      \/ 
      (exists (f : expr), e' = f <# ( v)   /\ ((exists (g :expr ), e =  g /\ tauRed g f /\ is_value_of_expr f)  ))
      ).
Proof.
 intros.
 induction e.
 apply fork_tau_behave_ce in H0.
 destruct H0.
 intuition.
 substs.
 apply taured_val_id in H1.
 substs.
 branch 2.
 exists (E_comp lab).
 intuition.
 right.
 exists lab.
 intuition.
 assumption.
 substs.
 left.
 apply taured_val_id in H1.
 substs.
 exists (E_comp lab).
 intuition.
 right.
 exists lab; intuition.
 assumption. 
 apply fork_tau_behave_ee in H0.
 intuition.
 destruct H1; destruct H0; intuition.
 substs.
 apply taured_val_id in H0; substs.
 branch 2.
 exists ( x).
 intuition.
 left.
 exists expr5 x.
 intuition.
 assumption.
 destruct H0; destruct H0; intuition; substs.
 apply taured_val_id in H2.
 substs.
 branch 1.
 exists ( x).
 intuition.
 left.
 exists expr5 x.
 intuition.
 assumption.
 destruct H0; destruct H0; intuition; substs.
 apply taured_val_id in H2.
 substs.
 branch 3.
 exists (x).
 intuition.
 exists expr5.
 intuition.
 assumption.
Qed.
 

Lemma fork_lab_behave_v1 : forall (v e' : expr) (e : livemodes) (l : label), is_value_of_expr v -> labRed l (( v)# e) e' ->  
      (
      (exists (f : livemodes), e' = ( v) <# f /\ ((exists (g g' :expr ), e =  g /\ labRed l g g' /\ f =  g')  \/ (exists (l : label),e = E_comp l /\ f = e ) ))
      \/ 
      (exists (f : livemodes), e' = ( v)# f  /\ ((exists (g g' :expr ), e =  g /\ labRed l g g' /\ f =  g')  ))
      \/ 
      (exists (f : expr), e' = ( v) #> f   /\ ((exists (g :expr ), e =  g /\ labRed l g f /\ is_value_of_expr f) \/ (e= E_comp l /\ f=(E_constant CONST_unit))  ))
      ).
Proof.
 intros.
 inversion H0.
 substs; intuition.
 apply fork_tau_behave_v1 in H2.
 intuition.
 destruct H3. 
 intuition.
 substs.
 apply red_not_value in H1; simpl in H1; intuition.
 substs.
 apply red_not_value in H1; simpl in H1; intuition.
 destruct H2.
 intuition.
 substs.
 inversion H1.
 substs.
 apply red_not_value in H9; simpl in H9; intuition.
 substs.
 apply fork_tau_behave_v1 in H4.
 intuition.
 branch 1.
 destruct H2.
 destruct H2.
 intuition.
 substs.
 simplify_eq H6; clear H6; intros; substs.
 destruct H3.
 intuition.
 substs.
 exists x1.
 intuition.
 left.
 destruct H3.
 destruct H3.
 intuition.
 substs.
 simplify_eq H4; clear H4; intros; substs.
 exists x x3.
 intuition.
 apply lab_r with (e1:=x0)(e2:=x2)(s:=s0).
 intuition.
 destruct H3.
 intuition.
 simplify_eq H5; clear H5; intros; substs.
 branch 2. 
 destruct H4; intuition; substs.
 destruct H2; destruct H2; destruct H3; destruct H3; intuition; substs.
 simplify_eq H2; simplify_eq H7; clear H2; clear H7; intros; substs.
 exists ( x3).
 intuition.
 exists x0 x3; intuition.
 apply lab_r with (e1:=x1)(e2:=x2)(s:=s0).
 intuition.
  destruct H2; destruct H2; destruct H3; intuition; substs.
 simplify_eq H2; simplify_eq H7; clear H2; clear H7; intros; substs.
 branch 3. 
 destruct H2. destruct H2; destruct H4; intuition; substs.
 destruct H6; intuition.
 simplify_eq H4; simplify_eq H7; clear H4; clear H7; intros; substs.
 exists x1.
 intuition.
 left.
 exists x.
 intuition.
 apply lab_r with (e1:=x0)(e2:=x2)(s:=s0).
 intuition.
 assumption.
 substs.
 branch 3.
 destruct H2; destruct H2; intuition; substs.
 apply taured_val_id in H4.
 substs.
 simplify_eq H6; clear H6; intros; substs.
 simpl; auto.
 substs.
 apply red_not_value in H10; simpl in H10; intuition.
 substs.
 apply red_not_value in H9; simpl in H9; intuition.
 substs.
 branch 3.
 destruct H2.
 intuition.
 substs.
 exists (E_constant CONST_unit).
 inversion H1.
 substs.
 apply red_not_value in H8; simpl in H8; intuition.
 substs.
 apply taured_val_id in H4; substs; intuition.
 simpl; auto.
 substs.
 apply red_not_value in H9; simpl in H9; intuition.
 substs.
 apply red_not_value in H8; simpl in H8; intuition.
 destruct H2.
 intuition; substs.
 apply red_not_value in H1; simpl in H1; intuition.
 assumption.
Qed.


Lemma fork_lab_behave_v2 : forall (v e' : expr) (e : livemodes)(l: label), is_value_of_expr v -> labRed l (e # ( v)) e' ->  
      (
      (exists (f : livemodes), e' =   f #> ( v) /\ ((exists (g g' :expr ), e =  g /\ labRed l g g' /\ f =  g')  \/ (exists (l : label),e = E_comp l /\ f = e ) ))
      \/ 
      (exists (f : livemodes), e' = f # ( v)  /\ ((exists (g g' :expr ), e =  g /\ labRed l g g' /\ f =  g')  ))
      \/ 
      (exists (f : expr), e' =  f <# ( v)  /\ ((exists (g :expr ), e =  g /\ labRed l g f /\ is_value_of_expr f) \/ (e= E_comp l /\ f=(E_constant CONST_unit))  ))
      ).
Proof.
 intros.
 induction e.
 apply fork_label_behave_ce in H0.
 intuition.
 substs.
 destruct H2.
 intuition.
 substs.
 apply taured_val_id in H1.
 substs.
 branch 3.
 exists (E_constant CONST_unit).
 intuition.
 assumption.
 destruct H0.
 intuition.
 apply labred_not_val in H1.
 simpl in H1; intuition.
 destruct H0.
 intuition.
 apply labred_not_val in H1.
 simpl in H1; intuition.
 apply fork_label_origin_ee in H0.
 intuition.
 destruct H1.
 intuition.
 destruct H0.
 intuition.
 substs.
 apply taured_val_id in H2.
 substs.
 branch 2.
 exists ( x).
 intuition.
 exists expr5 x.
 intuition.
 assumption.
 destruct H2.
 intuition.
 apply taured_val_id in H0.
 substs.
 branch 1.
 exists ( x).
 intuition.
 left.
 exists expr5 x.
 intuition.
 assumption.
 destruct H2.
 intuition.
 substs.
 branch 3.
 apply taured_val_id in H0; substs.
 exists x; intuition.
 left.
 exists expr5.
 intuition.
 assumption.
 destruct H1.
 intuition.
 apply labred_not_val in H1; simpl in H1; intuition.
 apply labred_not_val in H1; simpl in H1; intuition.
 apply labred_not_val in H1; simpl in H1; intuition.
Qed.
 


Inductive fork_assoc_rel :  relation expr := 
 | forka_start : forall (a b c : livemodes), fork_assoc_rel (( (a # b)) # c) (a # ( (b # c)))
 | forka__end_sr : forall (a' b' : livemodes)(c' : expr), is_value_of_expr c' -> fork_assoc_rel (( (a' # b')) #> c') (a' #> ( (b' #> c')))
 | forka__end_rl : forall (a' c' : livemodes)(b' : expr), is_value_of_expr b' -> fork_assoc_rel (( (a' #> b')) <# c') (a' #> ( (b' <# c')))
 | forka__end_rs : forall (a' c' : livemodes)(b' : expr), is_value_of_expr b' -> fork_assoc_rel (( (a' #> b')) # c') (a' # (  (( b') # c')))
 | forka__end_ls : forall (b' c' : livemodes)(a' : expr), is_value_of_expr a' -> fork_assoc_rel (( (a' <# b')) # c') (a' <# (  (b' # c')))
 | forka__end_ll : forall (b' c' : livemodes)(a' : expr), is_value_of_expr a' -> fork_assoc_rel (( (a' <# b')) <# c') (a' <# ( (b' # c')))
 | forka__end_rr : forall (a' : livemodes)(b' c' : expr), is_value_of_expr b' -> is_value_of_expr c' -> fork_assoc_rel (( (a' #> b')) #> c') (a' #> ( ( b' #> c')))
 | forka__end_lr : forall (b' : livemodes)(a' c' : expr), is_value_of_expr c' -> is_value_of_expr a' -> fork_assoc_rel (( (a' <# b')) #> c') (a' <# (  (b' #> c')))
 | forka_end_comp : forall (x : livemodes)(q' : expr), is_value_of_expr q' -> fork_assoc_rel (( (x #> (E_constant CONST_unit))) #> q') (x #> (E_constant CONST_unit <# ( q'))).

(*
Lemma fork_assoc_wbsm_h : ((forall (q p p' : expr) (r : redlabel), (weakred r p p') ->
                                                        ( (fork_assoc_rel p q) -> (exists (q' : expr), (weakred r q q') /\  (fork_assoc_rel p' q') )) ) 
/\                        (forall (p q q' : expr) (r : redlabel), weakred r q q' -> ( fork_assoc_rel p q -> (exists (p' : expr), weakred r p p' /\  fork_assoc_rel p' q' )))).
Proof.
 intros.
 split.
 intro q.
 assert ((forall x : expr, (fun r p p' => (( (fork_assoc_rel p q) -> (exists (q' : expr), (weakred r q q') /\  (fork_assoc_rel p' q') )))) RL_tau x x) ).
 intros.
 exists q.
 intuition.
 apply weakred_T.
 apply star_refl.
 intros.
 apply weakind with (r:=r)(e:=p)(e0:=p') in H .
 apply H.
 assumption.
 intros.
 admit.
 intros.
 assert (labRed l e0 e3).
 apply lab_r with (e1:=e1)(e2:=e2)(s:=s).
 intuition.
 assert (H5:=H4); clear H4.
 intuition.
 inversion H3.
 substs.
 apply fork_lab_assoc_total in H5.
 intuition.
 destruct H6 as [a'].
 destruct H5 as [b'].
 destruct H5 as [c'].
 intuition.
 substs.
 exists (a' #  (b' # c')).
 intuition.
 apply weakred_L.
 assumption.
 apply forka_start.
 destruct H5 as [a'].
 destruct H5 as [b'].
 destruct H5 as [c'].
 intuition. substs.
 exists (a' #> (b' #> c')).
 intuition.
 Hint Resolve weakred_L.
 auto.
 Hint Constructors fork_assoc_rel.
 auto.
 destruct H6 as [a'].
 destruct H5 as [b'].
 destruct H5 as [c'].
 intuition. substs.
 exists (a' #> (c' <# b')).
 intuition.
 destruct H5 as [a'].
 destruct H5 as [c'].
 destruct H5 as [b'].
 intuition. substs.
 exists (a' #  (( b') # c')).
 intuition.
 destruct H6 as [b'].
 destruct H5 as [c'].
 destruct H5 as [a'].
 intuition. substs.
 exists (a' <#  (b' # c')).
 intuition.
 destruct H5 as [b'].
 destruct H5 as [c'].
 destruct H5 as [a'].
 intuition. substs.
 exists (a' <#  (b' # c')).
 intuition.
 destruct H6 as [a'].
 destruct H5 as [b'].
 destruct H5 as [c'].
 intuition.
 substs.
 exists (a' #> ( b' #> c')).
 intuition.
 destruct H5 as [b'].
 destruct H5 as [a'].
 destruct H5 as [c'].
 intuition. substs.
 exists (a' <#  (b' #> c')).
 intuition.
 destruct H5 as [x].
 destruct H5 as [q'].
 intuition. substs.
 exists (x #> (E_constant CONST_unit <#  q')).
 intuition.
 substs.
 apply labred_not_val in H5.
 simpl in H5.
 intuition.
 substs.
 apply labred_not_val in H5.
 simpl in H5.
 intuition.
 substs.
 apply fork_lab_behave_v1 in H5.
 intuition.
 destruct H8.
 intuition.
 substs.
 destruct H5.
 destruct H5.
 intuition.
 substs.

(* MARK *)

 apply fork_tau_assoc_total in H4.
 admit.
 assumption.
 apply H4.
 
 apply weakind with (P:=(fun r p p' => (( (fork_assoc_rel p q) -> (exists (q' : expr), (weakred r q q') /\  (fork_assoc_rel p' q') ))))).
 intros.

 split.
 revert p.
 apply weakind.
 intros.



(*
 
Inductive fork_assoc_rel :  relation expr := 


 | forka_start : forall (a b c : livemodes), fork_assoc_rel (E_apply (E_apply (E_constant CONST_fork) ( (E_live_expr ( (E_apply (E_apply (E_constant CONST_fork) ( (E_live_expr a)) ) ( (E_live_expr b)))))) ) ( (E_live_expr c))) (E_apply (E_apply (E_constant CONST_fork) ( (E_live_expr a)) ) ( (E_live_expr ( (E_apply (E_apply (E_constant CONST_fork) ( (E_live_expr b)) ) ( (E_live_expr c)))))))
 | forka_tau : forall  (e e' : expr),  is_value_of_expr e /\ is_value_of_expr e' -> fork_assoc_rel e e'.

Theorem fork_assoc_wbsm : forall (p q : expr), fork_assoc_rel p q -> ((forall (l : label) (p' : expr), labRed l p p' -> (exists (q' : expr), labRed l q q' /\ fork_assoc_rel p' q') ) /\ (forall (l : label) (q' : expr), labRed l q q' -> (exists (p' : expr), labRed l p p' /\ fork_assoc_rel p' q') )).
Proof.
 intros.
 splits.
 intros.
 assert (L:=H0).
 inversion H.
 substs.
 apply fork_lab_behave in H0.
 intuition.
 destruct H1.
 destruct H0.
 substs.
 induction c.
 assert (H0:=L).
 apply fork_label_behave_ec in H0.
 intuition.
 destruct H2.
 intuition.
 discriminate H3.
 destruct H0.
 intuition.
 simplify_eq H2; clear H2; intros; substs.
 assert (K:=H1).
 induction b.
 induction a.
 apply fork_label_origin_cc in H1.
 intuition.
 substs.
 apply fork_label_behave in H1.
 intuition.
 destruct H0.
 destruct H0.
 substs.
 
 exists ( x #  ( x0 # E_comp lab)).
 splits.
 substs.
 intuition.
 substs.
 admit.
 assert (H0:=L).
 apply fork_label_origin_ee in H0.
 intuition.
 destruct H1.
 intuition.
 destruct H0.
 intuition.
 simplify_eq H3.
 intros.
 substs.
 clear H3.
 substs.

 admit.


 substs.
 destruct H2.
 intuition.
 discriminate H4.
 destruct H2.
 intuition.
 discriminate H4.
 destruct H1.
 intuition.
 destruct H0.
 intuition.
 simplify_eq H3; clear H3; intros; substs.
 apply fork_tau_behave_total in H2.
 intuition.
 destruct H0.
 destruct H0.
 substs.
 exists ((-<  (-< a b)  expr5)).
 substs.
 destruct H2.
 destruct H0.
 admit.
 
 

 
 substs.
 intuition. 
 apply labred_not_val in H0.
 intuition.
 

 intros.
 assert (L:=H0).
 inversion H.
 substs.
 
 apply fork_lab_behave in H0.
 intuition.
 destruct H1.
 destruct H0.
 substs.
 admit.
 intuition.
 destruct H0.
 substs.
 destruct H2.
 destruct H0.
 intuition.
 admit.

 admit.
 

 substs.
 intuition. 
 apply labred_not_val in H0.
 intuition.
Qed.

-< (-< a b) (c) = -< (a) (-< b c)
*)
*)
