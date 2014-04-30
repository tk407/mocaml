Load progress.

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

Lemma bind_tau_behave_front_boxed : forall ( e e' x : expr), tauRed e x -> tauRed ((E_live_expr ( e)) >>= e') ((E_live_expr ( x)) >>= e').
Proof.
 intros.
 apply star_ind with (R:=tauStep)(X:=expr)(P:= (fun y z => tauRed ((E_live_expr ( y)) >>= e') ((E_live_expr ( z)) >>= e'))).
 intros.
 apply star_refl.
 intros.
 apply S_star with (y:=((E_live_expr (y))>>=e')).
 inversion H0.
 apply tStep with (s:= s).
 apply JO_red_movebind.
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

Lemma JO_red_ret_td : forall (v:expr) (s:select),
     is_value_of_expr v -> totalDetTauStep (E_apply (E_constant CONST_ret) v) (E_live_expr ( v)).
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
  apply red_not_value in H7.
  contradiction.
  apply red_not_value in H6;  simpl in H6;  intuition.
  intros.
  inversion H0.
  inversion H1.
  reflexivity.
  apply red_not_value in H10; contradiction.
  apply red_not_value in H9; simpl in H9; intuition.
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
 intros.
 inversion H1.
 substs.
 
 inversion H2.
 substs.
 inversion H.
 intuition.
 apply tStep in H8.
 apply H9 in H8; substs; intuition.
 substs.
 inversion H2.
 substs.
 inversion H.
 apply tStep in H7.
 intuition.
 substs.
 apply H10 in H7; substs.
 reflexivity.
 substs.
 inversion H.
 substs.
 intuition.
 inversion H4.
 substs.
 apply red_not_value in H5; simpl in H5; intuition.
 substs.
 apply tts_not_val in H.
 simpl in H; intuition.
Qed.


Lemma JO_red_dobind_td : forall (v e:expr) (s:select),
     is_value_of_expr v ->
     totalDetTauStep (E_bind  (E_live_expr ( v))  e) (E_apply e v).
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
 apply red_not_value in H7; contradiction.
 apply red_not_value in H6; simpl in H6; intuition.
 intros.
 inversion H0.
 inversion H1.
 reflexivity.
 apply red_not_value in H10; contradiction.
 apply red_not_value in H9; simpl in H9; intuition.
Qed.


Lemma tau_app1 : forall (e e' e'' : expr),
       tauStep (e) (e'') ->
       tauStep (E_apply e e') (E_apply e'' e').
Proof.
 intros.
 inversion H.
 apply tStep with (s:=s).
 apply JO_red_context_app1.
 trivial.
Qed.

Lemma tau_app2 : forall (e e' e'' : expr),
       is_value_of_expr e ->
       tauStep (e') (e'') ->
       tauStep (E_apply e e') (E_apply e e'').
Proof.
 intros.
 inversion H0.
 apply tStep with (s:=s).
 apply JO_red_context_app2.
 trivial.
 trivial.
Qed.

Lemma taustep_not_val : forall (e e' : expr), tauStep e e' -> (~ (is_value_of_expr e)).
Proof.
 intros.
 inversion H.
 apply red_not_value in H0.
 assumption.
Qed.


Hint Resolve taustep_not_val.


Lemma simpTau : forall(e e' : expr) (s: select),  
      e [s] --> [RL_tau] e' -> tauStep e e'.
Proof.
 intros.
 apply tStep with (s:=s).
 trivial.
Qed.

Hint Resolve simpTau.

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
 apply red_not_value in H8; contradiction.
 apply red_not_value in H7; contradiction.
 intros.
 inversion H1.
 inversion H2.
 apply red_not_value in H11; contradiction.
 apply red_not_value in H10; contradiction.
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
 inversion H8.
  apply red_not_value in H15; contradiction.
 apply red_not_value in H16; contradiction.
 inversion H7.
 intros.
 inversion H1.
 inversion H2.
 inversion H11.
 apply red_not_value in H17; contradiction.
 apply red_not_value in H18; contradiction.
 inversion H10.
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
 inversion H8.
 apply red_not_value in H14; contradiction.
 apply red_not_value in H15; contradiction.
 inversion H7.
 intros.
 inversion H1.
 inversion H2.
 inversion H11.
 apply red_not_value in H17; contradiction.
 apply red_not_value in H18; contradiction.
 inversion H10.
 reflexivity.
Qed.

Lemma tdtstep_not_val : forall (e e' : expr), totalDetTauStep e e' -> (~ (is_value_of_expr e)).
Proof.
 intros e e' H; inversion H; intuition.
 apply taustep_not_val in H4; contradiction.
Qed.

Lemma  JO_red_context_app1_td : forall (e e':expr) (e'':expr),
     totalDetTauStep e e'' ->
     totalDetTauStep (E_apply e e') (E_apply e'' e').
Proof.
intros.
 apply ttStep.
 intuition.
 inversion H.
 intuition.
 substs.
 inversion H3.
 substs.
 apply tStep with (s:=s).
 apply JO_red_context_app1.
 assumption.
 inversion H0.
 substs.
 apply tts_not_val in H; simpl in H; intuition.
 substs.
 apply tts_not_val in H; simpl in H; intuition.
 substs.
 apply tts_not_val in H; simpl in H; intuition.
 substs.
 inversion H.
 intuition.
 apply H1 in H6; assumption.
 inversion H0.
 substs.
 inversion H1.
 substs.
 apply tdtstep_not_val in H; simpl in H; intuition. 
 substs.
 apply tdtstep_not_val in H; simpl in H; intuition. 
 substs.
 apply tdtstep_not_val in H; simpl in H; intuition. 
 substs.
 apply tdtstep_not_val in H; simpl in H; intuition.
 substs.
 apply tdtstep_not_val in H; simpl in H; intuition. 
 substs.
 apply tdtstep_not_val in H; simpl in H; intuition. 
 substs.
 apply tdtstep_not_val in H; simpl in H; intuition. 
 substs.
 inversion H; intuition.
 apply tStep in H7; apply H8 in H7; substs; reflexivity.
 substs.
 apply tdtstep_not_val in H; simpl in H; intuition. 
 substs.
 apply tdtstep_not_val in H; simpl in H; intuition. 
 substs.
 apply tdtstep_not_val in H; simpl in H; intuition.  
Qed.



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
     (is_value_of_expr e) ->
     ~ (is_value_of_expr e') ->
     totalDetTauStep e' e'' ->
     totalDetTauStep (E_apply e e') (E_apply e e'').
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
 substs.
 simpl in H0; auto.
 substs.
 simpl in H0; auto.
 substs.
 simpl in H0; auto.
 substs.
 simpl in H0; auto.
 substs.
 inversion H1.
 intuition.
 apply H3 in H9; auto.
 substs.
 apply red_not_value in H8; intuition.
 inversion H1.
 intuition.
 substs.
 inversion H6.
 substs.
 inversion H3.
 substs.
 intuition.
 substs.
 simpl in  H0; intuition.
 substs.
 simpl in  H0; intuition. substs; simpl in  H0; intuition.
 substs; simpl in  H0; intuition.
 substs; simpl in  H0; intuition.
 substs; simpl in  H0; intuition.
 apply tStep in H13.
 apply H7 in H13; substs.
 reflexivity.
 substs.
 apply red_not_value in H12; contradiction.
 contradiction.
 substs.
 assert (is_value_of_expr (E_pair e''' v')); simpl; intuition.
 substs.
 assert (is_value_of_expr (E_pair v e''')); simpl; intuition.
Qed.
