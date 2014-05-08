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
            (exists (f f': expr), tauRed e (E_live_expr (f)) /\ labRed l f f'  /\ (((y=(((E_live_expr ( f')))>>=e'))\/(is_value_of_expr f' /\ tauRed (E_apply e' f') y)))
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

 intuition.
 simplify_eq H5; clear H5; intros; substs.
 destruct H4.
 intuition.
 destruct H3.
 intuition.
 substs.
 inversion H0.
 substs.
 apply red_not_value in H9; simpl in H9; intuition.
 substs.
 apply bind_tau_behave_back_h in H6.
 destruct H6.
 destruct H3.
 intuition.
 simplify_eq H4; clear H4; intros; substs.
 destruct H3.
 intuition.
 substs.
 apply taured_val_id in H4; substs.
 right.
 right.
 exists x1 e'.
 intuition.
 apply lab_r with (e1:=x2)(e2:=e')(s:=s).
 intuition.
 apply star_refl.
 simpl; auto.
 destruct H3.
 intuition.
 destruct H6.
 intuition.
 substs.
 simplify_eq H4; clear H4; intros; substs.
 apply taured_val_id in H5. simplify_eq H5; clear H5; intros; substs.
  right.
 right.
 exists x1 x6.
 intuition.
 apply lab_r with (e1:=x2)(e2:=x5)(s:=s); intuition.
 simpl; auto.
 simplify_eq H4; clear H4; intros; substs.
 apply taured_val_id in H5. simplify_eq H5; clear H5; intros; substs.
  right.
 right.
 exists x1.
 exists x6.
 intuition.
 apply lab_r with (e1:=x2)(e2:=x5)(s:=s); intuition.
 simpl; auto.
 exists (E_live_expr e') x0; intuition.
 intuition.
  right.
 left.
 exists x1.
 intuition.
 exists x2. 
right.
 intuition.
 apply lab_r with (e1:=e1)(e2:=e2)(s:=s).
 intuition.
 exists e e'.
 reflexivity.
Qed.

Lemma app_ret_tau_behave : forall (e e' x : expr), tauRed (E_ret e)  x -> (
                     (exists (f : expr), tauRed e f /\ x=(E_ret f)) \/
                     (exists (v : expr), is_value_of_expr v /\ tauRed e v /\ x = (E_live_expr v))).
Proof.
 intros.
 Check star_ind.
 specialize star_ind with (R:=tauStep)(P:=fun x' y =>(
   (exists (e': expr), x'=(E_ret  e') /\ tauRed x' y) -> 
   (exists (e': expr), x'=(E_ret e') /\ 
     ((exists f, tauRed e' f /\ y = E_ret  f) \/
      (exists v, is_value_of_expr v /\ tauRed e' v /\ y = E_live_expr v))))
 ) (x:=(E_ret  e)) (x0:=x).
 intros.
 assert ((forall x : expr,
      (exists e', x = E_ret e' /\ tauRed x x) ->
      exists e',
      x = E_ret e' /\
      ((exists f, tauRed e' f /\ x = E_ret f) \/
       (exists v, is_value_of_expr v /\ tauRed e' v /\ x = E_live_expr v))) ).
 intros.
 destruct H1.
 intuition.
 substs.
 exists x1.
 intuition.
 left.
 exists x1.
 intuition.
 apply star_refl.
 apply H0 with (x:=(E_ret e)) (x0:=x) in H1.
 destruct H1.
 destruct H1.
 simplify_eq H1; clear H1; intros; substs.
 intuition.
 intros.
 destruct H5.
 destruct H5.
 substs.
 inversion H2.
 substs.
 inversion H5.
 substs.
 exists x1.
 intuition.
 right.
 exists x1.
 intuition.
 apply star_refl.
 apply taured_val_id in H3.
 intuition.
 simpl; auto.
 substs.
 exists x1.
 intuition.
 assert (exists e',
     E_ret e'0 = E_ret e' /\
     ((exists f, tauRed e' f /\ z = E_ret f) \/
      (exists v, is_value_of_expr v /\ tauRed e' v /\ z = E_live_expr v))).
 apply H4.
 exists e'0.
 intuition.
 destruct H0.
 intuition.
 simplify_eq H9; clear H9; intros; substs.
 left.
 destruct H0.
 exists x2.
 intuition.
 apply S_star with (y:=x0).
 apply tStep in H8; intuition.
 assumption.
 simplify_eq H9; clear H9; intros; substs.
 right.
 destruct H0.
 exists x2.
 intuition.
 apply S_star with (y:=x0).
 apply tStep in H8; intuition.
 assumption.
 assumption.
 exists e.
 intuition.
Qed.


Lemma app_ret_lab_behave : forall (e e' x : expr)(l : label), labRed l (E_ret  e)  x -> (
                     (exists (f : expr), labRed l e f /\ x=(E_ret f)) \/
                     (exists (v : expr), is_value_of_expr v /\ labRed l e v /\ x = (E_live_expr v))).
Proof.
 intros.
 inversion H.
 substs.
 intuition.
 apply app_ret_tau_behave in H1.
 intuition.
 destruct H2; intuition; substs.
 inversion H0.
 substs.
 apply app_ret_tau_behave in H3.
 intuition.
 left.
 destruct H1.
 exists x1.
 intuition.
 substs.
 apply lab_r with (e1:=x0)(e2:=e'0)(s:=s).
 intuition.
 right.
 destruct H1.
 exists x1.
 intuition.
 substs.
 apply lab_r with (e1:=x0)(e2:=e'0)(s:=s).
 intuition.
 apply E_unit.
 destruct H2.
 intuition; substs.
 inversion H0.
 apply (E_unit).
Qed.

Lemma app_tau_push_2 : forall (e : expr), is_value_of_expr e -> (forall (e' x : expr),  tauRed e' x -> tauRed (E_apply e e') (E_apply e x)).
Proof.
 intros e H.
 apply star_ind.
 intro x; apply star_refl.
 intros.
 apply S_star with (y:=(E_apply e y)).
 inversion H0.
 apply tStep with (s:=s).
 apply JO_red_context_app2.
 assumption.
 assumption.
 assumption.
Qed.

Lemma app_tau_push_1 : forall (e' : expr), (forall (e x : expr),  tauRed e x -> tauRed (E_apply e e') (E_apply x e')).
Proof.
 intros e'.
 apply star_ind.
 intro x; apply star_refl.
 intros.
 apply S_star with (y:=(E_apply y e')).
 inversion H.
 apply tStep with (s:=s).
 apply JO_red_context_app1.
 assumption.
 assumption.
Qed.

Lemma app_lab_push_2 : forall (e e' x : expr) (l : label), is_value_of_expr e -> labRed l e' x -> labRed l (E_apply e e') (E_apply e x).
Proof.
 intros.
 inversion H0.
 intuition.
 substs.
 apply lab_r with (e1:=(E_apply e e1))(e2:=(E_apply e e2))(s:=s).
 Hint Immediate app_tau_push_2.
 intuition.
 apply JO_red_context_app2; intuition.
Qed.

Lemma app_lab_push_1 : forall (e e' x : expr) (l : label), labRed l e x -> labRed l (E_apply e e') (E_apply x e').
Proof.
 intros.
 inversion H.
 intuition.
 substs.
 apply lab_r with (e1:=(E_apply e1 e'))(e2:=(E_apply e2 e'))(s:=s).
 Hint Immediate app_tau_push_1.
 intuition.
 apply JO_red_context_app1; intuition.
Qed.

 

Lemma JO_red_ret_td : forall (v:expr) (s:select),
     is_value_of_expr v -> totalDetTauStep (E_ret v) (E_live_expr ( v)).
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
  apply red_not_value in H2; contradiction.
  intros.
  inversion H0.
  inversion H1.
  reflexivity.
  apply red_not_value in H5; contradiction.
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
     totalDetTauStep (E_inpair v v')  (E_pair v v').
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
 substs.
 apply red_not_value in H7; contradiction.
 intros.
 substs.
 apply red_not_value in H8; contradiction.
 intros.
 inversion H1.
 substs.
 inversion H2.
 reflexivity.
 apply red_not_value in H8; contradiction.
 apply red_not_value in H9; contradiction.
Qed.


Lemma JO_red_proj1_td : forall (v v':expr),
     is_value_of_expr v ->
     is_value_of_expr v' ->
     totalDetTauStep (E_proj1 (E_pair v v'))  v.
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
 substs.
 inversion H3.
 apply red_not_value in H8; contradiction.
 apply red_not_value in H9; contradiction.
 intros.
 inversion H1.
 inversion H2.
 substs.
 reflexivity.
 substs.
 inversion H6.
 apply red_not_value in H9; contradiction.
 apply red_not_value in H10; contradiction.
Qed.


Lemma JO_red_proj2_td : forall (v v':expr),
     is_value_of_expr v ->
     is_value_of_expr v' ->
     totalDetTauStep (E_proj2 (E_pair v v'))  v'.
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
 substs.
 inversion H3.
 apply red_not_value in H8; contradiction.
 apply red_not_value in H9; contradiction.
 intros.
 inversion H1.
 inversion H2.
 substs.
 reflexivity.
 substs.
 inversion H6.
 apply red_not_value in H9; contradiction.
 apply red_not_value in H10; contradiction.
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
 assert (L:=H).
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
 inversion L.
 intuition.
 apply H1 in H6; intuition.
 inversion H.
 intuition.
 apply H6 in H4. 
 substs.
 clear H4.
 inversion H0.
 substs.
 inversion H2.
 substs.
 apply tdtstep_not_val in H; simpl in H; intuition. 
 substs.
 apply tdtstep_not_val in H; simpl in H; intuition. 
 substs.
 apply tdtstep_not_val in H; simpl in H; intuition. 
 substs.
 apply simpTau in H9.
 apply H6 in H9; substs.
 reflexivity.
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
Qed.

(*
Lemma weakbisim_ttd_bind_suffix: forall (R : relation expr), isExprRelationWeakBisimilarity R ->
                              (exists ( e : expr), (forall (vp vq : expr), is_value_of_expr vp -> is_value_of_expr vq -> R vp vq -> totalTauRed (vq>>=e)(e))) -> 
                                (exists (e : expr), forall (p q : expr), R p q -> isExprValueEqualWeaklyBisimilar p (q>>=e)).
Proof.
 intros. 
 destruct H0.
 exists x.
 intros.
 apply isexprvalueequalweaklybisimilar.
 exists (
   fun a b => (
     (exists (p q : expr), a = p /\
        ((R p q /\ (b = q >>= x))\/(is_value_of_expr p /\ is_value_of_expr q /\ totalTauRed (q>>=x) b)))
     )
   ).
 intuition.
 unfold isExprRelationValueEqualWeakBisimilarity.
 unfold isExprRelationWeakBisimilarity.
 unfold isExprRelationWeakBisimilarity in H.
 intuition.
 destruct H2.
 destruct H2.
 intuition.
 substs.
 apply H in H5.
 intuition.
 apply H2 in H3.
 destruct H3.
 intuition.
 exists (x2>>=x).
 intuition.
 Hint Resolve bind_lab_behave_front.
 auto.
 exists p'.
 exists x2.
 intuition.
 substs.
 apply H in H1.
 intuition.
 apply labred_not_val in H3.
 intuition.
 destruct H2.
 destruct H2.
 intuition; substs.
 apply H in H5.
 intuition.
 apply bind_lab_behave_back_h in H3.
 intuition.
 destruct H6.
 intuition.
 apply H5 in H6.
 destruct H6.
 intuition.
 apply bind_tau_behave_back_h in H8.
 destruct H8.
 destruct H3.
 intuition.
 simplify_eq H8; clear H8; intros; substs.
 destruct H3.
 intuition; substs.
 exists x3.
 intuition.
 exists x3 x; intuition.
 left; intuition.
 apply H in H9.
 intuition.
 apply H12 in H8.
 
 
 ).
*)