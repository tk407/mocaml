Require Import Arith.
Require Import Bool.
Require Import List.

Load redTotalDetProp.


Lemma mon_left_id : forall (x:value_name) (t : typexpr) (a e:expr) (s s' : select),
    is_value_of_expr a ->
    ((E_apply(E_constant (CONST_ret)) a) >>= (E_function x t e)) -->* (E_apply (E_function x t e) a).
Proof.
 intros.
 apply JO_red_star_step with (e' := (E_live_expr (LM_expr a) >>= E_function x t e))(s:=s)(rl:=RL_tau).
 apply JO_red_evalbind.
 apply JO_red_ret.
 apply H.
 apply JO_red_star_step with (e' := (E_apply (E_function x t e) a))(s:=s')(rl:=RL_tau).
 apply JO_red_dobind.
 apply H.
 apply JO_red_star_refl.
Qed.

Lemma mon_left_id_wbsm : forall (x:value_name) (t : typexpr) (a e:expr),
    is_value_of_expr a ->
    weakbisim ((E_apply(E_constant (CONST_ret)) a) >>= (E_function x t e)) (E_apply (E_function x t e) a).
Proof.
 intros.
 cut (totalTauRed ((E_apply(E_constant (CONST_ret)) a) >>= (E_function x t e)) (E_apply (E_function x t e) a)).
 intros.
 apply bisimsymm.
 apply ttau_weakbisim_incl.
 trivial.
 intros.
 apply S_star with (y:=((E_live_expr (LM_expr a) >>= E_function x t e))).
 apply JO_red_evalbind_td.
 apply JO_red_ret_td.
 apply S_First.
 trivial.
 intros.
 apply JO_red_evalbind.
 apply JO_red_ret.
 trivial.
 apply S_star with (y:=(E_apply (E_function x t e) a)).
 apply JO_red_dobind_td.
 apply S_First.
 trivial.
 apply star_refl.
Qed.


Lemma mon_right_id : forall (a:expr) (s s' : select),
   is_value_of_expr a ->
   E_live_expr (LM_expr a) >>= E_constant CONST_ret -->* E_live_expr (LM_expr a).
Proof.
 intros.
 apply JO_red_star_step with (e' := (E_apply (E_constant CONST_ret) a))(s:= s)(rl:=RL_tau).
 apply JO_red_dobind.
 trivial.
 apply JO_red_star_step with (e' := (E_live_expr (LM_expr a)))(s:=s')(rl:=RL_tau).
 apply JO_red_ret.
 trivial.
 apply JO_red_star_refl.
Qed.

Lemma mon_right_id_wbsm : forall (a:expr) (s s' : select),
   is_value_of_expr a ->
   weakbisim (E_live_expr (LM_expr a) >>= E_constant CONST_ret) (E_live_expr (LM_expr a)).
Proof.
  intros.
  cut (totalTauRed (E_live_expr (LM_expr a) >>= E_constant CONST_ret) (E_live_expr (LM_expr a))).
  intros.
  apply bisimsymm.
  apply ttau_weakbisim_incl.
  trivial.
  apply S_star with (y:=(E_apply (E_constant CONST_ret) a)).
  apply JO_red_dobind_td.
  trivial.
  trivial.
  apply S_star with (y:=(E_live_expr (LM_expr a))).
  apply JO_red_ret_td.
  trivial. trivial.
  apply star_refl.
Qed.

Lemma mon_assoc : forall (v v' v'' : value_name) (t t' : typexpr) (a e e' :expr)(s s' s'':select),  
    is_value_of_expr a ->
    v <> v'' ->
    v' <> v'' ->
    ((subst_expr a v'' e') = e') ->
    ((subst_expr a v'' e) = e) ->
    exists (b :expr), (E_live_expr (LM_expr a) >>= (E_function v t e) >>= (E_function v' t' e') -->* b) /\ (E_live_expr (LM_expr a) >>= (E_function v'' t (E_apply (E_function v t e) (E_ident v'') >>= (E_function v' t' e'))) -->* b).
Proof.
 intros.
 exists (E_apply (E_function v t e) a >>= E_function v' t' e' ).
 split.
 Show 1.
  apply JO_red_star_step with (e' := ((E_apply (E_function v t e) a) >>= E_function v' t' e'))(s:=s)(rl:=RL_tau).
  apply JO_red_evalbind with (e' := ((E_apply (E_function v t e) a))).
  apply JO_red_dobind.
  trivial.
  apply JO_red_star_refl.
 apply JO_red_star_step with (e' := (E_apply (E_function v'' t (E_apply (E_function v t e) (E_ident v'') >>= E_function v' t' e')) a))(s:=s')(rl:=RL_tau).
 apply JO_red_dobind.
 trivial.
 apply JO_red_star_step with  (e' := (subst_expr a v'' (E_apply (E_function v t e) (E_ident v'') >>= E_function v' t' e')))(s:=s'')(rl:=RL_tau).
 apply JO_red_app with (x:=v'') (v:=a) (e := (E_apply (E_function v t e) (E_ident v'') >>= E_function v' t' e')).
 trivial.
 auto.
 cut ((subst_expr a v''  (E_apply (E_function v t e) (E_ident v'') >>= E_function v' t' e') = (E_apply (E_function v t e) a >>= E_function v' t' e'))). 
 intros.
 rewrite H4.
 apply JO_red_star_refl.
 simpl.
 rewrite H2.
 rewrite H3.
 cut ((if eq_value_name v v'' then true else false) = false).
 intros.
 rewrite H4.
 cut ((if eq_value_name v'' v'' then a else E_ident v'') = a).
 intros.
 rewrite H5.
 cut ((if eq_value_name v' v'' then true else false) = false).
 intros.
 rewrite H6.
 trivial.
 Check eq_value_name v v''.
 destruct (eq_value_name v v'').
 contradiction.
 destruct (eq_value_name v' v'').
 contradiction.
 trivial.
 destruct (eq_value_name v'' v'').
 trivial.
 contradiction n.
 trivial.
 destruct (eq_value_name v v'').
 contradiction e0.
 trivial.
Qed.



Lemma mon_assoc_wbsm : forall (v v' v'' : value_name) (t t' : typexpr) (a e e' :expr)(s s' s'':select),  
    is_value_of_expr a ->
    v <> v'' ->
    v' <> v'' ->
    ((subst_expr a v'' e') = e') ->
    ((subst_expr a v'' e) = e) ->
    weakbisim (E_live_expr (LM_expr a) >>= (E_function v t e) >>= (E_function v' t' e')) (E_live_expr (LM_expr a) >>= (E_function v'' t (E_apply (E_function v t e) (E_ident v'') >>= (E_function v' t' e')))).
Proof.
 intros.
 cut (exists (b :expr), (weakbisim (E_live_expr (LM_expr a) >>= (E_function v t e) >>= (E_function v' t' e')) b) /\ (weakbisim (E_live_expr (LM_expr a) >>= (E_function v'' t (E_apply (E_function v t e) (E_ident v'') >>= (E_function v' t' e')))) b)).
 intros.
 elim H4.
 intros.
 elim H5; intros.
 apply bisimsymm in H7.
 apply bisimtrans with (e':=x).
 auto.
 intros.
 exists (E_apply (E_function v t e) a >>= E_function v' t' e' ).
 split.
 Show 1.
  cut (totalTauRed (E_live_expr (LM_expr a) >>= E_function v t e >>= E_function v' t' e') (E_apply (E_function v t e) a >>= E_function v' t' e')).
  intros.
  apply bisimsymm.
  apply ttau_weakbisim_incl.
  trivial.
  apply S_star with (y := ((E_apply (E_function v t e) a) >>= E_function v' t' e')).
  apply JO_red_evalbind_td.
  apply JO_red_dobind_td.
  trivial.
  trivial.
  intros.
  apply JO_red_evalbind.
  apply JO_red_dobind.
  trivial.
  apply star_refl.
 Show 1.
 cut (totalTauRed (E_live_expr (LM_expr a) >>=   E_function v'' t (E_apply (E_function v t e) (E_ident v'') >>= E_function v' t' e')) (E_apply (E_function v t e) a >>= E_function v' t' e')).
 intros.
 apply bisimsymm.
 apply ttau_weakbisim_incl.
 trivial.
 apply S_star with (y := (E_apply (E_function v'' t (E_apply (E_function v t e) (E_ident v'') >>= E_function v' t' e')) a)).
 apply JO_red_dobind_td.
 trivial.
 trivial.
 apply S_star with  (y := (subst_expr a v'' (E_apply (E_function v t e) (E_ident v'') >>= E_function v' t' e'))).
 apply JO_red_app_td.
 trivial.
 cut ((subst_expr a v''  (E_apply (E_function v t e) (E_ident v'') >>= E_function v' t' e') = (E_apply (E_function v t e) a >>= E_function v' t' e'))). 
 intros.
 rewrite H4.
 apply star_refl.
 simpl.
 rewrite H2.
 rewrite H3.
 cut ((if eq_value_name v v'' then true else false) = false).
 intros.
 rewrite H4.
 cut ((if eq_value_name v'' v'' then a else E_ident v'') = a).
 intros.
 rewrite H5.
 cut ((if eq_value_name v' v'' then true else false) = false).
 intros.
 rewrite H6.
 trivial.
 Check eq_value_name v v''.
 destruct (eq_value_name v v'').
 contradiction.
 destruct (eq_value_name v' v'').
 contradiction.
 trivial.
 destruct (eq_value_name v'' v'').
 trivial.
 contradiction n.
 trivial.
 destruct (eq_value_name v v'').
 contradiction e0.
 trivial.
Qed.

