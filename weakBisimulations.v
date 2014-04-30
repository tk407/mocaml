Require Import Arith.
Require Import Bool.
Require Import Setoid.
Add LoadPath "WeakUpTo".
Require Import WeakUpTo.Relations.
Require Import WeakUpTo.Reductions.

Load mconbase2.

Load LibTactics.

Notation "A >>= F" := (E_bind A F) (at level 42, left associativity).
Notation "A [ C ] --> [ D ] B" := (JO_red A C D B) (at level 54, no associativity).
Notation " A # B " := (E_apply (E_apply (E_constant CONST_fork) ( (E_live_expr A)) ) ( (E_live_expr B))) (at level 20).
Notation " A <# B "  := (E_live_expr((E_taggingleft(E_pair A (E_live_expr B))))) (at level 20).
Notation " A #> B "  := (E_live_expr((E_taggingright(E_pair (E_live_expr A) B)))) (at level 20).
Notation " A <|# B "  := (((E_taggingleft(E_pair A (E_live_expr B))))) (at level 20).
Notation " A #|> B "  := (((E_taggingright(E_pair (E_live_expr B) A)))) (at level 20).

Inductive idExp : expr -> expr -> Prop :=
 | id_id: forall (e : expr ), idExp e e.

Inductive tauStep : relation expr :=
 | tStep :  forall (e e' : expr) (s : select), JO_red e s RL_tau e' -> tauStep e e'.
Hint Constructors tauStep.


Definition tauRed : relation expr := (star tauStep).



Lemma tauRed_trans : forall (e e' e'' : expr), tauRed e e' -> tauRed e' e'' -> tauRed e e''.
Proof.
 unfold tauRed.
 apply star_trans.
Qed.

Inductive totalDetTauStep : relation expr :=
 | ttStep : forall (e e' : expr), ( (tauStep e e') /\ (forall (e'' : expr) (s : select) (l : label), JO_red e s (RL_labelled(l)) e'' -> False) /\ (forall (e''' : expr), tauStep e e''' -> e' = e''')) -> totalDetTauStep e e'.
Hint Constructors totalDetTauStep.

Lemma dettaustep : forall (e e' e'' : expr), totalDetTauStep e e' /\ tauStep e e'' -> e' = e''.
Proof.
 intros.
 elim H.
 intros.
 inversion H0.
 elim H2; intros.
 elim H6.
 intros.
 apply H8.
 trivial.
Qed.



Definition totalTauRed : relation expr := (star totalDetTauStep).


Lemma totalTauRed_trans : forall (e e' e'' : expr), totalTauRed e e' -> totalTauRed e' e'' -> totalTauRed e e''.
Proof.
 unfold tauRed.
 apply star_trans.
Qed.

Lemma tau_step_incl_totalTau_step : Relations.incl totalDetTauStep tauStep.
Proof.
 unfold Relations.incl.
 intros.
 inversion H.
 elim H0.
 intros.
 trivial.
Qed.

Lemma tau_incl_totalTau : Relations.incl totalTauRed tauRed.
Proof. 
 apply star_incl.
 apply tau_step_incl_totalTau_step.
Qed.


Inductive labRed : label -> relation expr :=
 | lab_r : forall (e0 e1 e2 e3 : expr) (s : select) (l : label), tauRed e0 e1 /\ JO_red e1 s (RL_labelled(l)) e2 /\ tauRed e2 e3 -> labRed l e0 e3.
Hint Resolve labRed.

Inductive weakred : redlabel -> relation expr :=
 | weakred_T : forall ( e e' : expr ), tauRed e e' -> weakred RL_tau e e'
 | weakred_L : forall ( e e' : expr) (l : label), labRed l e e' -> weakred (RL_labelled l) e e'.

Inductive weaksim : relation expr := 
 | weaksim_id : forall (e : expr), weaksim e e
 | weaksim_gen: forall (e e' : expr), 
                  (forall (l : label), 
                    (forall (e0 : expr), labRed l e e0 -> (exists (e1 : expr), labRed l e' e1 /\ weaksim e0 e1)))
                  -> weaksim e e'
 | weaksim_tr : forall (e e' e'' : expr), weaksim e e' /\ weaksim e' e'' -> weaksim e e''.
Hint Resolve weaksim_id.
Hint Resolve weaksim_gen.

Lemma weaksim_refl : forall (e : expr), weaksim e e.
Proof.
 intros.
 apply weaksim_id.
Qed.
Hint Resolve weaksim_refl.
(*
Lemma induction_on_trans2 : forall ( e e' e1 e2 : expr). 
*)
Lemma weaksim_trans : forall (e e' e'' : expr), weaksim e e' /\ weaksim e' e'' -> weaksim e e''.
Proof.
 apply weaksim_tr.
Qed.

Inductive weakbisim : relation expr :=
 | weakbi : forall (e e' : expr), weaksim e e' /\ weaksim e' e -> weakbisim e e'.
Hint Resolve weakbi.

Inductive weakbisimalt : relation expr :=
 | weakbialt_id : forall (p : expr), weakbisimalt p p
 | weakbialt_gen : forall (p q : expr), (forall( l : label), (forall (q' : expr), labRed l q q' -> (exists (p' : expr), labRed l p p' /\ weakbisimalt p' q')) /\ (forall (p' : expr), labRed l p p' -> (exists (q' : expr), labRed l q q' /\ weakbisimalt p' q'))) -> weakbisimalt p q.
(*
Lemma weakbisim_eqv_alt : forall (e e' : expr), weakbisimalt e e' -> weaksim e e'.
Proof.
 apply weakbisimalt_ind.
 apply weaksim_id.
 intros.
 Check labRed_ind.
 apply weaksim_gen.
 intro l.
 elim H with (l:=l).
 Check labRed_ind.
 Check weaksim_ind.
 intros.
 induction H.
 apply weaksim_gen.
 Check labRed_ind.
 Check weaksim_ind.
 intros.
 inversion H.
 elim H1 with (l:=l).
 intros.
 intuition.
 Check labRed_ind.
 induction H.
 apply weakbialt in H.
 split.
 intros.
 generalize e e'.
 Check weakbisim_ind.
 apply weakbisim_ind in H.
 apply weakbialt.
 intros.
 split.
 induction
*)

Lemma bisimsymm : forall (e e' : expr), weakbisim e e' <-> weakbisim e' e.
Proof.
 intros.
 split.
 intros.
 apply weakbi.
 apply and_comm.
 inversion H.
 trivial.
 intros.
 apply weakbi.
 apply and_comm.
 inversion H.
 trivial.
Qed.
Hint Resolve bisimsymm.

Lemma bisimrefl : forall (e : expr), weakbisim e e.
Proof.
 intros.
 apply weakbi.
 split.
 apply weaksim_id.
 apply weaksim_id.
Qed.
Hint Resolve bisimrefl.

Lemma bisimtrans: forall (e e' e'': expr), weakbisim e e' /\ weakbisim e' e'' -> weakbisim e e''.
Proof.
 intros.
 elim H.
 intros.
 apply weakbi.
 split.
 inversion H0.
 inversion H1.
 elim H2.
 intros.
 elim H5.
 intros.
 apply weaksim_trans with (e':=e').
 auto.
 inversion H0.
 inversion H1.
 elim H2.
 elim H5.
 intros.
 apply weaksim_trans with (e':=e').
 auto.
Qed.


Lemma tau_weaksim_incl : forall (e e' : expr), tauRed e e' -> weaksim e' e.
Proof.
 intros.
 apply weaksim_gen.
 intros.
 exists e0.
 split.
 inversion H0.
 elim H1.
 intros. 
 apply lab_r with (e1:=e2)(e2:=e3)(s:=s).
 split.
 apply tauRed_trans with (e' := e').
 trivial.
 trivial.
 trivial.
 apply weaksim_id.
Qed.


Lemma ttau_prefix : forall (e e' e'' : expr), totalTauRed e e' /\ tauRed e e'' -> ((totalTauRed e e'' /\ totalTauRed e'' e') \/ (tauRed e' e'')).
Proof. 
 intros.
 elim H.
 intros.
 induction H1; intuition.
 left.
 split. 
 apply star_refl;
 trivial.
 trivial.
 inversion H3.
 right.
 rewrite <- H6; trivial.
 inversion H5.
 elim H9.
 intros.
 elim H13.
 intros.
 cut (y = y0).
 intros.
 cut (totalTauRed y z /\ totalTauRed z e' \/ tauRed e' z).
 intros.
 elim H17.
 intros.
 left.
 split.
 elim H18.
 intros.
 rewrite <- H16 in H5.
 apply S_star with (y:=y).
 trivial.
 trivial.
 elim H18.
 intros.
 trivial.
 intros.
 right.
 trivial.
 apply H.
 rewrite <- H16 in H6.
 trivial.
 trivial.
 rewrite <- H16 in H6.
 trivial.
 symmetry.
 apply H15.
 trivial.
Qed. 

Lemma ttau_midpoint : forall (e e' : expr), totalTauRed e e' -> ((fun x y => forall (z : expr), totalTauRed x z -> (totalTauRed z y \/ totalTauRed y z)) e e').
Proof.
 apply star_ind.
 intros.
 right.
 assumption.
 intros.
 inversion H2.
 subst.
 left.
 apply S_star with (y:=y).
 assumption.
 assumption.
 inversion H.
 intuition.
 inversion H3.
 intuition.
 apply H12 in H15.
 subst.
 apply H1 in H4.
 assumption.
Qed.

Lemma ttau_weakbisim_incl : forall (e e' : expr), totalTauRed e e' -> weakbisim e' e.
Proof.
 intros.
 apply weakbi.
 split.
 cut (tauRed e e').
 apply tau_weaksim_incl.
 apply tau_incl_totalTau.
 trivial.
 unfold totalTauRed in H.
 inversion H.
 apply weaksim_id.
 apply weaksim_gen.
 intros l e0.
 intros.
 exists e0.
 split.
 inversion H4.
 apply lab_r with (e1:=e2)(e2:=e3)(s:=s).
 split.
 cut (((totalTauRed e e2 /\ totalTauRed e2 e') \/ (tauRed e' e2))).
 intros.
 elim H9.
 intros.
 elim  H10.
 intros.
 inversion H12.
 apply star_refl.
 inversion H13.
 elim H17.
 intros.
 elim H21.
 intros.
 elim H22 with (e'':=e3)(s:=s)(l:=l).
 elim H5.
 intros.
 elim H25.
 intros.
 trivial.
 intros. 
 trivial.
 apply ttau_prefix.
 split.
 trivial.
 elim H5; intros.
 trivial.
 elim H5; intros; trivial.
 apply weaksim_id.
Qed.

(*
Inductive livemodes_ctx : Set := 
 | LM_ctx_expr (expr5:expr_ctx)
 | LM_ctx_BASE (lm : livemodes)
with expr_ctx : Set := 
 | E_ctx_H
 | E_ctx_apply (expr5:expr_ctx) (expr':expr_ctx)
 | E_ctx_bind (expr5:expr_ctx) (expr':expr_ctx)
 | E_ctx_function (value_name5:value_name) (typexpr5:typexpr) (expr5:expr_ctx)
 | E_ctx_fix (e:expr_ctx)
 | E_ctx_live_expr (lm:livemodes_ctx)
 | E_ctx_pair (e:expr_ctx) (e':expr_ctx)
 | E_ctx_taggingleft (e:expr_ctx)
 | E_ctx_taggingright (e:expr_ctx)
 | E_ctx_case (e1:expr_ctx) (x1:value_name) (e2:expr_ctx) (x2:value_name) (e3:expr_ctx)
 | E_ctx_BASE (e:expr).

(** context application *)
Fixpoint appctx_lm (lmc:livemodes_ctx) (e:expr) : livemodes :=
 match lmc with
 | LM_ctx_expr (expr5) => LM_expr (appctx_E expr5 e)
 | LM_ctx_BASE (lm) => lm
 end
with appctx_E (E5:expr_ctx) (e:expr) : expr :=
  match E5 with
  | E_ctx_H => e
  | E_ctx_apply (expr5) (expr') => E_apply (appctx_E expr5 e) (appctx_E expr' e)
  | E_ctx_bind (expr5) (expr') => E_bind (appctx_E expr5 e) (appctx_E expr' e) 
  | E_ctx_function (value_name5) (typexpr5) (expr5) => E_function (value_name5) (typexpr5) (appctx_E expr5 e)
  | E_ctx_fix (ex) => E_fix (appctx_E ex e)
  | E_ctx_live_expr (lm) => E_live_expr (appctx_lm lm e) 
  | E_ctx_pair (ex) (ex') => E_pair (appctx_E ex e) (appctx_E ex' e)
  | E_ctx_taggingleft (ex) => E_taggingleft (appctx_E ex e)
  | E_ctx_taggingright (ex) => E_taggingright (appctx_E ex e)
  | E_ctx_case (e1) (x1) (e2) (x2) (e3) => E_case (appctx_E e1 e) (x1) (appctx_E e2 e) (x2) (appctx_E e3 e)
  | E_ctx_BASE (ex) => ex end.
*)

Definition isExprRelationWeakBisimilarity (R : relation expr) : Prop :=
   forall (p q : expr), R p q -> ((forall (p' : expr) (l : label), labRed l p p' -> (exists (q' : expr), labRed l q q' /\  R p' q' )) /\(forall (q' : expr) (l : label), labRed l q q' -> (exists (p' : expr), labRed l p p' /\  R p' q' ))
               /\ (forall (p' : expr), tauRed p p' -> (exists (q' : expr), tauRed q q' /\  R p' q' )) /\(forall (q' : expr), tauRed q q' -> (exists (p' : expr), tauRed p p' /\  R p' q' ))
 ).

Definition isExprRelationValueEqualWeakBisimilarity (R : relation expr) : Prop :=
   isExprRelationWeakBisimilarity R /\ (forall (vp vq : expr), is_value_of_expr vp -> is_value_of_expr vq -> R vp vq -> vp=vq).

Inductive isExprWeaklyBisimilar : relation expr :=
  | isexprweaklybisimilar : (forall (e e' : expr), (exists (R : relation expr), isExprRelationWeakBisimilarity R /\ R e e') -> isExprWeaklyBisimilar e e').

Inductive isExprValueEqualWeaklyBisimilar : relation expr :=
  | isexprvalueequalweaklybisimilar : (forall (e e' : expr), (exists (R : relation expr), isExprRelationValueEqualWeakBisimilarity R /\ R e e') -> isExprValueEqualWeaklyBisimilar e e').
(*
Definition composeExprWithExprRelation (e : expr) (R : relation expr) : relation expr :=
*)
(*
Lemma E_apply_vewbsm : forall (f e f' e' : expr),  isExprValueEqualWeaklyBisimilar f f' -> isExprValueEqualWeaklyBisimilar e e' -> isExprValueEqualWeaklyBisimilar (E_apply f e) (E_apply f' e').
Proof.
Admitted.

Lemma E_bind_vewbsm : forall (f e f' e' : expr),  isExprValueEqualWeaklyBisimilar f f' -> isExprValueEqualWeaklyBisimilar e e' -> isExprValueEqualWeaklyBisimilar (E_bind f e) (E_bind f' e').
Proof.
Admitted.

(* FUNCTIONS ARE A PROBLEM: as they are values, they are only value equal weakly bisimilar with themselves. 
Contextual equivalence wants to be the property that f and f' are contextually equivalent if for any contextually equivalent e e' the application is contextually equivalent. 
This could be restricted to correctly typed expressions though.

This means that value equal weak bisimilarity is a subset of contextual equivalence. *)

(* this same effect happens for Live boxes. *)
*)
   
(*
Theorem ValueEqualWeakBisimilarityIsAContextualEquivalence : forall (e e' : expr) (c : expr_ctx), isExprValueEqualWeaklyBisimilar e e' -> isExprValueEqualWeaklyBisimilar (appctx_E c e) (appctx_E c e').
Proof.
 intros.
 inversion H.
 substs.
 destruct H0 as [R H0].
 destruct H0 as [H0 H1].
 induction c.
 simpl.
 assumption.
 simpl.
 unfold isExprRelationValueEqualWeakBisimilarity in H0.
 intuition.
 apply isexprvalueequalweaklybisimilar.
 induction c.
 exists R.
 intuition.
 
 inversion H.
 substs.
 unfold Hrwbsim.
*)

Check weakred_ind.
Check labRed_ind.
Check star_ind.
Check tauStep_ind.

Lemma weakind: forall P : redlabel -> expr -> expr -> Prop,
       (forall x : expr, P RL_tau x x) -> (
       ((forall (e e' : expr) (s : select), JO_red e s RL_tau e' -> (fun x y => (forall (z : expr), tauRed y z -> P RL_tau y z -> P RL_tau x z)) e e'))) ->
       ((forall (e0 e1 e2 e3 : expr) (s : select) (l : label),
        tauRed e0 e1 /\ JO_red e1 s (RL_labelled l) e2 /\ tauRed e2 e3 ->
        P (RL_labelled l) e0 e3)) ->
       forall (r : redlabel) (e e0 : expr), weakred r e e0 -> P r e e0.
Proof.
 intros.
 apply weakred_ind.
 apply star_ind.
 assumption.
 intros.
 inversion H3.
 substs.
 specialize H0 with (e:=x)(e':=y)(s:=s).
 apply H0 with (z:=z)  in H6.
 assumption.
 assumption.
 assumption.
 intros.
 apply labRed_ind with (P:=((fun x y z => (P (RL_labelled x) y z))) ).
 apply H1.
 assumption.
 assumption.
Qed.

Lemma weakbisim_weakred : forall (R : relation expr), isExprRelationWeakBisimilarity R <-> forall (p q : expr), R p q -> 
        ((forall (p' : expr) (r : redlabel), weakred r p p' -> (exists (q' : expr), weakred r q q' /\  R p' q' )) /\(forall (q' : expr) (r : redlabel), weakred r q q' -> (exists (p' : expr), weakred r p p' /\  R p' q' ))
 ).
 intros.
 split.
 intros.
 unfold isExprRelationWeakBisimilarity in H.
 intuition.
 induction r.
 inversion H1.
 substs.
 assert (exists q', tauRed q q' /\ R p' q').
 specialize H with (p:=p)(q:=q).
 apply H in H0.
 intuition.
 destruct H3.
 exists x.
 intuition.
 apply weakred_T.
 assumption.
 inversion H1.
 substs.
 assert (exists q', labRed lab q q' /\ R p' q').
 specialize H with (p:=p)(q:=q).
 apply H in H0.
 intuition.
 destruct H2.
 exists x.
 intuition.
 apply weakred_L.
 assumption.
 inversion H1.
 substs.
 assert (exists p', tauRed p p' /\ R p' q').
 specialize H with (p:=p)(q:=q).
 apply H in H0.
 intuition.
 destruct H3.
 exists x.
 intuition.
 apply weakred_T.
 assumption.
 substs.
 inversion H1.
 substs.
 assert (exists p', labRed l p p' /\ R p' q').
 specialize H with (p:=p)(q:=q).
 apply H in H0.
 intuition.
 destruct H3.
 exists x.
 intuition.
 apply weakred_L.
 assumption.
 intros.
 unfold isExprRelationWeakBisimilarity.
 intros.
 specialize H with (p:=p)(q:=q).
 apply H in H0.
 destruct H0.
 intuition.
 specialize H0 with (p':=p')(r:=RL_labelled l).
 assert (weakred (RL_labelled l) p p'). apply weakred_L; assumption.
 apply H0 in H3.
 destruct H3 as [q' H3].
 exists q'.
 destruct H3.
 inversion H3.
 substs.
 intuition.
 specialize H1 with (q':=q')(r:=RL_labelled l).
 assert (weakred (RL_labelled l) q q'). apply weakred_L; assumption.
 apply H1 in H3.
 destruct H3 as [p' H3].
 exists p'.
 destruct H3.
 inversion H3.
 substs.
 intuition.
 specialize H0 with (p':=p')(r:=RL_tau).
 assert (weakred (RL_tau) p p'). apply weakred_T; assumption.
 apply H0 in H3.
 destruct H3 as [q' H3].
 exists q'.
 destruct H3.
 inversion H3.
 substs.
 intuition.
 specialize H1 with (q':=q')(r:=RL_tau).
 assert (weakred (RL_tau) q q'). apply weakred_T; assumption.
 apply H1 in H3.
 destruct H3 as [p' H3].
 exists p'.
 destruct H3.
 inversion H3.
 substs.
 intuition.
Qed.

Lemma weakbisim_trans: forall (e e' e'' : expr ), isExprWeaklyBisimilar e e' /\ isExprWeaklyBisimilar e' e'' -> isExprWeaklyBisimilar e e''.
Proof. 
 intros.
 intuition.
 inversion H0.
 inversion H1.
 substs.
 destruct H.
 destruct H4.
 intuition. 
 apply isexprweaklybisimilar.
 exists (comp x x0).
 intuition.
 apply weakbisim_weakred.
 specialize weakbisim_weakred with (R:=x).
 intuition.
 specialize weakbisim_weakred with (R:=x0).
 intuition.
 unfold comp.
 inversion H7.
 apply H9 in H12.
 intuition.
 apply H2 in H11.
 intuition.
 apply H12 in H8.
 destruct H8.
 intuition.
 apply H13 in H11.
 destruct H11.
 intuition.
 exists x3.
 intuition.
 exists x2.
 intuition.
 assumption.
 inversion H7.
 specialize weakbisim_weakred with (R:=x0).
 intuition.
 apply H11 in H10.

 intuition.
 apply H2 in H9.
 intuition.
 apply H14 in H8.
 destruct H8.
 intuition.
 unfold comp.
 apply H15 in H9.
 destruct H9.
 intuition.
 exists x3.
 intuition.
 exists x2.
 assumption.
 assumption.
 unfold comp.
 exists e'.
 assumption.
 assumption.
Qed.

Lemma weakbisim_sym : forall (e e' : expr), isExprWeaklyBisimilar e e' -> isExprWeaklyBisimilar e' e.
Proof.
 intros.
 apply isexprweaklybisimilar.
 inversion H.
 substs.
 destruct H0.
 intuition.
 exists (trans x).
 split.
 apply weakbisim_weakred.
 specialize weakbisim_weakred with (R:=x).
 intros.
 unfold trans in H3.
 unfold trans.
 intuition.
 apply H0 in H3.
 intuition.
 apply H0 in H3.
 intuition.
 unfold trans.
 assumption.
Qed.
 

(*
Theorem weakredind : forall (X : Type) (R : relation X) (P : X -> X -> Prop),
       (forall x : X, P x x) ->
       (forall y x z : X, R x y -> star R y z -> P y z -> P x z) ->
       forall x x0 : X, star R x x0 -> P x x0



 Theorem Weak_ind:
       forall P: redlabel -> expr -> expr -> Prop,
       (forall x, P RL_tau x x) ->
       (forall y l x z s ,
        JO_red x s RL_tau y -> weakred l y z -> P l y z -> P l x z) ->
       (forall y a x z s,
        JO_red x s (RL_labelled a) y -> weakred RL_tau y z -> P RL_tau y z -> P (RL_labelled a) x z) ->
       forall l x x', weakred l x x' -> P l x x'.
    Proof.
      intros P Hrefl Htau Ha lab x x' Hxx'.
      induction lab.
      induction Hxx' as [ x | x1 x x' Hxx1 Hx1x' IH ]. induction H.
      apply Hrefl.
      inversion H.
      apply Htau with (y:=y)(s:=s).
      assumption.
      apply weakred_T.
      assumption.
      assumption.
      destruct Hxx1.
      Check star_ind.
      intuition.
      apply Ha with (y:=.
      as [ x1 Hxx1 Hx1x' ].
      destruct Hx1x' as [ x2 Hx1x2 Hx2x' ].
      induction Hxx1 as [ x | w x x1 Hxw Hwx1 IH ].
      apply Ha with x2; simpl; auto.
      clear Hx1x2.
      induction Hx2x' as [ x2 | u x2 x' Hux1 Hx1x' IH ]; [ apply Hrefl | apply Htau with u; assumption ].
      apply Htau with w; auto.
      exists x1; auto; exists x2; assumption.
    Qed.
*)