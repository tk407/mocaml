Require Import Arith.
Require Import Bool.
Require Import Setoid.
Add LoadPath "WeakUpTo".
Require Import WeakUpTo.Relations.
Require Import WeakUpTo.Reductions.

Load mconbase2.


Inductive idExp : expr -> expr -> Prop :=
 | id_id: forall (e : expr ), idExp e e.

Inductive tauStep : relation expr :=
 | tStep :  forall (e e' : expr) (s : select), JO_red e s RL_tau e' -> tauStep e e'.

Definition tauRed : relation expr := (star tauStep).



Lemma tauRed_trans : forall (e e' e'' : expr), tauRed e e' -> tauRed e' e'' -> tauRed e e''.
Proof.
 unfold tauRed.
 apply star_trans.
Qed.

Inductive totalDetTauStep : relation expr :=
 | ttStep : forall (e e' : expr), ( (tauStep e e') /\ (forall (e'' : expr) (s : select) (l : label), JO_red e s (RL_labelled(l)) e'' -> False) /\ (forall (e''' : expr), tauStep e e''' -> e' = e''')) -> totalDetTauStep e e'.

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

Inductive weaksim : relation expr := 
 | weaksim_id : forall (e : expr), weaksim e e
 | weaksim_gen: forall (e e' : expr), 
                  (forall (l : label), 
                    (forall (e0 : expr), labRed l e e0 -> (exists (e1 : expr), labRed l e' e1 /\ weaksim e0 e1)))
                  -> weaksim e e'
 | weaksim_tr : forall (e e' e'' : expr), weaksim e e' /\ weaksim e' e'' -> weaksim e e''.


Lemma weaksim_refl : forall (e : expr), weaksim e e.
Proof.
 intros.
 apply weaksim_id.
Qed.
(*
Lemma induction_on_trans2 : forall ( e e' e1 e2 : expr). 
*)
Lemma weaksim_trans : forall (e e' e'' : expr), weaksim e e' /\ weaksim e' e'' -> weaksim e e''.
Proof.
 apply weaksim_tr.
Qed.

Inductive weakbisim : relation expr :=
 | weakbi : forall (e e' : expr), weaksim e e' /\ weaksim e' e -> weakbisim e e'.

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

Lemma bisimrefl : forall (e : expr), weakbisim e e.
Proof.
 intros.
 apply weakbi.
 split.
 apply weaksim_id.
 apply weaksim_id.
Qed.

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

