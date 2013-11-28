Inductive concurrent (A : Type, B: Type) :=
 | Live : A -> concurrent A
 | Dead : concurrent A
 | Fork : A*B -> concurrent (A*B).

Implicit Arguments Live [A].
Implicit Arguments Dead [A].
Implicit Arguments Fork [A].

Definition ret {A : Type} (x : A) := Some x.

Definition bind {A B : Type} (a : option A) (f : A -> option B) : option B :=
 match a with 
  | Some x => f x
  | None => None
 end.

Notation "A >>= F" := (bind A F) (at level 42, left associativity).

Lemma mon_left_id : forall (A B: Type) (a : A) (f : A -> option B),
  ret a >>= f = f a.
intros.
reflexivity.
Qed.
