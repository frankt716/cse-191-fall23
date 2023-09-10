Local Open Scope nat_scope.

Inductive prop : Type :=
| var : nat -> prop
| T : prop
| F : prop
| conj : prop -> prop -> prop
| disj : prop -> prop -> prop
| imp : prop -> prop -> prop
| neg : prop -> prop.
Notation "'¬' P" := (neg P) (at level 19).
Infix "∧" := conj (at level 20, left associativity).
Infix "∨" := disj (at level 21, left associativity).
Infix "→" := imp (at level 22, right associativity).
Notation "P ≡ Q" := (P → Q ∧ Q → P) (at level 23).

Definition tva : Type := nat -> bool.

Fixpoint interp (P : prop) (M : tva) : bool :=
  match P with
  | var x => M x
  | T => true
  | F => false
  | conj P Q => andb (interp P M) (interp Q M)
  | disj P Q => orb (interp P M) (interp Q M)
  | imp P Q => implb (interp P M) (interp Q M)
  | neg P => negb (interp P M)
  end.

Inductive taut : prop -> Type :=
| tautK (P : prop) : (forall {M : tva}, interp P M = true) -> taut P.

Lemma identity_law1 : forall {P : prop}, taut (P ∧ T ≡ P).
Proof.
  intros P.
  constructor.
  intros M.
  simpl.
  destruct (interp P M).
  - reflexivity.
  - reflexivity.
Qed.

Lemma imp_id : forall {P : prop}, taut (P → P).
Proof.
  intros P.
  constructor.
  intros M.
  simpl.
  destruct (interp P M).
  - reflexivity.
  - reflexivity.
Qed.

Lemma lem : forall {P : prop}, taut (P ∨ ¬ P).
Proof.
  intros P.
  constructor.
  intros M.
  simpl.
  destruct (interp P M).
  - reflexivity.
  - reflexivity.
Qed.

