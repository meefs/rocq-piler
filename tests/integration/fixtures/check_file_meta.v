(** Fixture for check_file output filtering tests *)

Definition myNat := nat.

Inductive myBool : Type :=
  | myTrue | myFalse.

Fixpoint myAdd (n m : nat) : nat :=
  match n with
  | 0 => m
  | S n' => S (myAdd n' m)
  end.

Lemma skipDefs : True.
Proof. exact I. Qed.

Theorem alsoSkip : myBool -> True.
Proof. intro; exact I. Qed.

Lemma admitOne : True.
Proof. Admitted.

Lemma admitTwo : True.
Proof. Admitted.
