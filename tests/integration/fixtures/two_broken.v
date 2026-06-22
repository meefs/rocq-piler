From Stdlib Require Import Arith List Lia.
Import ListNotations.

Lemma add_comm : forall n m, n + m = m + n.
Proof.
  intros n m. induction n.
  - simpl. apply plus_n_O_wrong.
  - simpl. rewrite IHn. lia.
Qed.

Lemma rev_length : forall (A : Type) (l : list A), length (rev l) = length l.
Proof.
  intros A l. induction l as [| x xs IH].
  - reflexivity.
  - simpl. rewrite app_length. simpl. omega_tactic.
Qed.
