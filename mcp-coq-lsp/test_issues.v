Require Import Arith.

Lemma test_tree : forall (a b : nat), (a + b = b + a) /\ (a <= a + b).
Proof.
  intros a b.
  split.
  - apply Nat.add_comm.
  (* second bullet missing *)
Admitted.
