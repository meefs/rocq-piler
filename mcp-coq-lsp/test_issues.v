Require Import Arith.

Lemma test_llm : forall (a b : nat), (a + b = b + a) /\ (a <= a + b).
Proof.
intros a b.
split.
- apply Nat.add_comm.
- apply Nat.le_add_r.
Qed.

