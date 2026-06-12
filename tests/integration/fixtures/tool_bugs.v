From Stdlib Require Import Arith.

(** Fixture for reproducing TODO.md tool bugs. *)

(* Bug #2, #3, #7: Two proofs with similar structure for reset_proof targeting *)
Lemma bug_reset_target_a : True.
Proof.
Admitted.

Lemma bug_reset_target_b : True.
Proof.
Admitted.

(* Bug #9: Multi-line lemma statement *)
Lemma bug_multiline_stmt
  : True /\ True.
Proof.
  split.
  - exact I.
  - exact I.
Qed.

(* Bug #8: Lemma that add_lemma + reset_proof can corrupt *)
Lemma bug_add_reset_existing : True.
Proof.
  exact I.
Qed.

(* Bug #1: Compound tactic (induction) for goals query *)
Lemma bug_compound_induction : forall n : nat, n + 0 = n.
Proof.
Admitted.

(* Bug #3: Another proof so reset on «wrong» is detectable *)
Lemma bug_preserve_a : True.
Proof.
  exact I.
Qed.
Lemma bug_preserve_b : True.
Proof.
Admitted.
