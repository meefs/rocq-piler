From Stdlib Require Import Arith.

(** Fixture for term-refinement (hole-addressed) workflow tests. *)

(* Basic skeleton: two independent named holes *)
Lemma ref_conj : True /\ (1 = 1).
Proof.
Admitted.

(* Dependent holes: witness appears in the proof hole's type *)
Lemma ref_exists : exists n : nat, n = 2.
Proof.
Admitted.

(* Tactic fill that creates unnamed goals (auto-rename path) *)
Lemma ref_tactic_fill : (True /\ True) /\ (2 = 2).
Proof.
Admitted.

(* Full workflow target: induction skeleton + tactic leaves *)
Lemma ref_plus_comm : forall n m : nat, n + m = m + n.
Proof.
Admitted.

(* Already closed — refinement tools must refuse *)
Lemma ref_closed : True.
Proof.
  exact I.
Qed.
