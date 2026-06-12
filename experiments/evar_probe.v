From Stdlib Require Import Arith.

(* Q1 probe: dependent hole — witness of ex_intro appears in the type of the
   proof hole, so plain refine shelves it *)
Lemma q1_dependent : exists n : nat, n = 2.
Proof.
Admitted.

(* Q2 probe: named evars *)
Lemma q2_named : True /\ (1 = 1).
Proof.
Admitted.

(* Q3 probe: goal selectors written to a file *)
Lemma q3_selectors : True /\ (2 = 2).
Proof.
  refine (conj ?[left_part] ?[right_part]).
  [left_part]: { exact I. }
  [right_part]: { reflexivity. }
Qed.

(* Q3b probe: out-of-order selector fills *)
Lemma q3_out_of_order : True /\ (3 = 3).
Proof.
  refine (conj ?[a] ?[b]).
  [b]: { reflexivity. }
  [a]: { exact I. }
Qed.

(* Q3c probe: incremental — selector fills to be added via tools *)
Lemma q3_incremental : True /\ (4 = 4).
Proof.
  refine (conj ?[ga] ?[gb]).
- [gb]: reflexivity.
Admitted.

(* Order probe: goal-list order vs existential creation order *)
Lemma order_probe : (True /\ True) /\ (2 = 2).
Proof.
Admitted.

(* Q1b probe: typeclass hole noise *)
Lemma q1_typeclass : forall (x y : nat), {x = y} + {x <> y}.
Proof.
Admitted.
