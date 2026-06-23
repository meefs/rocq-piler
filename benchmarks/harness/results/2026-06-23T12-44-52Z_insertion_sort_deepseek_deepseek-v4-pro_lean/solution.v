From Stdlib Require Import Arith List.
Import ListNotations.

(** * Insertion Sort Correctness — Benchmark *)

Fixpoint insert (n : nat) (l : list nat) : list nat :=
  match l with
  | [] => [n]
  | h :: t => if n <=? h then n :: h :: t else h :: insert n t
  end.

Fixpoint insertion_sort (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => insert h (insertion_sort t)
  end.

Inductive sorted : list nat -> Prop :=
| sorted_nil : sorted []
| sorted_single : forall x, sorted [x]
| sorted_cons : forall x y l, x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Lemma insert_sorted : forall n l, sorted l -> sorted (insert n l).
Proof.
  intros n l Hsorted.
  induction Hsorted as [|x| x y l' Hle Hsorted' IH].
  - simpl. apply sorted_single.
  - simpl.
    destruct (n <=? x) eqn:Hcmp.
    + apply Nat.leb_le in Hcmp.
      apply sorted_cons with (x := n) (y := x) (l := []); [exact Hcmp|apply sorted_single].
    + apply Nat.leb_nle in Hcmp.
      apply sorted_cons with (x := x) (y := n) (l := []).
      * apply Nat.lt_le_incl. apply Nat.nle_gt. exact Hcmp.
      * apply sorted_single.
  - simpl.
    destruct (n <=? x) eqn:Hcmp.
    + apply Nat.leb_le in Hcmp.
      apply sorted_cons with (x := n) (y := x) (l := y :: l'); [exact Hcmp|].
      apply sorted_cons with (x := x) (y := y) (l := l'); assumption.
    + apply Nat.leb_nle in Hcmp.
      assert (Hxn : x <= n).
      { apply Nat.lt_le_incl. apply Nat.nle_gt. exact Hcmp. }
      destruct (n <=? y) eqn:Hcmp2.
      * apply Nat.leb_le in Hcmp2.
        apply sorted_cons with (x := x) (y := n) (l := y :: l'); [exact Hxn|].
        apply sorted_cons with (x := n) (y := y) (l := l'); [exact Hcmp2|exact Hsorted'].
      * cbv [insert] in *.
        rewrite Hcmp2 in *.
        apply sorted_cons with (x := x) (y := y) (l := insert n l').
        -- exact Hle.
        -- exact IH.
Qed.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Theorem insertion_sort_sorted : forall (l : list nat),
  sorted (insertion_sort l).
Proof.
  induction l as [|h t IH].
  - simpl. apply sorted_nil.
  - simpl. apply insert_sorted. exact IH.
Qed.

Theorem insertion_sort_sorted_neg : ~ (forall (l : list nat),
  sorted (insertion_sort l)).
Proof.
Admitted.
