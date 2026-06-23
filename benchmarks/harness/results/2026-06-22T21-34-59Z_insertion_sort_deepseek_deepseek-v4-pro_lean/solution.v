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

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Lemma insert_sorted : forall n l, sorted l -> sorted (insert n l).
Proof.
  induction 1 as [|x| x y l Hle Hsorted IH].
  - simpl. apply sorted_single.
  - simpl. case_eq (n <=? x); intros Hcmp.
    + apply Nat.leb_le in Hcmp.
      apply (sorted_cons n x [] Hcmp). apply sorted_single.
    + apply Nat.leb_nle in Hcmp.
      simpl.
      apply (sorted_cons x n []).
      apply Nat.lt_le_incl. apply Nat.nle_gt. exact Hcmp.
      apply sorted_single.
  - simpl. case_eq (n <=? x); intros Hcmp.
    + apply Nat.leb_le in Hcmp.
      apply (sorted_cons n x (y :: l) Hcmp).
      apply (sorted_cons x y l Hle Hsorted).
    + apply Nat.leb_nle in Hcmp.
      simpl.
      destruct (n <=? y) eqn:Hcmp2.
      * apply Nat.leb_le in Hcmp2.
        apply (sorted_cons x n (y :: l)).
        apply Nat.lt_le_incl. apply Nat.nle_gt. exact Hcmp.
        apply (sorted_cons n y l Hcmp2 Hsorted).
      * simpl in IH. rewrite Hcmp2 in IH. simpl in IH.
        apply (sorted_cons x y (insert n l) Hle IH).
Qed.

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
