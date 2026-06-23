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
  intros n l H. revert n.
  induction H as [|x| x y l Hle Hsorted IH]; intros n'; simpl.
  - apply sorted_single.
  - case_eq (n' <=? x); intros Hcmp.
    + apply Nat.leb_le in Hcmp.
      apply (sorted_cons n' x [] Hcmp). apply sorted_single.
    + apply Nat.leb_gt in Hcmp. apply Nat.lt_le_incl in Hcmp.
      apply (sorted_cons x n' [] Hcmp). apply sorted_single.
  - case_eq (n' <=? x); intros Hcmp_x.
    + apply Nat.leb_le in Hcmp_x.
      apply (sorted_cons n' x (y :: l) Hcmp_x).
      apply (sorted_cons x y l Hle). exact Hsorted.
    + apply Nat.leb_gt in Hcmp_x. apply Nat.lt_le_incl in Hcmp_x.
      specialize (IH n'). simpl in IH.
      case_eq (n' <=? y); intros Hcmp_y.
      * apply Nat.leb_le in Hcmp_y.
        apply (sorted_cons x n' (y :: l) Hcmp_x).
        apply (sorted_cons n' y l Hcmp_y). exact Hsorted.
      * rewrite Hcmp_y in IH.
        apply (sorted_cons x y (insert n' l) Hle). exact IH.
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
