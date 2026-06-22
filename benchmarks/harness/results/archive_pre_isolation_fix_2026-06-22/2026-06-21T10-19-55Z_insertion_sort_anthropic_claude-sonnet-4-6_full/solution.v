From Stdlib Require Import Arith List Lia.
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

(** Helper: inserting n into a sorted list yields a sorted list *)
Lemma insert_sorted : forall n l,
  sorted l -> sorted (insert n l).
Proof.
  intros n l Hsorted.
  induction Hsorted as [| x | x y l Hxy Hsorted IH].
  - (* l = [] *)
    simpl. apply sorted_single.
  - (* l = [x] *)
    simpl.
    destruct (n <=? x) eqn:Hnx.
    + apply Nat.leb_le in Hnx.
      apply sorted_cons; [exact Hnx | apply sorted_single].
    + apply Nat.leb_gt in Hnx.
      apply sorted_cons; [lia | apply sorted_single].
  - (* l = x :: y :: l, sorted *)
    simpl.
    destruct (n <=? x) eqn:Hnx.
    + apply Nat.leb_le in Hnx.
      apply sorted_cons; [exact Hnx | apply sorted_cons; [exact Hxy | exact Hsorted]].
    + apply Nat.leb_gt in Hnx.
      (* n > x, so insert n (y :: l) *)
      simpl in IH.
      destruct (n <=? y) eqn:Hny.
      * apply Nat.leb_le in Hny.
        apply sorted_cons; [lia | apply sorted_cons; [exact Hny | exact Hsorted]].
      * apply Nat.leb_gt in Hny.
        apply sorted_cons; [exact Hxy | exact IH].
Qed.

Theorem insertion_sort_sorted : forall (l : list nat),
  sorted (insertion_sort l).
Proof.
  intros l.
  induction l as [| h t IH].
  - simpl. apply sorted_nil.
  - simpl. apply insert_sorted. exact IH.
Qed.

Theorem insertion_sort_sorted_neg : ~ (forall (l : list nat),
  sorted (insertion_sort l)).
Proof.
Admitted.
