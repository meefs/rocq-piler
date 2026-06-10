Require Import Nat List.
Import ListNotations.

(** * Insertion Sort Correctness — Benchmark *)

Lemma leb_le : forall n m, (n <=? m) = true -> n <= m.
Proof.
Admitted.

Lemma leb_gt : forall n m, (n <=? m) = false -> m < n.
Proof.
Admitted.

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

Lemma insert_sorted : forall (n : nat) (l : list nat),
  sorted l -> sorted (insert n l).
Proof.
Admitted.

Theorem insertion_sort_sorted : forall (l : list nat),
  sorted (insertion_sort l).
Proof.
Admitted.
