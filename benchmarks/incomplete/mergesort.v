Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Import ListNotations.

(** * Merge Sort Correctness — Benchmark *)
(* Definitions: merge, sorted, split, mergesort *)

Fixpoint merge (l1 l2 : list nat) : list nat :=
  match l1, l2 with
  | [], l2 => l2
  | l1, [] => l1
  | x :: xs, y :: ys =>
    if x <=? y then x :: merge xs (y :: ys)
    else y :: merge (x :: xs) ys
  end.

Inductive sorted : list nat -> Prop :=
  | sorted_nil : sorted []
  | sorted_singleton x : sorted [x]
  | sorted_cons x y l :
      x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Fixpoint split (l : list nat) : list nat * list nat :=
  match l with
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: rest =>
    let (l1, l2) := split rest in
    (x :: l1, y :: l2)
  end.

Fixpoint mergesort (l : list nat) : list nat :=
  match l with
  | [] => []
  | [x] => [x]
  | _ :: _ :: _ =>
    let (l1, l2) := split l in
    merge (mergesort l1) (mergesort l2)
  end.

Lemma sorted_cons_inv : forall x l,
  sorted (x :: l) -> sorted l.
Proof.
Admitted.

Lemma merge_sorted : forall l1 l2,
  sorted l1 -> sorted l2 -> sorted (merge l1 l2).
Proof.
Admitted.

Lemma split_length : forall l,
  length (fst (split l)) + length (snd (split l)) = length l.
Proof.
Admitted.

Lemma split_shorter_l : forall l,
  length (fst (split l)) < length l \/ length l <= 1.
Proof.
Admitted.

Lemma split_shorter_r : forall l,
  length (snd (split l)) < length l \/ length l <= 1.
Proof.
Admitted.

Theorem mergesort_sorted : forall l, sorted (mergesort l).
Proof.
Admitted.
