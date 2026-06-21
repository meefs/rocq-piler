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

Lemma insert_sorted : forall n l, sorted l -> sorted (insert n l).
Proof.
  intros n l Hs.
  induction Hs as [| x | x y l' Hxy Hs' IH].
  - simpl. constructor.
  - simpl. destruct (Nat.leb_spec n x).
    + constructor. auto. constructor.
    + constructor. lia. constructor.
  - simpl. destruct (Nat.leb_spec n x).
    + constructor. auto. constructor. auto. auto.
    + simpl in IH. destruct (Nat.leb_spec n y).
      * constructor. lia. constructor. auto. auto.
      * constructor. auto. auto.
Qed.

Theorem insertion_sort_sorted : forall (l : list nat),
  sorted (insertion_sort l).
Proof.
  induction l as [| h t IH].
  - simpl. constructor.
  - simpl. apply insert_sorted. auto.
Qed.

Theorem insertion_sort_sorted_neg : ~ (forall (l : list nat),
  sorted (insertion_sort l)).
Proof.
Admitted.
