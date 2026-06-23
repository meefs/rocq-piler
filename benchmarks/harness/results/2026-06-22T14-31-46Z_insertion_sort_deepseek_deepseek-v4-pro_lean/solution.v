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
  induction 1 as [ | x | x y l Hle Hs IH ].
  - simpl. apply sorted_single.
  - simpl. destruct (Nat.leb_spec n x) as [Hle'|Hlt'].
    + apply (sorted_cons n x [] Hle'). apply sorted_single.
    + apply (sorted_cons x n []). apply Nat.lt_le_incl, Hlt'. apply sorted_single.
  - simpl. destruct (Nat.leb_spec n x) as [Hle'|Hlt'].
    + apply (sorted_cons n x (y :: l) Hle').
      apply (sorted_cons x y l Hle Hs).
    + destruct (n <=? y) eqn:Heq.
      * apply sorted_cons with (x := x) (y := n) (l := y :: l).
        -- apply Nat.lt_le_incl, Hlt'.
        -- apply sorted_cons with (x := n) (y := y) (l := l).
           ++ apply Nat.leb_le, Heq.
           ++ exact Hs.
      * apply sorted_cons with (x := x) (y := y) (l := insert n l).
        -- exact Hle.
        -- simpl in IH; rewrite Heq in IH; exact IH.
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
