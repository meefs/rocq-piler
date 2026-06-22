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

Lemma insert_le_head : forall n x l,
  x <= n -> sorted (x :: l) -> sorted (x :: insert n l).
Proof.
  intro n. intro x. intro l. revert x.
  induction l as [| h t IH]; intros x Hxn Hs.
  - simpl. constructor. assumption. constructor.
  - simpl. destruct (Nat.leb_spec n h) as [Hnh | Hnh].
    + inversion Hs; subst.
      constructor. assumption. constructor; assumption.
    + inversion Hs; subst.
      constructor. assumption.
      apply IH. lia. assumption.
Qed.

Lemma insert_sorted : forall n l,
  sorted l -> sorted (insert n l).
Proof.
  intros n l Hsorted.
  induction l as [| h t IH].
  - simpl. constructor.
  - simpl. destruct (Nat.leb_spec n h) as [Hnh | Hnh].
    + constructor; assumption.
    + apply insert_le_head. lia.
      inversion Hsorted; subst; assumption.
Qed.

Theorem insertion_sort_sorted : forall (l : list nat),
  sorted (insertion_sort l).
Proof.
  induction l as [| h t IH].
  - simpl. constructor.
  - simpl. apply insert_sorted. assumption.
Qed.

Theorem insertion_sort_sorted_neg : ~ (forall (l : list nat),
  sorted (insertion_sort l)).
Proof.
Admitted.
