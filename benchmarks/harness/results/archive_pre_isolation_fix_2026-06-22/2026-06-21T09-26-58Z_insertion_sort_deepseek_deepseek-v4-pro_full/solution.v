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

Lemma insert_cons_le : forall l x a, a <= x -> sorted (a :: l) -> sorted (a :: insert x l).
Proof.
  induction l as [|b t IH]; intros x a Hax Hs.
  - simpl. apply sorted_cons; [exact Hax | apply sorted_single].
  - assert (Hab : a <= b) by (inversion Hs; assumption).
    assert (Hbt : sorted (b :: t)) by (inversion Hs; assumption).
    simpl. destruct (x <=? b) eqn:E.
    + apply Nat.leb_le in E.
      apply sorted_cons; [exact Hax|].
      apply sorted_cons; [exact E | exact Hbt].
    + apply Nat.leb_gt in E.
      apply sorted_cons; [exact Hab|].
      apply IH; [apply Nat.lt_le_incl; exact E | exact Hbt].
Qed.

Lemma insert_sorted : forall l x, sorted l -> sorted (insert x l).
Proof.
  destruct l as [|a t]; intros x Hs.
  - simpl. apply sorted_single.
  - simpl. destruct (x <=? a) eqn:E.
    + apply Nat.leb_le in E.
      apply sorted_cons; [exact E | exact Hs].
    + apply Nat.leb_gt in E.
      apply insert_cons_le; [apply Nat.lt_le_incl; exact E | exact Hs].
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
