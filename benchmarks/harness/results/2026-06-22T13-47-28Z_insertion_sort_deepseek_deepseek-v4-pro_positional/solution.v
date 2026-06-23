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

Lemma insert_ge_sorted : forall n l a,
  sorted (a :: l) -> a <= n -> sorted (a :: insert n l).
Proof.
  induction l as [|b l IH]; intros a Hs Hle.
  - apply (sorted_cons a n []); auto. apply sorted_single.
  - inversion Hs as [?|x y l' Hle' Hrest]; subst.
    + (* sorted_single: l = [] *) simpl.
      apply (sorted_cons a n []); auto. apply sorted_single.
    + simpl. destruct (n <=? y) eqn:E.
      * apply Nat.leb_complete in E.
        apply (sorted_cons x n (y :: l')); auto.
        apply (sorted_cons n y l'); auto.
      * apply Nat.leb_nle in E. apply Nat.nle_gt in E. apply Nat.lt_le_incl in E.
        apply (sorted_cons x y (insert n l')).
        -- exact Hle'.
        -- apply (IH y Hrest E).
Qed.

Lemma insert_sorted : forall n l, sorted l -> sorted (insert n l).
Proof.
  induction l as [|a l IH]; intros Hs.
  - apply sorted_single.
  - inversion Hs as [?|x y l' Hle Hrest]; subst.
    + simpl. apply (sorted_cons a n []); auto. apply sorted_single.
    + simpl. destruct (n <=? x) eqn:E.
      * apply Nat.leb_complete in E. apply (sorted_cons n x (y :: l')); auto.
        exact (sorted_cons x y l' Hle Hrest).
      * apply Nat.leb_nle in E. apply Nat.nle_gt in E. apply Nat.lt_le_incl in E.
        apply (insert_ge_sorted n (y :: l') x).
        -- exact (sorted_cons x y l' Hle Hrest).
        -- exact E.
Qed.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Theorem insertion_sort_sorted : forall (l : list nat),
  sorted (insertion_sort l).
Proof.
  induction l as [|a l IH].
  - apply sorted_nil.
  - simpl. apply insert_sorted. exact IH.
Qed.

Theorem insertion_sort_sorted_neg : ~ (forall (l : list nat),
  sorted (insertion_sort l)).
Proof.
Admitted.
