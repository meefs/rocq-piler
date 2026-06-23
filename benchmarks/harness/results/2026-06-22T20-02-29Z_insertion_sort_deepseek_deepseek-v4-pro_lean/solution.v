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

Lemma insert_sorted : forall l, sorted l -> forall n, sorted (insert n l).
Proof.
  induction 1 as [ | a | a b l Hle Hrest IH]; simpl; intro n.
  - apply sorted_single.
  - destruct (n <=? a) eqn:H.
    + apply sorted_cons with (x:=n) (y:=a) (l:=[]).
      * apply Nat.leb_le, H.
      * apply sorted_single.
    + apply sorted_cons with (x:=a) (y:=n) (l:=[]).
      * apply Nat.lt_le_incl. apply Nat.leb_gt, H.
      * apply sorted_single.
  - destruct (n <=? a) eqn:H.
    + apply sorted_cons with (x:=n) (y:=a) (l:=b::l).
      * apply Nat.leb_le, H.
      * apply sorted_cons with (x:=a) (y:=b) (l:=l); auto.
    + pose proof (IH n) as Hinsert_sorted.
      destruct (n <=? b) eqn:Hnb.
      * unfold insert in Hinsert_sorted. rewrite Hnb in Hinsert_sorted.
        apply sorted_cons with (x:=a) (y:=n) (l:=b::l).
        -- apply Nat.lt_le_incl. apply Nat.leb_gt, H.
        -- exact Hinsert_sorted.
      * unfold insert in Hinsert_sorted. rewrite Hnb in Hinsert_sorted.
        apply sorted_cons with (x:=a) (y:=b) (l:=insert n l).
        -- apply Hle.
        -- exact Hinsert_sorted.
Qed.

Theorem insertion_sort_sorted : forall (l : list nat),
  sorted (insertion_sort l).
Proof.
  induction l as [|h t IH]; simpl.
  - apply sorted_nil.
  - apply insert_sorted, IH.
Qed.

Theorem insertion_sort_sorted_neg : ~ (forall (l : list nat),
  sorted (insertion_sort l)).
Proof.
Admitted.
