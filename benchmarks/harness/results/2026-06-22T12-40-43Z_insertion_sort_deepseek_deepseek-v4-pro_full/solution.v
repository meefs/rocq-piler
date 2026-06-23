From Stdlib Require Import Arith List.
Require Import Lia.
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

Lemma insert_cons : forall n h t, insert n (h :: t) = if n <=? h then n :: h :: t else h :: insert n t.
Proof. reflexivity. Qed.

Lemma insert_sorted : forall n l, sorted l -> sorted (insert n l).
Proof.
  intros n l.
  induction 1 as [|x| x y l' Hle Hsorted IH].
  - simpl. apply sorted_single.
  - simpl. destruct (n <=? x) eqn:Heq.
    + apply sorted_cons with (y:=x) (l:=[]).
      * apply Nat.leb_le in Heq. exact Heq.
      * apply sorted_single.
    + apply sorted_cons with (x:=x) (y:=n) (l:=[]).
      * apply Nat.leb_gt in Heq. lia.
      * apply sorted_single.
  - simpl.
    destruct (n <=? x) eqn:Heq.
    + apply Nat.leb_le in Heq.
      apply sorted_cons with (x:=n) (y:=x) (l:=y::l').
      * exact Heq.
      * apply sorted_cons with (x:=x) (y:=y) (l:=l').
        -- exact Hle.
        -- exact Hsorted.
    + apply Nat.leb_gt in Heq.
      destruct (n <=? y) eqn:Hny.
      * assert (Ht : n :: y :: l' = insert n (y :: l')).
        { simpl. destruct (n <=? y) eqn:Heq'.
          - reflexivity.
          - rewrite Hny in Heq'. discriminate. }
        rewrite <- Ht in IH.
        apply sorted_cons with (x:=x) (y:=n) (l:=y::l').
        -- apply Nat.leb_le in Hny. lia.
        -- exact IH.
      * assert (Ht : y :: insert n l' = insert n (y :: l')).
        { simpl. destruct (n <=? y) eqn:Heq'.
          - rewrite Hny in Heq'. discriminate.
          - reflexivity. }
        rewrite <- Ht in IH.
        apply sorted_cons with (x:=x) (y:=y) (l:=insert n l').
        -- exact Hle.
        -- exact IH.
Qed.

Theorem insertion_sort_sorted : forall (l : list nat),
  sorted (insertion_sort l).
Proof.
  induction l as [|h t IH]; simpl.
  - apply sorted_nil.
  - apply insert_sorted. exact IH.
Qed.

Theorem insertion_sort_sorted_neg : ~ (forall (l : list nat),
  sorted (insertion_sort l)).
Proof.
Admitted.
