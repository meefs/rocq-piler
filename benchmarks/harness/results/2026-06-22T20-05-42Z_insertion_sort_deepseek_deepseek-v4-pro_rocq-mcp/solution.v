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
  intros n l Hsort. revert n.
  induction Hsort as [|x| x y l0 Hle Hsort IH].
  - intro n. apply sorted_single.
  - intro n. simpl. destruct (n <=? x) eqn:E.
    + apply Nat.leb_le in E.
      apply sorted_cons with (y:=x) (l:=[]).
      * exact E.
      * apply sorted_single.
    + apply Nat.leb_gt in E.
      apply sorted_cons with (y:=n) (l:=[]).
      * apply Nat.lt_le_incl. exact E.
      * apply sorted_single.
  - intro n. simpl. destruct (n <=? x) eqn:Ex.
    + apply Nat.leb_le in Ex.
      apply sorted_cons with (y:=x) (l:=y::l0).
      * exact Ex.
      * apply sorted_cons with (y:=y) (l:=l0).
        -- exact Hle.
        -- exact Hsort.
    + apply Nat.leb_gt in Ex.
      pose proof (IH n) as Hins.
      destruct (n <=? y) eqn:Ey.
      * assert (Heq : insert n (y :: l0) = n :: y :: l0).
        { simpl. rewrite Ey. reflexivity. }
        rewrite Heq in Hins.
        apply sorted_cons with (y:=n) (l:=y::l0).
        -- apply Nat.lt_le_incl. exact Ex.
        -- exact Hins.
      * assert (Heq : insert n (y :: l0) = y :: insert n l0).
        { simpl. rewrite Ey. reflexivity. }
        rewrite Heq in Hins.
        apply sorted_cons with (y:=y) (l:=insert n l0).
        -- exact Hle.
        -- exact Hins.
Qed.

Theorem insertion_sort_sorted : forall (l : list nat),
  sorted (insertion_sort l).
Proof.
  induction l as [|h t IH].
  - apply sorted_nil.
  - simpl. apply insert_sorted. exact IH.
Qed.

Theorem insertion_sort_sorted_neg : ~ (forall (l : list nat),
  sorted (insertion_sort l)).
Proof.
Admitted.
