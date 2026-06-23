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

Theorem insertion_sort_sorted : forall (l : list nat),
  sorted (insertion_sort l).
Proof.
  induction l as [|h t IH].
  - apply sorted_nil.
  - simpl.
    assert (insert_sorted : forall x l, sorted l -> sorted (insert x l)).
    { intros x l Hsorted.
      induction Hsorted as [|a0| a0 b m0 Hale Hsorted' IHi].
      - apply sorted_single.
      - simpl. destruct (x <=? a0) eqn:E.
        + apply sorted_cons with (y:=a0).
          * apply Nat.leb_le. exact E.
          * apply sorted_single.
        + apply sorted_cons with (y:=x).
          * apply Nat.leb_gt in E. apply Nat.lt_le_incl. exact E.
          * apply sorted_single.
      - simpl. destruct (x <=? a0) eqn:E1.
        + apply sorted_cons with (y:=a0).
          * apply Nat.leb_le. exact E1.
          * apply sorted_cons with (y:=b). exact Hale. exact Hsorted'.
        + simpl. destruct (x <=? b) eqn:E2.
          * apply sorted_cons with (y:=x).
            { apply Nat.leb_gt in E1. apply Nat.lt_le_incl. exact E1. }
            apply sorted_cons with (y:=b).
            { apply Nat.leb_le. exact E2. }
            exact Hsorted'.
          * apply sorted_cons with (y:=b).
            { exact Hale. }
            unfold insert in IHi. rewrite E2 in IHi. simpl in IHi.
            exact IHi.
    }
    apply (insert_sorted h (insertion_sort t)). exact IH.
Qed.

Theorem insertion_sort_sorted_neg : ~ (forall (l : list nat),
  sorted (insertion_sort l)).
Proof.
Admitted.
