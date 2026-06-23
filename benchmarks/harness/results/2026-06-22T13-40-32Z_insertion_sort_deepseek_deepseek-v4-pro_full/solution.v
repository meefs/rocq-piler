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
  intros n l H. induction H as [|x| x y l Hxy Hsorted IH].
  - apply sorted_single.
  - simpl. destruct (n <=? x) eqn:Ex.
    + apply sorted_cons with (x:=n) (y:=x) (l:=[]).
      * apply Nat.leb_le. exact Ex.
      * apply sorted_single.
    + apply sorted_cons with (x:=x) (y:=n) (l:=[]).
      * apply Nat.leb_gt in Ex. apply Nat.lt_le_incl. exact Ex.
      * apply sorted_single.
  - simpl. destruct (n <=? x) eqn:Ex.
    + apply sorted_cons with (x:=n) (y:=x) (l:=y::l).
      * apply Nat.leb_le. exact Ex.
      * apply sorted_cons with (x:=x) (y:=y) (l:=l).
        -- exact Hxy.
        -- exact Hsorted.
    + destruct (n <=? y) eqn:Ey.
      * apply sorted_cons with (x:=x) (y:=n) (l:=y::l).
        -- apply Nat.leb_gt in Ex. apply Nat.lt_le_incl. exact Ex.
        -- apply sorted_cons with (x:=n) (y:=y) (l:=l).
           ++ apply Nat.leb_le. exact Ey.
           ++ exact Hsorted.
      * simpl in IH. rewrite Ey in IH.
        apply sorted_cons with (x:=x) (y:=y) (l:=insert n l).
        -- exact Hxy.
        -- exact IH.
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
