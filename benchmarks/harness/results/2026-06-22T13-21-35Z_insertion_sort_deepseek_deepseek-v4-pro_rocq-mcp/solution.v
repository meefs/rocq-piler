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

Lemma insert_sorted : forall n l, sorted l -> sorted (insert n l).
Proof.
  intros n l H.
  induction H as [|x| x y l' Hle Hs IHs].
  - simpl. apply sorted_single.
  - simpl. destruct (n <=? x) eqn:En.
    + apply Nat.leb_le in En.
      apply (sorted_cons n x [] En (sorted_single x)).
    + apply Nat.leb_gt in En.
      apply (sorted_cons x n []).
      * apply Nat.lt_le_incl. exact En.
      * apply sorted_single.
  - simpl. destruct (n <=? x) eqn:En.
    + apply Nat.leb_le in En.
      apply (sorted_cons n x (y :: l')).
      * exact En.
      * apply (sorted_cons x y l' Hle Hs).
    + apply Nat.leb_gt in En.
      destruct (n <=? y) eqn:En2.
      * apply Nat.leb_le in En2.
        apply (sorted_cons x n (y :: l')).
        -- apply Nat.lt_le_incl. exact En.
        -- apply (sorted_cons n y l').
          ++ exact En2.
          ++ exact Hs.
      * assert (Heq : insert n (y :: l') = y :: insert n l').
        { simpl. rewrite En2. reflexivity. }
        rewrite Heq in IHs.
        apply (sorted_cons x y (insert n l')).
        -- exact Hle.
        -- exact IHs.
Qed.

Theorem insertion_sort_sorted : forall (l : list nat),
  sorted (insertion_sort l).
Proof.
  induction l as [|h t IH].
  - simpl. apply sorted_nil.
  - simpl. apply (insert_sorted h (insertion_sort t) IH).
Qed.

Theorem insertion_sort_sorted_neg : ~ (forall (l : list nat),
  sorted (insertion_sort l)).
Proof.
Admitted.
