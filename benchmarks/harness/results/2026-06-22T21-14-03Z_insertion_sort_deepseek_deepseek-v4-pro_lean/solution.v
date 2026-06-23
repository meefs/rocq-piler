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

Lemma insert_preserves_sorted : forall x l,
  sorted l -> sorted (insert x l).
Proof.
  intros x l H.
  induction H as [| x' | x' y' l' Hle Hsorted IH].
  - simpl. apply sorted_single.
  - simpl.
    destruct (x <=? x') eqn:E.
    { apply sorted_cons with (y := x').
      - apply Nat.leb_le. exact E.
      - apply sorted_single. }
    { apply sorted_cons with (y := x).
      - apply Nat.leb_nle in E. apply Nat.nle_gt in E. apply Nat.lt_le_incl. exact E.
      - apply sorted_single. }
  - simpl.
    destruct (x <=? x') eqn:E.
    { apply sorted_cons with (y := x').
      - apply Nat.leb_le. exact E.
      - constructor; [exact Hle | exact Hsorted]. }
    { destruct (x <=? y') eqn:E2.
      { apply sorted_cons with (y := x).
        - apply Nat.leb_nle in E. apply Nat.nle_gt in E. apply Nat.lt_le_incl. exact E.
        - apply sorted_cons with (y := y').
          + apply Nat.leb_le. exact E2.
          + exact Hsorted. }
      { apply sorted_cons with (y := y').
        - exact Hle.
        - simpl in IH. rewrite E2 in IH. exact IH. } }
Qed.
Theorem insertion_sort_sorted : forall (l : list nat),
  sorted (insertion_sort l).
Proof.
  induction l as [| h t IH].
  - simpl. apply sorted_nil.
  - simpl. apply insert_preserves_sorted. exact IH.
Qed.

Theorem insertion_sort_sorted_neg : ~ (forall (l : list nat),
  sorted (insertion_sort l)).
Proof.
Admitted.