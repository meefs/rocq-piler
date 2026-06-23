From Stdlib Require Import Arith List.
Import ListNotations.
Require Import Lia.

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
  intros n l H. induction H.
  - simpl. apply sorted_single.
  - simpl. destruct (n <=? x) eqn:Heq.
    + apply Nat.leb_le in Heq. apply sorted_cons.
      { exact Heq. }
      { apply sorted_single. }
    + apply Nat.leb_nle in Heq. apply sorted_cons.
      { lia. }
      { apply sorted_single. }
  - simpl. destruct (n <=? x) eqn:Heq.
    + apply Nat.leb_le in Heq. apply sorted_cons.
      { exact Heq. }
      { exact (sorted_cons _ _ _ H H0). }
    + apply Nat.leb_nle in Heq.
      simpl.
      destruct (n <=? y) eqn:Hcmp.
      * apply Nat.leb_le in Hcmp.
        apply sorted_cons.
        { lia. }
        { apply sorted_cons; [exact Hcmp | exact H0]. }
      * assert (insert n (y :: l) = y :: insert n l) as Heq_ins.
        { simpl. rewrite Hcmp. reflexivity. }
        rewrite Heq_ins in IHsorted.
        apply sorted_cons.
        { exact H. }
        { exact IHsorted. }
Qed.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

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
