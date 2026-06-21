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



From Stdlib Require Import Lia.

Lemma insert_sorted : forall n l, sorted l -> sorted (insert n l).
Proof.
  intros n l H; induction H; simpl.
  { (* sorted_nil:b210a71e *) solve [ constructor ]. }
  { (* sorted_single:1ebbf7b3 *) solve [ destruct (n <=? x) eqn:E; [apply Nat.leb_le in E; constructor; auto; constructor | apply Nat.leb_gt in E; constructor; [lia | constructor]] ]. }
  { (* sorted_cons:e7817dd3 *) destruct (n <=? x) eqn:E1; [apply Nat.leb_le in E1; constructor; auto | apply Nat.leb_gt in E1; simpl in IHsorted; destruct (n <=? y) eqn:E2; [apply Nat.leb_le in E2; constructor; [lia | constructor; auto] | constructor; auto]].
    { (* d99fd161 *) constructor; assumption.
    }
  }
Qed.

Theorem insertion_sort_sorted : forall (l : list nat),
  sorted (insertion_sort l).
Proof.
induction l; simpl; [constructor | apply insert_sorted; auto].
Qed.

Theorem insertion_sort_sorted_neg : ~ (forall (l : list nat),
  sorted (insertion_sort l)).
Proof.
Admitted.
