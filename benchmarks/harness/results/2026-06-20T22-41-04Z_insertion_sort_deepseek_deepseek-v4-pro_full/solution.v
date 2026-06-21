Require Import Nat List.
Import ListNotations.

(** * Insertion Sort Correctness — Benchmark *)

Lemma leb_le : forall n m, (n <=? m) = true -> n <= m.
Proof.
intros n m H; apply PeanoNat.Nat.leb_le; exact H.
Qed.

Lemma leb_gt : forall n m, (n <=? m) = false -> m < n.
Proof.
intros n m H; apply PeanoNat.Nat.leb_gt; exact H.
Qed.

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

Lemma insert_sorted : forall (n : nat) (l : list nat),
  sorted l -> sorted (insert n l).
Proof.
  intros n l Hs; induction Hs as [| x | x y l Hxy Hsl IH]; simpl.
  { (* sorted_nil:b210a71e *) solve [ constructor ]. }
  { (* sorted_single:1ebbf7b3 *) destruct (n <=? x) eqn:E; apply sorted_cons; [apply leb_le; exact E | apply sorted_single | apply PeanoNat.Nat.lt_le_incl; apply leb_gt; exact E | apply sorted_single].
  }
  { (* sorted_cons:e7817dd3 *) destruct (n <=? x) eqn:E1.
    { (* 4b719908 *) apply sorted_cons; [apply leb_le; exact E1 | apply sorted_cons; [exact Hxy | exact Hsl]].
    }
    { (* c2a650ea *) destruct (n <=? y) eqn:E2.
      { (* 6966b08a *) apply sorted_cons; [apply PeanoNat.Nat.lt_le_incl; apply leb_gt; exact E1 | apply sorted_cons; [apply leb_le; exact E2 | exact Hsl]].
      }
      { (* 14b9da48 *) simpl in IH; rewrite E2 in IH; apply sorted_cons; [exact Hxy | exact IH].
      }
    }
  }
Qed.

Lemma insert_sorted_neg : ~ (forall (n : nat) (l : list nat),
  sorted l -> sorted (insert n l)).
Proof.
Admitted.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Theorem insertion_sort_sorted : forall (l : list nat),
  sorted (insertion_sort l).
Proof.
induction l as [| h t IH]; simpl; [apply sorted_nil | apply insert_sorted; exact IH].
Qed.

Theorem insertion_sort_sorted_neg : ~ (forall (l : list nat),
  sorted (insertion_sort l)).
Proof.
Admitted.
