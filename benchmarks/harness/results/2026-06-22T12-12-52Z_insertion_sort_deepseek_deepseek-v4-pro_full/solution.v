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



Lemma insert_head_ge : forall n a b l z zs,
  a <= b ->
  n > a ->
  insert n (b :: l) = z :: zs ->
  a <= z.
Proof.
intros n a b l z zs Hle Hgt Hins. simpl in Hins. destruct (n <=? b) eqn:Heq.
- inversion Hins.
subst z. apply Nat.lt_le_incl; exact Hgt.
- inversion Hins.
subst z. exact Hle.
Qed.

Lemma insert_sorted : forall n l, sorted l -> sorted (insert n l).
Proof.
intros n l Hsort. induction Hsort.
- simpl. apply sorted_single.
- simpl. destruct (n <=? x) eqn:Heq.
  + apply Nat.leb_le in Heq. apply sorted_cons with (y := x) (l := []); auto. apply sorted_single.
+ apply Nat.leb_gt in Heq. apply sorted_cons with (y := n) (l := []). apply Nat.lt_le_incl; exact Heq. apply sorted_single.
- simpl. destruct (n <=? x) eqn:Heq.
  + apply Nat.leb_le in Heq. apply sorted_cons with (y := x) (l := y :: l); auto. constructor; auto.
+ apply Nat.leb_gt in Heq. destruct (n <=? y) eqn:Heq2.
  -- apply Nat.leb_le in Heq2. apply sorted_cons with (y := n) (l := y :: l). apply Nat.lt_le_incl; exact Heq. apply sorted_cons with (y := y) (l := l); auto.
-- apply Nat.leb_gt in Heq2.
simpl in IHHsort. apply sorted_cons with (y := y) (l := insert n l); auto.
rewrite (proj2 (Nat.leb_gt n y) Heq2) in IHHsort. exact IHHsort.
Qed.

Theorem insertion_sort_sorted : forall (l : list nat),
  sorted (insertion_sort l).
Proof.
induction l as [| h t IH]. simpl. apply sorted_nil. simpl. apply insert_sorted. exact IH.
Qed.

Theorem insertion_sort_sorted_neg : ~ (forall (l : list nat),
  sorted (insertion_sort l)).
Proof.
Admitted.
