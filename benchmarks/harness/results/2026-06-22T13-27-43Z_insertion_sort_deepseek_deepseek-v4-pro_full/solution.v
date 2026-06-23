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

Lemma insert_preserves_sorted : forall n l, sorted l -> sorted (insert n l).
Proof.
  intros n l.
  induction l as [|a l' IH].
  - intro. simpl. apply sorted_single.
  - intro H.
    inversion H as [|x| x y l'' Hle Hsort'].
    + subst. simpl. destruct (n <=? a) eqn:E.
      * apply sorted_cons with (y := a) (l := []); [apply Nat.leb_le; eauto | apply sorted_single].
      * apply sorted_cons with (y := n) (l := []); [apply Nat.lt_le_incl, Nat.leb_gt; eauto | apply sorted_single].
    + subst.
      simpl. destruct (n <=? a) eqn:Ena.
      * apply sorted_cons with (y := a) (l := y :: l'').
        { apply Nat.leb_le; assumption. }
        { apply sorted_cons with (y := y) (l := l''); assumption. }
      * apply Nat.leb_gt in Ena.
        destruct (n <=? y) eqn:Eny.
        { apply sorted_cons with (y := n) (l := y :: l'').
          - apply Nat.lt_le_incl. exact Ena.
          - apply sorted_cons with (y := y) (l := l'').
            + apply Nat.leb_le. exact Eny.
            + exact Hsort'. }
        { apply sorted_cons with (y := y) (l := insert n l'').
          - exact Hle.
          - assert (Heq : insert n (y :: l'') = y :: insert n l'').
            { simpl. rewrite Eny. reflexivity. }
            apply IH in Hsort'.
            rewrite Heq in Hsort'.
            exact Hsort'. }
Qed.

Theorem insertion_sort_sorted : forall (l : list nat),
  sorted (insertion_sort l).
Proof.
  induction l as [|h t].
  - simpl. apply sorted_nil.
  - simpl. apply insert_preserves_sorted. exact IHt.
Qed.

Theorem insertion_sort_sorted_neg : ~ (forall (l : list nat),
  sorted (insertion_sort l)).
Proof.
Admitted.
