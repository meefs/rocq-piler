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

Lemma sorted_insert : forall n l, sorted l -> sorted (insert n l).
Proof.
  intros n l Hsort.
  induction l as [|h t IH]; simpl.
  - apply sorted_single.
  - inversion Hsort as [|?|x y l' Hle Hsorted_t].
    + subst. simpl.
      destruct (n <=? h) eqn:Hcase.
      * apply leb_complete in Hcase.
        apply sorted_cons with (y:=h); [exact Hcase | apply sorted_single].
      * apply Nat.leb_gt in Hcase.
        apply Nat.lt_le_incl in Hcase.
        apply sorted_cons with (y:=n); [exact Hcase | apply sorted_single].
    + subst.
      destruct (n <=? h) eqn:Hcase.
      * apply leb_complete in Hcase.
        apply sorted_cons with (y:=h); [exact Hcase | ].
        apply sorted_cons with (y:=y); [exact Hle | exact Hsorted_t].
      * apply IH in Hsorted_t.
        destruct (n <=? y) eqn:Hcase2.
        -- destruct (insert n (y :: l')) eqn:Hinsert.
           ++ unfold insert in Hinsert. destruct (n <=? y); discriminate Hinsert.
           ++ unfold insert in Hinsert. rewrite Hcase2 in Hinsert.
              inversion Hinsert. subst. clear Hinsert.
              apply sorted_cons with (y:=n0); [ | exact Hsorted_t].
              apply Nat.leb_gt in Hcase.
              apply Nat.lt_le_incl in Hcase.
              exact Hcase.
        -- destruct (insert n (y :: l')) eqn:Hinsert.
           ++ unfold insert in Hinsert. rewrite Hcase2 in Hinsert. discriminate Hinsert.
           ++ unfold insert in Hinsert. rewrite Hcase2 in Hinsert.
              inversion Hinsert. subst. clear Hinsert.
              apply sorted_cons with (y:=n0); [exact Hle | exact Hsorted_t].
Qed.

Theorem insertion_sort_sorted : forall (l : list nat),
  sorted (insertion_sort l).
Proof.
  induction l as [|h t IH]; simpl.
  - apply sorted_nil.
  - apply sorted_insert.
    exact IH.
Qed.

Theorem insertion_sort_sorted_neg : ~ (forall (l : list nat),
  sorted (insertion_sort l)).
Proof.
Admitted.
