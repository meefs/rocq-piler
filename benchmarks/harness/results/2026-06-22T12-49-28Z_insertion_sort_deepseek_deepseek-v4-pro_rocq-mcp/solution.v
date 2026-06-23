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

(** ** Helper lemmas *)

Lemma insert_sorted : forall n l, sorted l -> sorted (insert n l).
Proof.
  induction l as [|h t IH]; intros H_sorted.
  - apply sorted_single.
  - inversion H_sorted; subst; clear H_sorted.
    + simpl.
      destruct (n <=? h) eqn:H_cmp.
      * apply leb_complete in H_cmp.
        apply sorted_cons with (y:=h); [exact H_cmp | apply sorted_single].
      * apply leb_complete_conv in H_cmp.
        apply sorted_cons with (y:=n).
        -- apply Nat.lt_le_incl. exact H_cmp.
        -- apply sorted_single.
    + simpl.
      destruct (n <=? h) eqn:H_cmp.
      * apply leb_complete in H_cmp.
        apply sorted_cons with (y:=h); [exact H_cmp | ].
        constructor; assumption.
      * apply leb_complete_conv in H_cmp.
        simpl.
        destruct (n <=? y) eqn:H_cmp2.
        -- apply leb_complete in H_cmp2.
           apply sorted_cons with (y:=n).
           ++ apply Nat.lt_le_incl. exact H_cmp.
           ++ apply sorted_cons with (y:=y); [exact H_cmp2 | assumption].
        -- apply sorted_cons with (y:=y).
           ++ assumption.
           ++ assert (insert n (y :: l) = y :: insert n l) as H_eq.
              { simpl. rewrite H_cmp2. reflexivity. }
              rewrite <- H_eq.
              apply IH. assumption.
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
