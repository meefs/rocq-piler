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

Lemma insert_leb_false : forall x y l, (x <=? y) = false -> insert x (y :: l) = y :: insert x l.
Proof.
  intros. simpl. destruct (x <=? y); congruence.
Qed.

Lemma insert_sorted : forall x l, sorted l -> sorted (insert x l).
Proof.
  induction l as [|h t IH].
  - intro. simpl. apply sorted_single.
  - intro H. simpl.
    destruct (x <=? h) eqn:E.
    + apply leb_complete in E.
      inversion H as [| | x0 y l0 Hle Hsorted]; subst.
      * constructor; [exact E | apply sorted_single].
      * constructor; [exact E | constructor; assumption].
    + apply leb_complete_conv in E.
      assert (Hhx : h <= x) by (apply Nat.lt_le_incl; exact E).
      inversion H as [| | x0 y l0 Hle Hsorted]; subst.
      * simpl. constructor; [exact Hhx | apply sorted_single].
      * clear H.
        simpl.
        destruct (x <=? y) eqn:Ey.
        -- apply leb_complete in Ey.
           constructor.
           { exact Hhx. }
           { constructor; [exact Ey | exact Hsorted]. }
        -- apply IH in Hsorted.
           apply (insert_leb_false x y l0) in Ey.
           rewrite Ey in Hsorted.
           constructor.
           { exact Hle. }
           { exact Hsorted. }
Qed.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Theorem insertion_sort_sorted : forall (l : list nat),
  sorted (insertion_sort l).
Proof.
  induction l as [|h t IH].
  - simpl. apply sorted_nil.
  - simpl. apply insert_sorted. apply IH.
Qed.

Theorem insertion_sort_sorted_neg : ~ (forall (l : list nat),
  sorted (insertion_sort l)).
Proof.
Admitted.
