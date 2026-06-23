From Stdlib Require Import Arith List Lia PeanoNat Permutation.
Import ListNotations.

(** * Merge Sort Correctness — Benchmark *)

Fixpoint merge (l1 l2 : list nat) {struct l1} : list nat :=
  match l1 with
  | [] => l2
  | x :: xs =>
    (fix merge_inner (l2 : list nat) : list nat :=
      match l2 with
      | [] => x :: xs
      | y :: ys =>
        if x <=? y then x :: merge xs l2
        else y :: merge_inner ys
      end) l2
  end.

Inductive sorted : list nat -> Prop :=
  | sorted_nil : sorted []
  | sorted_singleton x : sorted [x]
  | sorted_cons x y l :
      x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Fixpoint split (l : list nat) : list nat * list nat :=
  match l with
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: rest =>
    let (l1, l2) := split rest in
    (x :: l1, y :: l2)
  end.

Fixpoint mergesort (fuel : nat) (l : list nat) : list nat :=
  match fuel with
  | 0 => l
  | S fuel' =>
    match l with
    | [] => []
    | [x] => [x]
    | _ :: _ :: _ =>
      let (l1, l2) := split l in
      merge (mergesort fuel' l1) (mergesort fuel' l2)
    end
  end.

(** * Auxiliary Lemmas *)

Lemma sorted_all_ge : forall x l,
  sorted (x :: l) -> forall y, In y l -> x <= y.
Proof.
  intros x l H y Hin.
  revert x H y Hin.
  induction l as [|a l' IH]; intros x H y Hin.
  - inversion Hin.
  - inversion H as [| | x0 y0 l0 Hle Hs]; subst.
    destruct Hin as [Hy | Hy].
    + subst y. exact Hle.
    + apply Nat.le_trans with a.
      * exact Hle.
      * apply (IH a Hs y Hy).
Qed.

Lemma merge_lower_bound : forall l1 l2 a,
  (forall x, In x l1 -> a <= x) ->
  (forall x, In x l2 -> a <= x) ->
  forall x, In x (merge l1 l2) -> a <= x.
Proof.
  induction l1 as [|h1 t1 IH1]; simpl.
  - intros l2 a _ H2 x Hin. apply H2. exact Hin.
  - induction l2 as [|h2 t2 IH2]; simpl.
    + intros a H1 _ x Hin. apply H1. exact Hin.
    + intros a H1 H2 x Hin.
      destruct (h1 <=? h2) eqn:Hcmp.
      * destruct Hin as [Hin1 | Hin2].
        { subst x. apply H1. left; reflexivity. }
        { apply (IH1 (h2 :: t2) a).
          - intros z Hz. apply H1. right; exact Hz.
          - exact H2.
          - exact Hin2. }
      * destruct Hin as [Hin1 | Hin2].
        { subst x. apply H2. left; reflexivity. }
        { apply (IH2 a H1).
          - intros z Hz. apply H2. right; exact Hz.
          - exact Hin2. }
Qed.

Lemma sorted_tail : forall x l, sorted (x :: l) -> sorted l.
Proof.
  intros x l H. inversion H; subst; [apply sorted_nil | exact H3].
Qed.

Lemma sorted_cons_all : forall a l,
  sorted l -> (forall x, In x l -> a <= x) -> sorted (a :: l).
Proof.
  intros a l Hsort Hall.
  destruct l as [|h t].
  - apply sorted_singleton.
  - apply sorted_cons.
    + apply Hall. left; reflexivity.
    + exact Hsort.
Qed.

Lemma merge_sorted : forall l1 l2,
  sorted l1 -> sorted l2 -> sorted (merge l1 l2).
Proof.
  induction l1 as [|x xs IH1]; simpl; intros l2 H1 H2.
  - exact H2.
  - revert H1 H2.
    induction l2 as [|y ys IH2]; simpl; intros H1 H2.
    + exact H1.
    + destruct (x <=? y) eqn:Hcmp.
      * apply Nat.leb_le in Hcmp.
        apply sorted_cons_all.
        { apply (IH1 (y :: ys)).
          - apply sorted_tail with (x := x). exact H1.
          - exact H2. }
        { apply merge_lower_bound.
          - apply (sorted_all_ge x xs). exact H1.
          - intros z [Hz | Hz].
            + subst z. exact Hcmp.
            + apply Nat.le_trans with y.
              * exact Hcmp.
              * apply (sorted_all_ge y ys). exact H2. exact Hz. }
      * apply Nat.leb_gt in Hcmp.
        apply sorted_cons_all with (l := merge (x :: xs) ys).
        { apply IH2.
          - exact H1.
          - apply sorted_tail with (x := y). exact H2. }
        { apply merge_lower_bound with (l1 := x :: xs) (l2 := ys) (a := y).
          - intros z [Hz | Hz].
            + subst z. apply Nat.lt_le_incl, Hcmp.
            + apply Nat.le_trans with x.
              * apply Nat.lt_le_incl, Hcmp.
              * apply (sorted_all_ge x xs). exact H1. exact Hz.
          - apply (sorted_all_ge y ys). exact H2. }
Qed.

Fixpoint split_length_sum_eq (l : list nat) : forall l1 l2, split l = (l1, l2) -> length l1 + length l2 = length l.
Proof.
  destruct l as [|x l'].
  - intros l1 l2 H. inversion H. reflexivity.
  - destruct l' as [|y rest].
    + intros l1 l2 H. inversion H. reflexivity.
    + intros l1 l2 H.
      simpl in H.
      destruct (split rest) as [l1' l2'] eqn:Hsplit.
      inversion H. subst.
      simpl.
      assert (Hsum := split_length_sum_eq rest l1' l2' Hsplit).
      lia.
Qed.

Fixpoint split_perm_eq (l : list nat) : forall l1 l2, split l = (l1, l2) -> Permutation l (l1 ++ l2).
Proof.
  destruct l as [|x l'].
  - intros l1 l2 H. inversion H. subst. simpl. apply Permutation_refl.
  - destruct l' as [|y rest].
    + intros l1 l2 H. inversion H. subst. simpl. apply Permutation_refl.
    + intros l1 l2 H.
      simpl in H.
      destruct (split rest) as [l1' l2'] eqn:Hsplit.
      inversion H. subst. clear H.
      simpl.
      apply Permutation_trans with (x :: y :: (l1' ++ l2')).
       * apply perm_skip. apply perm_skip.
         apply (split_perm_eq rest l1' l2' Hsplit).
       * apply Permutation_trans with (x :: (l1' ++ y :: l2')).
         { apply perm_skip.
           apply Permutation_cons_app. apply Permutation_refl. }
        { simpl. apply Permutation_refl. }
Qed.

Lemma split_perm : forall l,
  let (l1, l2) := split l in
  Permutation l (l1 ++ l2).
Proof.
  intro l. destruct (split l) as [l1 l2] eqn:Heq.
  apply split_perm_eq; assumption.
Qed.

Lemma merge_perm : forall l1 l2,
  Permutation (l1 ++ l2) (merge l1 l2).
Proof.
  induction l1 as [|x xs IH1]; simpl; intros l2.
  - apply Permutation_refl.
  - induction l2 as [|y ys IH2]; simpl.
    + rewrite app_nil_r. apply Permutation_refl.
    + destruct (x <=? y) eqn:Hcmp.
      * apply perm_skip.
        apply IH1.
      * apply Permutation_trans with (y :: (x :: xs ++ ys)).
        { apply Permutation_trans with (x :: y :: xs ++ ys).
          - apply perm_skip.
            apply Permutation_sym.
            apply Permutation_cons_app. apply Permutation_refl.
          - apply perm_swap. }
        { apply perm_skip. apply IH2. }
Qed.

(** * Main Theorems *)

Lemma mergesort_sorted_aux : forall fuel l,
  length l <= fuel -> sorted (mergesort fuel l).
Proof.
  induction fuel as [|fuel' IH].
  - intros l Hle.
    assert (l = []) by (destruct l; [reflexivity | simpl in Hle; lia]).
    subst. simpl. apply sorted_nil.
  - intros l Hle.
    destruct l as [|x l'].
    + simpl. apply sorted_nil.
    + destruct l' as [|y rest].
      * simpl. apply sorted_singleton.
      * change (mergesort (S fuel') (x :: y :: rest)) with
          (let (l1, l2) := split (x :: y :: rest) in
           merge (mergesort fuel' l1) (mergesort fuel' l2)).
        case_eq (split (x :: y :: rest)); intros l1 l2 Hsplit.
        simpl in Hsplit.
        destruct (split rest) as [l1' l2'] eqn:Hsplit_rest.
        inversion Hsplit; subst; clear Hsplit.
        simpl.
        apply merge_sorted.
        { apply IH.
          pose proof (split_length_sum_eq rest l1' l2' Hsplit_rest) as Hsum.
          simpl in *. lia. }
        { apply IH.
          pose proof (split_length_sum_eq rest l1' l2' Hsplit_rest) as Hsum.
          simpl in *. lia. }
Qed.

Lemma mergesort_perm_aux : forall fuel l,
  Permutation l (mergesort fuel l).
Proof.
  induction fuel as [|fuel' IH].
  - intro l. simpl. apply Permutation_refl.
  - intro l. destruct l as [|x l'].
    + simpl. apply Permutation_refl.
    + destruct l' as [|y rest].
      * simpl. apply Permutation_refl.
      * change (mergesort (S fuel') (x :: y :: rest)) with
          (let (l1, l2) := split (x :: y :: rest) in
           merge (mergesort fuel' l1) (mergesort fuel' l2)).
        case_eq (split (x :: y :: rest)); intros l1 l2 Hsplit.
        simpl in Hsplit.
        destruct (split rest) as [l1' l2'] eqn:Hsplit_rest.
        inversion Hsplit; subst; clear Hsplit.
        simpl.
        apply Permutation_trans with (mergesort fuel' (x :: l1') ++ mergesort fuel' (y :: l2')).
        { apply Permutation_trans with ((x :: l1') ++ (y :: l2')).
          - assert (Hsplit_full : split (x :: y :: rest) = (x :: l1', y :: l2')).
            { simpl. rewrite Hsplit_rest. reflexivity. }
            apply (split_perm_eq (x :: y :: rest) (x :: l1') (y :: l2') Hsplit_full).
          - apply Permutation_app; apply IH. }
        { apply merge_perm. }
Qed.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Theorem mergesort_sorted : forall l,
  sorted (mergesort (length l) l).
Proof.
  intro l. apply mergesort_sorted_aux. reflexivity.
Qed.

Theorem mergesort_sorted_neg : ~ (forall l,
  sorted (mergesort (length l) l)).
Proof.
Admitted.

Theorem mergesort_perm : forall l,
  Permutation l (mergesort (length l) l).
Proof.
  intro l. apply mergesort_perm_aux.
Qed.

Theorem mergesort_perm_neg : ~ (forall l,
  Permutation l (mergesort (length l) l)).
Proof.
Admitted.
