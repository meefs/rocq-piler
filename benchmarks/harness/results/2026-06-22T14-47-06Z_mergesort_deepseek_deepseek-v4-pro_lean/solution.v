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

(** ** Helper lemmas about sorted *)

Lemma sorted_skip : forall x l,
  sorted (x :: l) -> sorted l.
Proof.
  intros x l H. inversion H; subst; [constructor|assumption].
Qed.

Lemma sorted_head_le : forall x l z,
  sorted (x :: l) -> In z (x :: l) -> x <= z.
Proof.
  intros x l z Hsorted Hin.
  remember (x :: l) as l'.
  revert x l z Hin Heql'.
  induction Hsorted as [|a|a b l1 Hle Hsorted']; intros x0 l0 z0 Hin Heq.
  - discriminate.
  - injection Heq; clear Heq; intros; subst.
    destruct Hin; subst; [lia|inversion H].
  - injection Heq; clear Heq; intros; subst.
    destruct Hin; subst; [lia|].
    rename H into Hin_tl.
    pose proof (IHHsorted' b l1 z0 Hin_tl eq_refl).
    lia.
Qed.

Lemma sorted_tail_ge_head : forall x l z,
  sorted (x :: l) -> In z l -> x <= z.
Proof.
  intros x l z Hsorted Hin.
  apply sorted_head_le with (z := z) in Hsorted.
  - exact Hsorted.
  - right; exact Hin.
Qed.

Lemma sorted_cons_min : forall y l,
  sorted l -> (forall z, In z l -> y <= z) -> sorted (y :: l).
Proof.
  intros y l Hsort Hall.
  remember l as l' eqn:Heq.
  destruct l' as [|x l0].
  - subst. constructor.
  - subst. apply (sorted_cons y x l0).
    + apply Hall. left; reflexivity.
    + exact Hsort.
Qed.

(** ** Lemmas about merge (proved while merge is transparent) *)

Lemma merge_inner_eq : forall x xs ys,
  (fix merge_inner (l2 : list nat) : list nat :=
     match l2 with
     | [] => x :: xs
     | y :: ys' =>
       if x <=? y then x :: merge xs l2
       else y :: merge_inner ys'
     end) ys = merge (x :: xs) ys.
Proof.
  intros x xs ys. revert x xs.
  induction ys as [|y ys IH]; intros x xs; simpl; auto.
Qed.

Lemma merge_cons_eq : forall x xs l,
  merge (x :: xs) l =
  match l with
  | [] => x :: xs
  | y :: ys =>
    if x <=? y then x :: merge xs (y :: ys)
    else y :: merge (x :: xs) ys
  end.
Proof.
  intros x xs l. simpl. destruct l; reflexivity.
Qed.

(** After proving merge_cons_eq, we make merge opaque to prevent
    unwanted reduction of [merge (x::xs) l2] into its inner fix. *)

Opaque merge.

Lemma merge_elements_ge : forall n l1 l2 b,
  (length l1 + length l2 <= n)%nat ->
  sorted l1 -> sorted l2 ->
  (forall z, In z l1 -> b <= z) ->
  (forall z, In z l2 -> b <= z) ->
  forall z, In z (merge l1 l2) -> b <= z.
Proof.
  induction n; intros l1 l2 b Hlen Hs1 Hs2 Hall1 Hall2 z Hin.
  - destruct l1; simpl in Hlen.
    + destruct l2; simpl in Hlen.
      * simpl in Hin. inversion Hin.
      * exfalso. apply Nat.nle_succ_0 in Hlen. exact Hlen.
    + exfalso. simpl in Hlen. inversion Hlen.
  - destruct l1 as [|x xs].
    + simpl in Hin. apply Hall2. exact Hin.
    + rewrite merge_cons_eq in Hin.
      destruct l2 as [|y ys].
      * simpl in Hin. apply Hall1. exact Hin.
      * simpl in Hin.
        destruct (x <=? y) eqn:Hle in Hin.
        -- destruct Hin as [Hin'|Hin'].
           ++ subst. apply Hall1. left; reflexivity.
           ++ apply (IHn xs (y :: ys) b).
              { simpl. simpl in Hlen. lia. }
              { inversion Hs1; subst; [constructor|assumption]. }
              { exact Hs2. }
              { intros z' Hz'. apply Hall1. right. exact Hz'. }
              { exact Hall2. }
              exact Hin'.
        -- destruct Hin as [Hin'|Hin'].
           ++ subst. apply Hall2. left; reflexivity.
           ++ apply (IHn (x :: xs) ys b).
              { simpl. simpl in Hlen. lia. }
              { exact Hs1. }
              { inversion Hs2; subst; [constructor|assumption]. }
              { exact Hall1. }
              { intros z' Hz'. apply Hall2. right. exact Hz'. }
              exact Hin'.
Qed.

Lemma merge_sorted : forall l1 l2, sorted l1 -> sorted l2 -> sorted (merge l1 l2).
Proof.
  cut (forall n l1 l2, (length l1 + length l2 <= n)%nat ->
    sorted l1 -> sorted l2 -> sorted (merge l1 l2)).
  { intros H l1 l2 Hs1 Hs2.
    apply H with (n := length l1 + length l2). simpl. lia. exact Hs1. exact Hs2. }
  induction n; intros l1 l2 Hlen Hs1 Hs2.
  - destruct l1; simpl in Hlen.
    + simpl. exact Hs2.
    + exfalso. simpl in Hlen. inversion Hlen.
  - destruct l1 as [|x xs].
    + simpl. exact Hs2.
    + rewrite merge_cons_eq.
      destruct l2 as [|y ys].
      * simpl. exact Hs1.
      * simpl.
        destruct (x <=? y) eqn:Hle.
        -- apply Nat.leb_le in Hle.
           apply sorted_cons_min with (y := x).
           { apply IHn.
             { simpl. simpl in Hlen. lia. }
             { apply sorted_skip with x. exact Hs1. }
             { exact Hs2. } }
           { apply merge_elements_ge with (n := length xs + length (y :: ys)).
             { simpl. simpl in Hlen. lia. }
             { apply sorted_skip with x. exact Hs1. }
             { exact Hs2. }
             { intros z Hz. apply (sorted_tail_ge_head x xs z Hs1 Hz). }
             { intros z Hz.
               destruct Hz as [Hz'|Hz']; subst.
               - exact Hle.
               - pose proof (sorted_tail_ge_head y ys z Hs2 Hz').
                 lia. } }
        -- apply Nat.leb_gt in Hle.
           remember (merge (x :: xs) ys) as m eqn:Hm.
           assert (Hm_sorted : sorted m).
           { subst m.
             assert (Hlen' : (length (x :: xs) + length ys <= n)%nat)
               by (simpl in Hlen; simpl; lia).
             apply (IHn (x :: xs) ys Hlen' Hs1 (sorted_skip y ys Hs2)). }
           assert (Hall_m : forall z, In z m -> y <= z).
           { subst m. intros z Hz.
             apply (merge_elements_ge (length (x :: xs) + length ys) (x :: xs) ys y).
             - simpl. lia.
             - exact Hs1.
             - apply sorted_skip with y. exact Hs2.
              - intros z' Hz'. pose proof (sorted_head_le x xs z' Hs1 Hz'). lia.
             - intros z' Hz'. apply (sorted_tail_ge_head y ys z' Hs2 Hz').
             - exact Hz. }
           apply sorted_cons_min with (y := y).
           { exact Hm_sorted. }
           { exact Hall_m. }
Qed.

Transparent merge.

Lemma split_length : forall l l1 l2,
  split l = (l1, l2) ->
  (length l1 <= length l /\ length l2 <= length l)%nat.
Proof.
  fix IH 1.
  intros l l1 l2 H.
  destruct l as [|x l'].
  - inversion H; simpl; auto.
  - destruct l' as [|y l''].
    + inversion H; simpl; auto.
    + simpl in H.
      destruct (split l'') as [l1' l2'] eqn:Hsplit.
      inversion H; subst; clear H.
      destruct (IH l'' l1' l2' Hsplit) as [H1 H2].
      simpl. split; lia.
Qed.

Lemma perm_y_cons_l1_l2 : forall y l1 l2,
  Permutation (A := nat) (y :: (l1 ++ l2)) (l1 ++ y :: l2).
Proof.
  intros y l1 l2.
  induction l1 as [|a l1 IH].
  - simpl. apply Permutation_refl.
  - simpl.
    apply Permutation_trans with (a :: y :: (l1 ++ l2)).
    { apply perm_swap. }
    apply perm_skip. apply IH.
Qed.

Lemma split_perm : forall l l1 l2,
  split l = (l1, l2) ->
  Permutation l (l1 ++ l2).
Proof.
  fix IH 1.
  intros l l1 l2 H.
  destruct l as [|x l'].
  - inversion H; subst; apply Permutation_refl.
  - destruct l' as [|y l''].
    + inversion H; subst; apply Permutation_refl.
    + simpl in H.
      destruct (split l'') as [l1' l2'] eqn:Hsplit.
      inversion H; subst; clear H.
      simpl.
      apply Permutation_trans with (x :: y :: (l1' ++ l2')).
      { apply perm_skip. apply perm_skip. apply (IH l'' l1' l2' Hsplit). }
      simpl.
      apply perm_skip.
      apply perm_y_cons_l1_l2.
Qed.

Lemma merge_perm_aux : forall n l1 l2,
  (length l1 + length l2 <= n)%nat ->
  Permutation (l1 ++ l2) (merge l1 l2).
Proof.
  induction n; intros l1 l2 Hlen.
  - destruct l1; simpl in Hlen.
    + simpl. apply Permutation_refl.
    + exfalso. simpl in Hlen. inversion Hlen.
  - destruct l1 as [|x xs].
    + simpl. apply Permutation_refl.
    + rewrite merge_cons_eq.
      destruct l2 as [|y ys].
      * simpl. rewrite (app_nil_r xs). apply Permutation_refl.
       * simpl.
         destruct (x <=? y) eqn:Hle.
         -- simpl.
            apply perm_skip.
            apply IHn.
            { simpl in Hlen. simpl. lia. }
         -- simpl.
            apply Permutation_trans with (y :: (x :: xs) ++ ys).
            { change (x :: xs ++ y :: ys) with ((x :: xs) ++ (y :: ys)).
              apply Permutation_trans with ((y :: ys) ++ (x :: xs)).
              - apply Permutation_app_comm.
              - apply perm_skip. apply Permutation_app_comm. }
            apply perm_skip.
            apply IHn.
            { simpl in Hlen. simpl. lia. }
Qed.

Lemma merge_perm : forall l1 l2,
  Permutation (l1 ++ l2) (merge l1 l2).
Proof.
  intros l1 l2.
  apply merge_perm_aux with (n := length l1 + length l2). lia.
Qed.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Theorem mergesort_sorted : forall l,
  sorted (mergesort (length l) l).
Proof.
  cut (forall n l, length l <= n -> sorted (mergesort n l)).
  { intros H l. apply H with (n := length l). lia. }
  induction n as [|n' IH]; intros l Hlen.
  - destruct l; [simpl; constructor 1| exfalso; simpl in Hlen; inversion Hlen].
  - destruct l as [|x [|y l']].
    + simpl. constructor.
    + simpl. constructor.
    + simpl mergesort.
      destruct (split l') as [l1' l2'] eqn:Hsplit'.
      simpl.
      apply merge_sorted.
      * apply IH.
        assert (H := split_length l' l1' l2' Hsplit').
        destruct H as [H1 H2].
        simpl. simpl in Hlen. lia.
      * apply IH.
        assert (H := split_length l' l1' l2' Hsplit').
        destruct H as [H1 H2].
        simpl. simpl in Hlen. lia.
Qed.

Theorem mergesort_sorted_neg : ~ (forall l,
  sorted (mergesort (length l) l)).
Proof.
Admitted.

Theorem mergesort_perm : forall l,
  Permutation l (mergesort (length l) l).
Proof.
  cut (forall n l, length l <= n ->
    Permutation l (mergesort n l)).
  { intros H l. apply H with (n := length l). lia. }
  induction n as [|n' IH]; intros l Hge.
  - destruct l; [simpl; apply Permutation_refl| exfalso; simpl in Hge; inversion Hge].
  - destruct l as [|x [|y l']].
    + simpl. apply Permutation_refl.
    + simpl. apply Permutation_refl.
    + simpl mergesort.
      destruct (split l') as [l1' l2'] eqn:Hsplit'.
      simpl.
      apply Permutation_trans with ((x :: l1') ++ (y :: l2')).
      { apply (split_perm (x :: y :: l') (x :: l1') (y :: l2')).
        simpl. rewrite Hsplit'. reflexivity. }
      apply Permutation_trans with (mergesort n' (x :: l1') ++ mergesort n' (y :: l2')).
      { apply Permutation_app; apply IH; 
        [assert (H := split_length l' l1' l2' Hsplit'); destruct H; simpl; simpl in Hge; lia
        |assert (H := split_length l' l1' l2' Hsplit'); destruct H; simpl; simpl in Hge; lia]. }
      apply merge_perm.
Qed.

Theorem mergesort_perm_neg : ~ (forall l,
  Permutation l (mergesort (length l) l)).
Proof.
Admitted.
