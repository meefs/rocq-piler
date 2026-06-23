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

(** ** Helper Lemmas *)

Lemma sorted_inv_cons : forall x xs,
  sorted (x :: xs) -> sorted xs.
Proof.
  intros x xs Hs.
  inversion Hs as [Hnil|Hsingleton| x' y l Hle Hrest]; subst.
  - apply sorted_nil.
  - exact Hrest.
Qed.

Lemma sorted_head_le : forall x xs,
  sorted (x :: xs) -> forall y, In y xs -> x <= y.
Proof.
  intros x xs Hs y0 Hin.
  revert x Hs y0 Hin.
  induction xs as [|a xs' IH]; intros x Hs y0 Hin.
  - inversion Hin.
  - inversion Hs as [| | x' b l Hle Hs']; subst.
    simpl in Hin. destruct Hin as [Hin|Hin].
    + subst y0. exact Hle.
    + eapply Nat.le_trans.
      * exact Hle.
      * apply (IH a Hs' y0 Hin).
Qed.

Lemma In_merge : forall l1 l2 z,
  In z (merge l1 l2) -> In z l1 \/ In z l2.
Proof.
  induction l1 as [|x xs IH]; simpl; intros l2 z Hin.
  - right; auto.
  - induction l2 as [|y ys IHinner]; simpl in *.
    + destruct Hin as [H|H].
      * left; left; auto.
      * left; right; auto.
    + destruct (x <=? y) eqn:Hcmp; simpl in Hin.
      * destruct Hin as [H|H].
        -- left; left; auto.
        -- apply (IH (y :: ys) z) in H.
           destruct H as [H|H].
           ++ left; right; auto.
           ++ right; auto.
      * destruct Hin as [H|H].
        -- right; left; auto.
        -- apply IHinner in H.
           destruct H as [H|H].
           ++ left; auto.
           ++ right; right; auto.
Qed.

Lemma In_merge_inner : forall x xs l2 z,
  In z ((fix merge_inner (l2 : list nat) : list nat :=
          match l2 with
          | [] => x :: xs
          | y :: ys => if x <=? y then x :: merge xs l2 else y :: merge_inner ys
          end) l2) ->
  In z (x :: xs) \/ In z l2.
Proof.
  induction l2 as [|y ys IH]; intros z; simpl.
  - left. auto.
  - destruct (x <=? y) eqn:Hcmp; simpl.
    { intros [H|H].
      - left; simpl; auto.
      - apply In_merge with (z := z) in H.
        destruct H as [H|H].
        + left; right; auto.
        + right; auto. }
    { intros [H|H].
      - right; left; auto.
      - apply IH in H.
        destruct H as [H|H].
        + left; auto.
        + right; right; auto. }
Qed.

Lemma merge_sorted : forall l1 l2, sorted l1 -> sorted l2 -> sorted (merge l1 l2).
Proof.
  induction l1 as [|x xs IH]; simpl; intros l2 Hs1 Hs2.
  - exact Hs2.
  - revert Hs2.
    induction l2 as [|y ys IHinner]; intros Hs2.
    + simpl. exact Hs1.
    + cbn in |- *.
      destruct (x <=? y) eqn:Hcmp.
      * apply Nat.leb_le in Hcmp.
        destruct (merge xs (y :: ys)) as [|h t] eqn:Heqm.
        -- apply sorted_singleton.
        -- assert (Hm : sorted (h :: t)).
           { rewrite <- Heqm. apply IH.
             - apply sorted_inv_cons with x; auto.
             - auto. }
           assert (Hin_h : In h (merge xs (y :: ys))).
           { rewrite Heqm; simpl; auto. }
           apply In_merge in Hin_h.
           apply sorted_cons with (x := x) (y := h) (l := t).
           ++ destruct Hin_h as [Hin_h|Hin_h].
              ** eapply sorted_head_le; eauto.
              ** simpl in Hin_h; destruct Hin_h as [Hin_h|Hin_h].
                 --- subst h; exact Hcmp.
                 --- eapply Nat.le_trans; [exact Hcmp|].
                     eapply sorted_head_le; eauto.
           ++ exact Hm.
      * apply Nat.leb_gt in Hcmp.
        remember ((fix merge_inner (l2 : list nat) : list nat :=
                    match l2 with
                    | [] => x :: xs
                    | y0 :: ys0 => if x <=? y0 then x :: merge xs l2 else y0 :: merge_inner ys0
                    end) ys) as m.
        assert (Hm_sorted : sorted m).
        { subst m. apply IHinner.
          apply sorted_inv_cons with y; auto. }
        destruct m as [|h t].
        -- apply sorted_singleton.
        -- assert (Hin_h : In h ((fix merge_inner (l2 : list nat) : list nat :=
                                   match l2 with
                                   | [] => x :: xs
                                   | y0 :: ys0 => if x <=? y0 then x :: merge xs l2 else y0 :: merge_inner ys0
                                   end) ys)).
           { rewrite <- Heqm; simpl; auto. }
           apply In_merge_inner in Hin_h.
           apply sorted_cons with (x := y) (y := h) (l := t).
           ++ destruct Hin_h as [Hin_h|Hin_h].
              ** simpl in Hin_h; destruct Hin_h as [Hin_h|Hin_h].
                 --- subst h; apply Nat.lt_le_incl; exact Hcmp.
                 --- eapply Nat.le_trans; [apply Nat.lt_le_incl; exact Hcmp|].
                     eapply sorted_head_le; eauto.
              ** eapply sorted_head_le; eauto.
           ++ exact Hm_sorted.
Qed.

Lemma split_length_eq : forall l,
  length (fst (split l)) + length (snd (split l)) = length l.
Proof.
  fix IH 1.
  intros l.
  destruct l as [|x xs]; simpl; auto.
  destruct xs as [|y ys].
  - simpl; auto.
  - destruct (split ys) as [l1 l2] eqn:H.
    simpl.
    ring_simplify.
    pose proof (f_equal fst H) as H1.
    pose proof (f_equal snd H) as H2.
    simpl in H1, H2.
    specialize (IH ys).
    rewrite H1, H2 in IH.
    apply (Nat.add_cancel_r _ _ 2).
    apply IH.
Qed.

Lemma split_length_lt_fst : forall l,
  2 <= length l ->
  length (fst (split l)) < length l.
Proof.
  intros l H.
  destruct l as [|x xs]; simpl in *.
  - lia.
  - destruct xs as [|y ys]; simpl in *.
    + lia.
    + destruct (split ys) as [l1 l2] eqn:Heq.
      simpl.
      assert (Hlen := split_length_eq ys).
      rewrite Heq in Hlen. simpl in Hlen.
      assert (Hle : length l1 <= length ys).
      { rewrite <- Hlen. apply Nat.le_add_r. }
      exact (proj1 (Nat.succ_le_mono (S (length l1)) (S (length ys)))
                   (proj1 (Nat.succ_le_mono (length l1) (length ys)) Hle)).
Qed.

Lemma split_length_lt_snd : forall l,
  2 <= length l ->
  length (snd (split l)) < length l.
Proof.
  intros l H.
  destruct l as [|x xs]; simpl in *.
  - lia.
  - destruct xs as [|y ys]; simpl in *.
    + lia.
    + destruct (split ys) as [l1 l2] eqn:Heq.
      simpl.
      assert (Hlen := split_length_eq ys).
      rewrite Heq in Hlen. simpl in Hlen.
      assert (Hle : length l2 <= length ys).
      { rewrite <- Hlen. apply Nat.le_add_l. }
      exact (proj1 (Nat.succ_le_mono (S (length l2)) (S (length ys)))
                   (proj1 (Nat.succ_le_mono (length l2) (length ys)) Hle)).
Qed.

Lemma mergesort_sorted_aux : forall k l, length l <= k -> sorted (mergesort k l).
Proof.
  induction k as [|k IH]; intros l Hlen; simpl.
  - assert (l = []) by (destruct l; simpl in *; auto; lia).
    subst; apply sorted_nil.
  - destruct l as [|x l]; simpl.
    + apply sorted_nil.
    + destruct l as [|y l].
      * simpl. apply sorted_singleton.
      * simpl.
        destruct (split l) as [l1 l2] eqn:Hs.
        simpl.
        apply merge_sorted.
         -- apply IH.
            pose proof (split_length_lt_fst (x :: y :: l)) as Hlt.
            simpl in Hlt. rewrite Hs in Hlt. simpl in Hlt.
            assert (H2 : 2 <= length (x :: y :: l)) by (simpl; lia).
            apply Hlt in H2.
            simpl.
            simpl in Hlen.
            pose proof (Nat.lt_le_trans (S (length l1)) (S (S (length l))) (S k) H2 Hlen) as H3.
            apply <- Nat.succ_le_mono in H3. exact H3.
         -- apply IH.
            pose proof (split_length_lt_snd (x :: y :: l)) as Hlt.
            simpl in Hlt. rewrite Hs in Hlt. simpl in Hlt.
            assert (H2 : 2 <= length (x :: y :: l)) by (simpl; lia).
            apply Hlt in H2.
            simpl.
            simpl in Hlen.
            pose proof (Nat.lt_le_trans (S (length l2)) (S (S (length l))) (S k) H2 Hlen) as H3.
            apply <- Nat.succ_le_mono in H3. exact H3.
Qed.

Lemma merge_perm : forall l1 l2, Permutation (l1 ++ l2) (merge l1 l2).
Proof.
  induction l1 as [|x xs IH]; intros l2; simpl.
  - apply Permutation_refl.
  - revert x xs IH.
    induction l2 as [|y ys IHinner]; intros x xs IH; simpl.
    + rewrite app_nil_r. apply Permutation_refl.
    + destruct (x <=? y) eqn:Hcmp.
      * apply perm_skip. apply IH.
      * etransitivity.
        -- apply (Permutation_app_comm (x :: xs) (y :: ys)).
        -- cbn [app].
           apply perm_skip.
           etransitivity.
           ++ apply Permutation_app_comm.
           ++ apply (IHinner x xs IH).
Qed.

Lemma split_perm : forall l,
  Permutation l ((fst (split l)) ++ (snd (split l))).
Proof.
  fix IH 1.
  intros l.
  destruct l as [|x xs].
  - simpl. apply Permutation_refl.
  - destruct xs as [|y ys].
    + simpl. apply Permutation_refl.
    + simpl (split (x :: y :: ys)).
      destruct (split ys) as [l1 l2] eqn:Hs; simpl.
      apply perm_skip.
      eapply Permutation_trans.
      * apply perm_skip.
        eapply Permutation_trans.
        --         pose proof (IH ys) as IHys.
        rewrite Hs in IHys; simpl in IHys.
        exact IHys.
        -- apply (Permutation_app_comm l1 l2).
      * simpl.
        apply Permutation_sym.
        apply Permutation_app_comm.
Qed.

Lemma mergesort_perm_aux : forall k l, length l <= k -> Permutation l (mergesort k l).
Proof.
  induction k as [|k IH]; intros l Hlen; simpl.
  - assert (l = []) by (destruct l; simpl in *; auto; lia).
    subst; apply Permutation_refl.
  - destruct l as [|x l]; simpl.
    + apply Permutation_refl.
    + destruct l as [|y l].
      * simpl. apply Permutation_refl.
      * simpl.
        destruct (split l) as [l1 l2] eqn:Hs.
        simpl.
        eapply Permutation_trans.
        -- apply split_perm.
        -- simpl. rewrite Hs; cbn [fst snd].
           eapply Permutation_trans.
           ++ apply Permutation_app.
              ** apply IH.
                 pose proof (split_length_lt_fst (x :: y :: l)) as Hlt.
                 simpl in Hlt. rewrite Hs in Hlt. simpl in Hlt.
                 assert (H2 : 2 <= length (x :: y :: l)) by (simpl; lia).
                 apply Hlt in H2.
                 simpl.
                 simpl in Hlen.
                 pose proof (Nat.lt_le_trans (S (length l1)) (S (S (length l))) (S k) H2 Hlen) as H3.
                 apply <- Nat.succ_le_mono in H3. exact H3.
              ** apply IH.
                 pose proof (split_length_lt_snd (x :: y :: l)) as Hlt.
                 simpl in Hlt. rewrite Hs in Hlt. simpl in Hlt.
                 assert (H2 : 2 <= length (x :: y :: l)) by (simpl; lia).
                 apply Hlt in H2.
                 simpl.
                 simpl in Hlen.
                 pose proof (Nat.lt_le_trans (S (length l2)) (S (S (length l))) (S k) H2 Hlen) as H3.
                 apply <- Nat.succ_le_mono in H3. exact H3.
           ++ apply merge_perm.
Qed.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Theorem mergesort_sorted : forall l,
  sorted (mergesort (length l) l).
Proof.
  intros l. apply mergesort_sorted_aux with (k := length l). lia.
Qed.

Theorem mergesort_sorted_neg : ~ (forall l,
  sorted (mergesort (length l) l)).
Proof.
Admitted.

Theorem mergesort_perm : forall l,
  Permutation l (mergesort (length l) l).
Proof.
  intros l. apply mergesort_perm_aux with (k := length l). lia.
Qed.

Theorem mergesort_perm_neg : ~ (forall l,
  Permutation l (mergesort (length l) l)).
Proof.
Admitted.
