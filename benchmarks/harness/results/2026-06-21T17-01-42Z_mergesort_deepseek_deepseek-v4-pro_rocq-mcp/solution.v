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

(** ** Helper lemmas *)

Lemma list_ind2 : forall (P : list nat -> Prop),
  P [] ->
  (forall x, P [x]) ->
  (forall x y l, P l -> P (x :: y :: l)) ->
  forall l, P l.
Proof.
  intros P H0 H1 H2.
  assert (forall n l, length l <= n -> P l) as H.
  { induction n as [|n IHn]; intros l Hlen.
    - destruct l; [exact H0 | simpl in Hlen; lia].
    - destruct l as [|x [|y rest]].
      + exact H0.
      + apply H1.
      + apply H2. apply IHn. simpl in Hlen. simpl. lia.
  }
  intros l. apply (H (length l)). lia.
Qed.

Lemma sorted_tl : forall a l, sorted (a :: l) -> sorted l.
Proof.
  intros a l Hs. inversion Hs; subst.
  - constructor.
  - assumption.
Qed.

Lemma sorted_head_le : forall a l, sorted (a :: l) -> forall x, In x l -> a <= x.
Proof.
  intros a l. revert a. induction l as [|b l' IH]; intros a Hs x Hin.
  - inversion Hin.
  - inversion Hs; subst.
    destruct Hin as [Heq | Hin].
    + subst. assumption.
    + apply Nat.le_trans with b.
      * assumption.
      * apply IH; assumption.
Qed.

Lemma sorted_cons_lb : forall a m,
  sorted m -> (forall z, In z m -> a <= z) -> sorted (a :: m).
Proof.
  intros a m Hs Hlb. destruct m as [|z rest].
  - constructor.
  - constructor.
    + apply Hlb. left. reflexivity.
    + assumption.
Qed.

Lemma merge_perm : forall l1 l2, Permutation (l1 ++ l2) (merge l1 l2).
Proof.
  induction l1 as [|x xs IHxs]; intros l2.
  - simpl. apply Permutation_refl.
  - induction l2 as [|y ys IHys].
    + simpl. rewrite app_nil_r. apply Permutation_refl.
    + simpl. destruct (x <=? y) eqn:E.
      * apply perm_skip. apply IHxs.
      * apply Permutation_trans with (x :: y :: xs ++ ys).
        -- apply perm_skip. apply Permutation_sym. apply Permutation_middle.
        -- apply Permutation_trans with (y :: x :: xs ++ ys).
           ++ apply perm_swap.
           ++ apply perm_skip. apply IHys.
Qed.

Lemma merge_lb : forall a l1 l2,
  (forall x, In x l1 -> a <= x) ->
  (forall x, In x l2 -> a <= x) ->
  forall x, In x (merge l1 l2) -> a <= x.
Proof.
  intros a l1 l2 H1 H2 x Hin.
  pose proof (merge_perm l1 l2) as Hp.
  apply Permutation_sym in Hp.
  apply (Permutation_in x Hp) in Hin.
  apply in_app_or in Hin.
  destruct Hin as [Hin | Hin]; [apply H1 | apply H2]; assumption.
Qed.

Lemma merge_sorted : forall l1 l2,
  sorted l1 -> sorted l2 -> sorted (merge l1 l2).
Proof.
  induction l1 as [|x xs IHxs]; intros l2 Hl1 Hl2.
  - simpl. exact Hl2.
  - revert Hl2. induction l2 as [|y ys IHys]; intros Hl2.
    + simpl. exact Hl1.
    + simpl. destruct (x <=? y) eqn:E.
      * apply Nat.leb_le in E.
        apply sorted_cons_lb.
        -- apply IHxs.
           ++ apply (sorted_tl x xs Hl1).
           ++ exact Hl2.
        -- apply merge_lb.
           ++ intros z Hz. apply (sorted_head_le x xs Hl1 z Hz).
           ++ intros z Hz. destruct Hz as [Heq | Hz].
              ** subst. exact E.
              ** apply Nat.le_trans with y.
                 --- exact E.
                 --- apply (sorted_head_le y ys Hl2 z Hz).
      * apply Nat.leb_gt in E.
        apply sorted_cons_lb.
        -- apply IHys. apply (sorted_tl y ys Hl2).
        -- apply (merge_lb y (x :: xs) ys).
           ++ intros z Hz. destruct Hz as [Heq | Hz].
              ** subst. apply Nat.lt_le_incl. exact E.
              ** apply Nat.le_trans with x.
                 --- apply Nat.lt_le_incl. exact E.
                 --- apply (sorted_head_le x xs Hl1 z Hz).
           ++ intros z Hz. apply (sorted_head_le y ys Hl2 z Hz).
Qed.

Lemma split_perm : forall l l1 l2,
  split l = (l1, l2) -> Permutation l (l1 ++ l2).
Proof.
  intro l. induction l as [| x | x y rest IH] using list_ind2; intros l1 l2 Hs.
  - simpl in Hs. inversion Hs; subst. simpl. apply perm_nil.
  - simpl in Hs. inversion Hs; subst. simpl. apply Permutation_refl.
  - simpl in Hs. destruct (split rest) as [a b] eqn:Hsr.
    inversion Hs; subst. simpl.
    apply perm_skip.
    specialize (IH a b eq_refl).
    apply Permutation_trans with (y :: a ++ b).
    + apply perm_skip. exact IH.
    + apply Permutation_middle.
Qed.

Lemma split_length : forall l l1 l2,
  split l = (l1, l2) -> length l1 <= length l /\ length l2 <= length l.
Proof.
  intro l. induction l as [| x | x y rest IH] using list_ind2; intros l1 l2 Hs.
  - simpl in Hs. inversion Hs; subst. simpl. split; lia.
  - simpl in Hs. inversion Hs; subst. simpl. split; lia.
  - simpl in Hs. destruct (split rest) as [a b] eqn:Hsr.
    inversion Hs; subst. simpl.
    specialize (IH a b eq_refl). destruct IH as [Ha Hb].
    split; lia.
Qed.

Lemma split_length_cons : forall a b rest l1 l2,
  split (a :: b :: rest) = (l1, l2) ->
  length l1 <= S (length rest) /\ length l2 <= S (length rest).
Proof.
  intros a b rest l1 l2 Hs. simpl in Hs.
  destruct (split rest) as [a' b'] eqn:Hr.
  inversion Hs; subst.
  pose proof (split_length rest a' b' Hr) as [Ha Hb].
  simpl. split; lia.
Qed.

Lemma mergesort_perm_gen : forall fuel l,
  length l <= fuel -> Permutation l (mergesort fuel l).
Proof.
  induction fuel as [|fuel' IH]; intros l Hlen.
  - assert (length l = 0) as Hl0 by lia.
    apply length_zero_iff_nil in Hl0. subst. simpl. apply perm_nil.
  - destruct l as [|a [|b rest]].
    + simpl. apply perm_nil.
    + simpl. apply Permutation_refl.
    + cbn [mergesort].
      destruct (split (a :: b :: rest)) as [l1 l2] eqn:Hsp.
      pose proof (split_perm _ _ _ Hsp) as Hperm.
      pose proof (split_length_cons _ _ _ _ _ Hsp) as [Hlen1 Hlen2].
      simpl in Hlen.
      assert (length l1 <= fuel') as Hf1 by lia.
      assert (length l2 <= fuel') as Hf2 by lia.
      apply Permutation_trans with (l1 ++ l2).
      * exact Hperm.
      * apply Permutation_trans with (mergesort fuel' l1 ++ mergesort fuel' l2).
        -- apply Permutation_app.
           ++ apply IH. exact Hf1.
           ++ apply IH. exact Hf2.
        -- apply merge_perm.
Qed.

Lemma mergesort_sorted_gen : forall fuel l,
  length l <= fuel -> sorted (mergesort fuel l).
Proof.
  induction fuel as [|fuel' IH]; intros l Hlen.
  - assert (length l = 0) as Hl0 by lia.
    apply length_zero_iff_nil in Hl0. subst. simpl. constructor.
  - destruct l as [|a [|b rest]].
    + simpl. constructor.
    + simpl. constructor.
    + cbn [mergesort].
      destruct (split (a :: b :: rest)) as [l1 l2] eqn:Hsp.
      pose proof (split_length_cons _ _ _ _ _ Hsp) as [Hlen1 Hlen2].
      simpl in Hlen.
      assert (length l1 <= fuel') as Hf1 by lia.
      assert (length l2 <= fuel') as Hf2 by lia.
      apply merge_sorted.
      * apply IH. exact Hf1.
      * apply IH. exact Hf2.
Qed.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Theorem mergesort_sorted : forall l,
  sorted (mergesort (length l) l).
Proof.
  intro l. apply mergesort_sorted_gen. lia.
Qed.

Theorem mergesort_sorted_neg : ~ (forall l,
  sorted (mergesort (length l) l)).
Proof.
Admitted.

Theorem mergesort_perm : forall l,
  Permutation l (mergesort (length l) l).
Proof.
  intro l. apply mergesort_perm_gen. lia.
Qed.

Theorem mergesort_perm_neg : ~ (forall l,
  Permutation l (mergesort (length l) l)).
Proof.
Admitted.
