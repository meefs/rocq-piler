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

(** ** Helper lemmas for sorted *)

Lemma sorted_inv_head : forall x y l, sorted (x :: y :: l) -> x <= y.
Proof. intros. inversion H; assumption. Qed.

Lemma sorted_inv_tail : forall x l, sorted (x :: l) -> sorted l.
Proof.
  intros x l H. inversion H; subst; [apply sorted_nil | assumption].
Qed.

Lemma sorted_cons_hd : forall x l, sorted l ->
  (l = [] \/ (exists h t, l = h :: t /\ x <= h)) ->
  sorted (x :: l).
Proof.
  intros x l Hl Hhd.
  destruct Hhd as [Hhd | [h [t [Heq Hle]]]].
  - subst. apply sorted_singleton.
  - subst. apply sorted_cons; assumption.
Qed.

(** ** merge preserves sortedness *)

Lemma merge_sorted_aux : forall n l1 l2,
  length l1 + length l2 <= n ->
  sorted l1 -> sorted l2 -> sorted (merge l1 l2).
Proof.
  induction n as [| n IH].
  - intros l1 l2 Hlen Hs1 Hs2.
    destruct l1; destruct l2; simpl in Hlen; try lia; simpl; apply sorted_nil.
  - intros l1 l2 Hlen Hs1 Hs2.
    destruct l1 as [| x xs].
    + simpl. exact Hs2.
    + destruct l2 as [| y ys].
      * simpl. exact Hs1.
      * simpl.
        destruct (x <=? y) eqn:Hxy.
        -- apply Nat.leb_le in Hxy.
           assert (Hxs : sorted xs) by (apply sorted_inv_tail with x; exact Hs1).
           assert (Hlen' : length xs + length (y :: ys) <= n) by (simpl in Hlen |- *; lia).
           pose proof (IH xs (y :: ys) Hlen' Hxs Hs2) as Hm.
           apply sorted_cons_hd; [exact Hm |].
           destruct xs as [| x' xs'].
           ++ right. exists y, ys. auto.
           ++ right. simpl.
              destruct (x' <=? y) eqn:Hx'y.
              ** exists x', (merge xs' (y :: ys)).
                 split; [reflexivity |]. apply sorted_inv_head with xs'; assumption.
              ** exists y, (merge (x' :: xs') ys).
                 split; [reflexivity | exact Hxy].
        -- apply Nat.leb_nle in Hxy.
           assert (Hyx : y <= x) by lia.
           assert (Hys : sorted ys) by (apply sorted_inv_tail with y; exact Hs2).
           assert (Hlen' : length (x :: xs) + length ys <= n) by (simpl in Hlen |- *; lia).
           pose proof (IH (x :: xs) ys Hlen' Hs1 Hys) as Hm.
           apply sorted_cons_hd; [exact Hm |].
           destruct ys as [| y' ys'].
           ++ right. exists x, xs. split; [reflexivity | exact Hyx].
           ++ right. simpl.
              destruct (x <=? y') eqn:Hxy'.
              ** exists x, (merge xs (y' :: ys')).
                 split; [reflexivity | exact Hyx].
              ** exists y', (merge (x :: xs) ys').
                 split; [reflexivity |]. apply sorted_inv_head with ys'; assumption.
Qed.

Lemma merge_sorted : forall l1 l2,
  sorted l1 -> sorted l2 -> sorted (merge l1 l2).
Proof.
  intros l1 l2 Hs1 Hs2.
  apply merge_sorted_aux with (n := length l1 + length l2); auto.
Qed.

(** ** Two-step induction principle for split *)

Lemma two_step_ind : forall P : list nat -> Prop,
  P [] -> (forall x, P [x]) ->
  (forall x y l, P l -> P (x :: y :: l)) ->
  forall l, P l.
Proof.
  intros P H0 H1 Hstep l.
  remember (length l) as n. revert l Heqn.
  induction n as [n IH] using lt_wf_ind.
  intros l Hn. destruct l as [| x [| y rest]].
  - exact H0.
  - exact (H1 x).
  - apply Hstep. apply IH with (length rest). simpl in Hn; lia. reflexivity.
Qed.

(** ** Properties of split *)

Lemma split_length : forall l,
  length (fst (split l)) + length (snd (split l)) = length l.
Proof.
  induction l as [| | x y rest IH] using two_step_ind.
  - simpl. lia.
  - simpl. lia.
  - simpl. destruct (split rest) as [r1 r2] eqn:Hr. simpl. simpl in IH. lia.
Qed.

Lemma split_shorter_l : forall l,
  2 <= length l ->
  length (fst (split l)) < length l.
Proof.
  induction l as [| | x y rest IH] using two_step_ind; intros Hlen.
  - simpl in Hlen. lia.
  - simpl in Hlen. lia.
  - simpl. destruct (split rest) as [r1 r2] eqn:Hr. simpl.
    pose proof (split_length rest) as Hsl. rewrite Hr in Hsl. simpl in Hsl. lia.
Qed.

Lemma split_shorter_r : forall l,
  2 <= length l ->
  length (snd (split l)) < length l.
Proof.
  induction l as [| | x y rest IH] using two_step_ind; intros Hlen.
  - simpl in Hlen. lia.
  - simpl in Hlen. lia.
  - simpl. destruct (split rest) as [r1 r2] eqn:Hr. simpl.
    pose proof (split_length rest) as Hsl. rewrite Hr in Hsl. simpl in Hsl. lia.
Qed.

Lemma split_perm : forall l,
  Permutation l (fst (split l) ++ snd (split l)).
Proof.
  induction l as [| | x y rest IH] using two_step_ind.
  - simpl. apply Permutation_refl.
  - simpl. apply Permutation_refl.
  - simpl. destruct (split rest) as [r1 r2] eqn:Hr. simpl in IH |- *.
    apply perm_skip.
    apply perm_trans with (y :: r1 ++ r2).
    + apply perm_skip. exact IH.
    + exact (Permutation_middle r1 r2 y).
Qed.

(** ** mergesort with sufficient fuel produces sorted output *)

Lemma mergesort_sorted_fuel : forall n l,
  length l <= n -> sorted (mergesort n l).
Proof.
  induction n as [| n IH]; intros l Hlen.
  - destruct l; simpl in Hlen; try lia. apply sorted_nil.
  - destruct l as [| x [| y rest]].
    + simpl. apply sorted_nil.
    + simpl. apply sorted_singleton.
    + simpl.
      destruct (split rest) as [r1 r2] eqn:Hr.
      apply merge_sorted.
      * apply IH.
        simpl in Hlen.
        pose proof (split_shorter_l (x :: y :: rest)) as Hsl.
        simpl in Hsl. rewrite Hr in Hsl. simpl in Hsl.
        assert (S (length r1) < S (S (length rest))) by (apply Hsl; lia).
        simpl. lia.
      * apply IH.
        simpl in Hlen.
        pose proof (split_shorter_r (x :: y :: rest)) as Hsl.
        simpl in Hsl. rewrite Hr in Hsl. simpl in Hsl.
        assert (S (length r2) < S (S (length rest))) by (apply Hsl; lia).
        simpl. lia.
Qed.

(** ** merge is a permutation of l1 ++ l2 *)

Lemma merge_inner_eq : forall x xs ys,
  (fix merge_inner (l2 : list nat) : list nat :=
    match l2 with
    | [] => x :: xs
    | y :: ys0 => if x <=? y then x :: merge xs l2 else y :: merge_inner ys0
    end) ys = merge (x :: xs) ys.
Proof.
  intros x xs ys. revert x xs.
  induction ys as [| y ys IH]; intros x xs.
  - simpl. reflexivity.
  - simpl. destruct (x <=? y); [reflexivity |]. rewrite IH. reflexivity.
Qed.

Lemma merge_perm_aux : forall n l1 l2,
  length l1 + length l2 <= n ->
  Permutation (l1 ++ l2) (merge l1 l2).
Proof.
  induction n as [| n IH]; intros l1 l2 Hlen.
  - destruct l1; destruct l2; simpl in Hlen; try lia; apply Permutation_refl.
  - destruct l1 as [| x xs].
    + simpl. apply Permutation_refl.
    + destruct l2 as [| y ys].
      * rewrite app_nil_r. simpl. apply Permutation_refl.
      * simpl.
        destruct (x <=? y) eqn:Hxy.
        -- apply perm_skip. apply IH. simpl in Hlen |- *. lia.
        -- rewrite merge_inner_eq.
           assert (Hlen' : length (x :: xs) + length ys <= n) by (simpl in Hlen |- *; lia).
           pose proof (IH (x :: xs) ys Hlen') as IHperm.
           apply perm_trans with (y :: (x :: xs) ++ ys).
           ++ apply perm_trans with (x :: y :: xs ++ ys).
              ** apply perm_skip. apply Permutation_sym.
                 apply Permutation_cons_app. apply Permutation_refl.
              ** apply perm_swap.
           ++ apply perm_skip. simpl. exact IHperm.
Qed.

Lemma merge_perm : forall l1 l2,
  Permutation (l1 ++ l2) (merge l1 l2).
Proof.
  intros. apply merge_perm_aux with (length l1 + length l2). lia.
Qed.

(** ** mergesort with sufficient fuel is a permutation *)

Lemma mergesort_perm_fuel : forall n l,
  length l <= n -> Permutation l (mergesort n l).
Proof.
  induction n as [| n IH]; intros l Hlen.
  - destruct l; simpl in Hlen; try lia. apply Permutation_refl.
  - destruct l as [| x [| y rest]].
    + simpl. apply Permutation_refl.
    + simpl. apply Permutation_refl.
    + simpl.
      destruct (split rest) as [r1 r2] eqn:Hr.
      assert (Hn1 : length (x :: r1) <= n). {
        simpl in Hlen.
        pose proof (split_shorter_l (x :: y :: rest)) as Hsl.
        simpl in Hsl. rewrite Hr in Hsl. simpl in Hsl.
        assert (S (length r1) < S (S (length rest))) by (apply Hsl; lia).
        simpl. lia.
      }
      assert (Hn2 : length (y :: r2) <= n). {
        simpl in Hlen.
        pose proof (split_shorter_r (x :: y :: rest)) as Hsl.
        simpl in Hsl. rewrite Hr in Hsl. simpl in Hsl.
        assert (S (length r2) < S (S (length rest))) by (apply Hsl; lia).
        simpl. lia.
      }
      pose proof (IH (x :: r1) Hn1) as Hp1.
      pose proof (IH (y :: r2) Hn2) as Hp2.
      apply perm_trans with ((x :: r1) ++ (y :: r2)).
      * pose proof (split_perm (x :: y :: rest)) as Hsp.
        simpl in Hsp. rewrite Hr in Hsp. simpl in Hsp. exact Hsp.
      * apply perm_trans with (mergesort n (x :: r1) ++ mergesort n (y :: r2)).
        -- apply Permutation_app; assumption.
        -- apply merge_perm.
Qed.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Theorem mergesort_sorted : forall l,
  sorted (mergesort (length l) l).
Proof.
  intros l. apply mergesort_sorted_fuel. lia.
Qed.

Theorem mergesort_sorted_neg : ~ (forall l,
  sorted (mergesort (length l) l)).
Proof.
Admitted.

Theorem mergesort_perm : forall l,
  Permutation l (mergesort (length l) l).
Proof.
  intros l. apply mergesort_perm_fuel. lia.
Qed.

Theorem mergesort_perm_neg : ~ (forall l,
  Permutation l (mergesort (length l) l)).
Proof.
Admitted.
