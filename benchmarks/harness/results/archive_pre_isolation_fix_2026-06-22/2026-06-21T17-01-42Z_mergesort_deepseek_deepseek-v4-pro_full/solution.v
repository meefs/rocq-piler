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

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

(** *** Helper lemmas *)

Lemma sorted_tail : forall a l, sorted (a :: l) -> sorted l.
Proof.
  intros a l H. inversion H; subst; [constructor | assumption].
Qed.

Lemma sorted_In_le : forall a l, sorted (a :: l) -> forall b, In b l -> a <= b.
Proof.
  intros a l Hsort. remember (a :: l) as al eqn:Heq.
  revert a l Heq. induction Hsort; intros a0 l0 Heq b Hin.
  - inversion Heq.
  - inversion Heq; subst. inversion Hin.
  - inversion Heq; subst.
    destruct Hin as [Hb|Hin'].
    + subst. exact H.
    + pose proof (IHHsort y l eq_refl b Hin') as Hyb.
      apply (Nat.le_trans _ y _ H Hyb).
Qed.

Lemma sorted_cons_all_le : forall a l, sorted l -> (forall x, In x l -> a <= x) -> sorted (a :: l).
Proof.
  intros a l Hsort Hle. induction Hsort as [|x|x0 y l0 Hle0 Hsort0 IH].
  - apply sorted_singleton.
  - apply sorted_cons with (y := x).
    + apply Hle. left; reflexivity.
    + constructor.
  - apply sorted_cons with (y := x0).
    + apply Hle. left; reflexivity.
    + apply sorted_cons with (y := y).
      * exact Hle0.
      * exact Hsort0.
Qed.

Lemma merge_In : forall l1 l2 x, In x (merge l1 l2) -> In x l1 \/ In x l2.
Proof.
  induction l1 as [|a l1 IH]; simpl; intros l2 x Hin.
  - auto.
  - induction l2 as [|b l2 IH2]; simpl in *.
    + auto.
    + destruct (a <=? b); simpl in Hin.
      * destruct Hin as [Hx|Hin'].
        -- auto.
        -- destruct (IH (b :: l2) x Hin') as [Hin1|Hin2]; auto.
      * destruct Hin as [Hx|Hin'].
        -- auto.
        -- destruct (IH2 Hin') as [Hin1|Hin2]; auto.
Qed.

Lemma merge_sorted : forall l1 l2, sorted l1 -> sorted l2 -> sorted (merge l1 l2).
Proof.
  induction l1 as [|a l1 IH]; intros l2 Hs1 Hs2; simpl.
  - exact Hs2.
  - induction l2 as [|b l2 IH2]; simpl.
    + exact Hs1.
    + simpl. destruct (a <=? b) eqn:Heq.
      * apply Nat.leb_le in Heq.
        apply sorted_cons_all_le.
        -- apply IH.
           ++ apply (sorted_tail a). exact Hs1.
           ++ exact Hs2.
        -- intros x Hx. apply merge_In in Hx. destruct Hx as [Hx1|Hx2].
           ++ apply (sorted_In_le _ _ Hs1). exact Hx1.
           ++ destruct Hx2 as [Hx2|Hx2].
              ** subst. exact Heq.
               ** apply (sorted_In_le _ _ Hs2) in Hx2.
                 apply (Nat.le_trans _ b _ Heq Hx2).
      * apply Nat.leb_nle in Heq.
        apply sorted_cons_all_le.
        -- apply IH2. apply (sorted_tail b). exact Hs2.
        -- intros x Hx. pose proof (merge_In (a :: l1) l2 x Hx) as [Hx1|Hx2].
           ++ destruct Hx1 as [Hx1|Hx1].
              ** subst. lia.
              ** apply (sorted_In_le _ _ Hs1) in Hx1. lia.
           ++ apply (sorted_In_le _ _ Hs2). exact Hx2.
Qed.

Lemma split_length_bound : forall l l1 l2, split l = (l1, l2) ->
  length l1 <= length l /\ length l2 <= length l.
Proof.
  fix FIX 1.
  intros l l1 l2 Hsplit.
  destruct l as [|a l].
  - simpl in Hsplit. inversion Hsplit; subst; simpl; auto.
  - destruct l as [|b l].
    + simpl in Hsplit. inversion Hsplit; subst; simpl; auto.
    + simpl in Hsplit.
      destruct (split l) as [l1' l2'] eqn:Heq.
      inversion Hsplit; subst; clear Hsplit.
      assert (Hres := FIX l l1' l2' Heq).
      destruct Hres as [Hlen1 Hlen2].
      split; simpl; [apply le_n_S; apply le_S; exact Hlen1 | apply le_n_S; apply le_S; exact Hlen2].
Qed.

Lemma split_length_lt : forall a b l l1 l2, split (a :: b :: l) = (l1, l2) ->
  length l1 < length (a :: b :: l) /\ length l2 < length (a :: b :: l).
Proof.
  intros a b l l1 l2 H. simpl in H.
  destruct (split l) as [l1' l2'] eqn:Heq.
  simpl in H. inversion H; subst; clear H.
  apply split_length_bound in Heq. destruct Heq as [Hlen1 Hlen2].
  split; simpl; lia.
Qed.

Lemma mergesort_sorted_gen : forall n l, length l <= n -> sorted (mergesort n l).
Proof.
  induction n as [|n IH]; intros l Hlen.
  - apply Nat.le_0_r in Hlen. destruct l; [|discriminate]. simpl. constructor.
  - destruct l as [|x l]; [simpl; constructor|].
    destruct l as [|y l]; [simpl; constructor|].
    cbv -[split].
    destruct (split (x :: y :: l)) as [l1 l2] eqn:Heq; simpl.
    apply merge_sorted.
    + apply IH. apply split_length_lt in Heq. destruct Heq as [Hlt1 _].
      simpl in Hlen. simpl in Hlt1. lia.
    + apply IH. apply split_length_lt in Heq. destruct Heq as [_ Hlt2].
      simpl in Hlen. simpl in Hlt2. lia.
Qed.

Theorem mergesort_sorted : forall l,
  sorted (mergesort (length l) l).
Proof.
  intros l. apply mergesort_sorted_gen. reflexivity.
Qed.

Theorem mergesort_sorted_neg : ~ (forall l,
  sorted (mergesort (length l) l)).
Proof. Admitted.

Lemma merge_perm : forall l1 l2, Permutation (l1 ++ l2) (merge l1 l2).
Proof.
  induction l1 as [|a l1 IH]; simpl; intros l2.
  - apply Permutation_refl.
  - induction l2 as [|b l2 IH2]; simpl.
    + rewrite app_nil_r. apply Permutation_refl.
    + destruct (a <=? b) eqn:Heq.
      * apply perm_skip. apply IH.
      * simpl.
        change ((fix merge_inner (l0 : list nat) : list nat :=
          match l0 with
          | [] => a :: l1
          | y :: ys => if a <=? y then a :: merge l1 l0 else y :: merge_inner ys
          end) l2) with (merge (a :: l1) l2).
        apply (perm_trans (l' := (b :: l2) ++ a :: l1)).
        -- change (a :: l1 ++ b :: l2) with ((a :: l1) ++ b :: l2).
           apply Permutation_app_comm.
        -- apply perm_skip.
           apply (perm_trans (l' := (a :: l1) ++ l2)).
           ++ apply Permutation_app_comm.
           ++ exact IH2.
Qed.

Lemma split_perm : forall l, Permutation l (fst (split l) ++ snd (split l)).
Proof.
  fix FIX 1.
  intros l.
  destruct l as [|a l].
  - simpl. apply Permutation_refl.
  - destruct l as [|b l].
    + simpl. apply Permutation_refl.
    + simpl split. destruct (split l) as [l1 l2] eqn:Heq; simpl.
      apply perm_skip.
      apply (perm_trans (l' := b :: l1 ++ l2)).
      * apply perm_skip. pose proof (FIX l) as Hp. rewrite Heq in Hp. simpl in Hp. exact Hp.
      * change (b :: l1 ++ l2) with ([b] ++ l1 ++ l2).
        apply (perm_trans (l' := l1 ++ [b] ++ l2)).
        -- rewrite (app_assoc [b] l1 l2).
           rewrite (app_assoc l1 [b] l2).
           apply Permutation_app_tail.
           apply Permutation_app_comm.
        -- simpl. apply Permutation_refl.
Qed.

Lemma mergesort_perm_gen : forall n l, length l <= n -> Permutation l (mergesort n l).
Proof.
  induction n as [|n IH]; intros l Hlen.
  - apply Nat.le_0_r in Hlen. destruct l; [|discriminate]. simpl. apply Permutation_refl.
  - destruct l as [|x l]; [simpl; apply Permutation_refl|].
    destruct l as [|y l]; [simpl; apply Permutation_refl|].
    cbv -[split].
    destruct (split (x :: y :: l)) as [l1 l2] eqn:Heq; simpl.
    apply (perm_trans (l' := l1 ++ l2)).
    + pose proof (split_perm (x :: y :: l)) as Hp.
      rewrite Heq in Hp. simpl in Hp. exact Hp.
    + apply (perm_trans (l' := mergesort n l1 ++ mergesort n l2)).
      * apply Permutation_app.
        -- apply IH. apply split_length_lt in Heq. destruct Heq as [Hlt1 _].
           simpl in Hlen. simpl in Hlt1. lia.
        -- apply IH. apply split_length_lt in Heq. destruct Heq as [_ Hlt2].
           simpl in Hlen. simpl in Hlt2. lia.
      * apply merge_perm.
Qed.

Theorem mergesort_perm : forall l,
  Permutation l (mergesort (length l) l).
Proof.
  intros l. apply mergesort_perm_gen. reflexivity.
Qed.

Theorem mergesort_perm_neg : ~ (forall l,
  Permutation l (mergesort (length l) l)).
Proof. Admitted.
