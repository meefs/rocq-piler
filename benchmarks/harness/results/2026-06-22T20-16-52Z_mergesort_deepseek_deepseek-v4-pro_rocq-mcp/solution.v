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

(** * Helper lemmas *)

Lemma merge_cons_l : forall x xs l,
  merge (x :: xs) l =
  (fix merge_inner (l0 : list nat) : list nat :=
    match l0 with
    | [] => x :: xs
    | y :: ys => if x <=? y then x :: merge xs l0 else y :: merge_inner ys
    end) l.
Proof. reflexivity. Qed.

Lemma merge_cons_cons : forall x xs y ys,
  merge (x :: xs) (y :: ys) =
  if x <=? y then x :: merge xs (y :: ys) else y :: merge (x :: xs) ys.
Proof.
  intros; simpl; reflexivity.
Qed.

Lemma sorted_inv : forall a l, sorted (a :: l) -> sorted l.
Proof.
  intros a l Hs. inversion Hs; subst; auto. constructor.
Qed.

Lemma Forall_le_trans : forall a b l, a <= b -> Forall (le b) l -> Forall (le a) l.
Proof.
  intros a b l Hle Hf.
  induction Hf.
  - constructor.
  - constructor; [lia | auto].
Qed.

Lemma sorted_Forall_le : forall a l, sorted (a :: l) -> Forall (le a) l.
Proof.
  intros a l. revert a.
  induction l as [|b l' IH]; intros a Hs.
  - constructor.
  - inversion Hs as [| |? ? ? Hle Hs']; subst; clear Hs.
    constructor.
    + exact Hle.
    + apply Forall_le_trans with b; [auto | apply IH with (a := b); auto].
Qed.

Lemma Forall_merge : forall (P : nat -> Prop) l1 l2,
  Forall P l1 -> Forall P l2 -> Forall P (merge l1 l2).
Proof.
  induction l1 as [|x xs IH]; intros l2 H1 H2.
  - simpl; auto.
  - induction l2 as [|y ys IHl2].
    + simpl. inversion H1; subst; auto.
    + rewrite merge_cons_cons.
      inversion H1 as [|? ? Hx Hxs]; subst.
      inversion H2 as [|? ? Hy Hys]; subst.
      destruct (x <=? y); constructor; auto.
Qed.

Lemma merge_sorted : forall l1 l2, sorted l1 -> sorted l2 -> sorted (merge l1 l2).
Proof.
  induction l1 as [|x xs IH]; intros l2 Hs1 Hs2.
  - simpl. auto.
  - induction l2 as [|y ys IHl2].
    + simpl. inversion Hs1; subst; auto.
    + rewrite merge_cons_cons.
      destruct (x <=? y) eqn:Hcmp.
      * apply Nat.leb_le in Hcmp.
        inversion Hs1 as [|x'|x' hd tl Hhd Hs1']; subst; clear Hs1.
        -- constructor; auto.
        -- assert (H_forall_x : Forall (le x) (hd :: tl)).
           { apply sorted_Forall_le with (a := x). constructor; auto. }
           assert (H_forall_y : Forall (le x) (y :: ys)).
           { pose proof (sorted_Forall_le y ys Hs2).
             constructor; [exact Hcmp |]. apply Forall_le_trans with y; auto. }
           apply Forall_merge with (P := le x) (l1 := hd :: tl) (l2 := y :: ys) in H_forall_x;
             [| exact H_forall_y].
           destruct (merge (hd :: tl) (y :: ys)) as [|h t] eqn:Hm.
           ++ constructor.
           ++ constructor.
              ** inversion H_forall_x as [|? ? Hh Ht]; subst. exact Hh.
              ** rewrite <- Hm. apply IH with (l2 := y :: ys); [exact Hs1' | exact Hs2].
      * apply Nat.leb_gt in Hcmp.
        inversion Hs2 as [|y'|y' hd tl Hhd Hs2']; subst; clear Hs2.
        -- constructor; [lia | auto].
        -- assert (H_forall_y : Forall (le y) (hd :: tl)).
           { apply sorted_Forall_le with (a := y). constructor; auto. }
           assert (H_forall_x : Forall (le y) (x :: xs)).
           { pose proof (sorted_Forall_le x xs Hs1).
             constructor; [lia |]. apply Forall_le_trans with x; auto; lia. }
           apply Forall_merge with (P := le y) (l1 := x :: xs) (l2 := hd :: tl) in H_forall_x;
             [| exact H_forall_y].
           destruct (merge (x :: xs) (hd :: tl)) as [|h t] eqn:Hm.
           ++ constructor.
           ++ constructor.
              ** inversion H_forall_x as [|? ? Hh Ht]; subst. exact Hh.
              ** apply IHl2. exact Hs2'.
Qed.

Lemma split_induction : forall (P : list nat -> Prop),
  P [] ->
  (forall x, P [x]) ->
  (forall x y rest, P rest -> P (x :: y :: rest)) ->
  forall l, P l.
Proof.
  intros P Hnil Hsing Hcons.
  fix IH 1.
  intros l.
  destruct l as [|a l'].
  - apply Hnil.
  - destruct l' as [|b rest].
    + apply Hsing.
    + apply Hcons. apply IH.
Qed.

Lemma split_length_sum : forall l l1 l2,
  split l = (l1, l2) -> length l1 + length l2 = length l.
Proof.
  induction l as [|a|a b rest IH] using split_induction;
    simpl; intros l1 l2 Hsplit.
  - inversion Hsplit; auto.
  - inversion Hsplit; subst; simpl; auto.
  - destruct (split rest) as [l1' l2'] eqn:Hs.
    injection Hsplit as Hl1 Hl2.
    subst. simpl. specialize (IH l1' l2' eq_refl). lia.
Qed.

Lemma split_length_pos : forall l, length l >= 2 ->
  forall l1 l2, split l = (l1, l2) -> length l1 > 0 /\ length l2 > 0.
Proof.
  intros l Hlen l1 l2 Hsplit.
  destruct l as [|a [|b rest]]; simpl in Hlen; try lia.
  simpl in Hsplit.
  destruct (split rest) as [l1' l2'] eqn:Hs.
  injection Hsplit as Hl1 Hl2.
  subst. simpl. split; lia.
Qed.

Lemma split_length_lt : forall l,
  length l >= 2 ->
  forall l1 l2, split l = (l1, l2) -> length l1 < length l /\ length l2 < length l.
Proof.
  intros l Hlen l1 l2 Hsplit.
  pose proof (split_length_sum l l1 l2 Hsplit).
  pose proof (split_length_pos l Hlen l1 l2 Hsplit) as [Hpos1 Hpos2].
  split; lia.
Qed.

Theorem mergesort_sorted : forall l,
  sorted (mergesort (length l) l).
Proof.
  cut (forall n l, length l <= n -> sorted (mergesort n l)).
  { intros H l. apply H with (n := length l). lia. }
  induction n as [|n' IH]; intros l Hle.
  - assert (l = []) by (destruct l; simpl in *; lia || auto).
    subst. simpl. constructor.
  - simpl.
    destruct l as [|a l'].
    + constructor.
    + destruct l' as [|b rest].
      * constructor.
      * destruct (split (a :: b :: rest)) as [l1 l2] eqn:Hsplit.
        apply merge_sorted.
        -- apply IH.
           pose proof (split_length_lt (a :: b :: rest) ltac:(simpl; lia) l1 l2 Hsplit) as [Hlen1 Hlen2].
           simpl in Hle, Hlen1, Hlen2. lia.
        -- apply IH.
           pose proof (split_length_lt (a :: b :: rest) ltac:(simpl; lia) l1 l2 Hsplit) as [Hlen1 Hlen2].
           simpl in Hle, Hlen1, Hlen2. lia.
Qed.

Theorem mergesort_sorted_neg : ~ (forall l,
  sorted (mergesort (length l) l)).
Proof.
Admitted.

Lemma perm_cons_app : forall (a : nat) l1 l2, Permutation (l1 ++ a :: l2) (a :: l1 ++ l2).
Proof.
  intros a l1 l2.
  induction l1 as [|x l1' IH]; simpl.
  - apply Permutation_refl.
  - apply Permutation_trans with (x :: a :: l1' ++ l2).
    + apply perm_skip. apply IH.
    + apply perm_swap.
Qed.

Lemma merge_perm : forall l1 l2, Permutation (l1 ++ l2) (merge l1 l2).
Proof.
  induction l1 as [|x xs IH]; intros l2; simpl.
  - apply Permutation_refl.
  - induction l2 as [|y ys IHl2]; simpl.
    + rewrite app_nil_r. apply Permutation_refl.
    + destruct (x <=? y).
      * simpl. apply perm_skip. apply IH.
      * apply Permutation_trans with (y :: (x :: xs ++ ys)).
        -- rewrite (app_comm_cons xs (y :: ys) x). apply perm_cons_app.
        -- apply perm_skip. apply IHl2.
Qed.

Lemma split_perm : forall l,
  Permutation l (fst (split l) ++ snd (split l)).
Proof.
  induction l as [|a|a b rest IH] using split_induction; simpl.
  - apply Permutation_refl.
  - apply Permutation_refl.
  - destruct (split rest) as [l1 l2] eqn:Hs.
    simpl in IH. simpl.
    apply perm_skip.
    apply Permutation_trans with (b :: l1 ++ l2).
    + apply perm_skip. exact IH.
    + assert (Htemp : Permutation (b :: l1) (l1 ++ [b])).
      { change (b :: l1) with ([b] ++ l1). apply Permutation_app_comm. }
      pose proof (Permutation_app_tail l2 Htemp) as Htemp2.
      apply Permutation_trans with ((l1 ++ [b]) ++ l2); [exact Htemp2 |].
      rewrite <- app_assoc. simpl. apply Permutation_refl.
Qed.

Theorem mergesort_perm : forall l,
  Permutation l (mergesort (length l) l).
Proof.
  cut (forall n l, length l <= n -> Permutation l (mergesort n l)).
  { intros H l. apply H with (n := length l). lia. }
  induction n as [|n' IH]; intros l Hle.
  - simpl. apply Permutation_refl.
  - simpl.
    destruct l as [|a l'].
    + apply Permutation_refl.
    + destruct l' as [|b rest].
      * apply Permutation_refl.
      * destruct (split (a :: b :: rest)) as [l1 l2] eqn:Hsplit.
        pose proof (split_length_lt (a :: b :: rest) ltac:(simpl; lia) l1 l2 Hsplit) as [Hlen1 Hlen2].
        simpl in Hle, Hlen1, Hlen2.
        assert (Hle1 : length l1 <= n') by lia.
        assert (Hle2 : length l2 <= n') by lia.
        apply Permutation_trans with (l1 ++ l2).
        -- pose proof (split_perm (a :: b :: rest)) as Hperm.
           rewrite Hsplit in Hperm. simpl in Hperm. exact Hperm.
        -- apply Permutation_trans with (mergesort n' l1 ++ mergesort n' l2).
           ++ apply Permutation_app; [apply IH | apply IH]; auto.
           ++ apply merge_perm.
Qed.

Theorem mergesort_perm_neg : ~ (forall l,
  Permutation l (mergesort (length l) l)).
Proof.
Admitted.
