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

Lemma sorted_Forall_le : forall x l, sorted (x :: l) -> Forall (le x) l.
Proof.
  intros x l H.
  revert x H.
  induction l as [|y l IH]; intros x H.
  - constructor.
  - inversion H as [| | ? ? ? Hle Hsort]; subst; clear H.
    constructor.
    + exact Hle.
    + apply (Forall_impl (P := le y) (le x)).
      { intros z Hz. apply Nat.le_trans with (m := y); assumption. }
      apply (IH y). exact Hsort.
Qed.

Lemma sorted_cons_general : forall x l, sorted l -> Forall (le x) l -> sorted (x :: l).
Proof.
  intros x l Hs Hf.
  revert x Hs Hf.
  induction l as [|y l IH]; intros x Hs Hf.
  - constructor.
  - inversion Hs as [| | y' z' l' Hle_s Hs']; subst; clear Hs.
    + inversion Hf as [|? ? Hle_x_y Hf']; subst; clear Hf.
      constructor; [exact Hle_x_y | constructor].
    + inversion Hf as [|? ? Hle_x_y Hf']; subst; clear Hf.
      constructor; auto.
      constructor; auto.
Qed.

Lemma sorted_tail : forall x l, sorted (x :: l) -> sorted l.
Proof.
  intros x l Hs.
  inversion Hs; subst; auto.
  constructor.
Qed.

Lemma sorted_head_le : forall x y l, sorted (x :: y :: l) -> x <= y.
Proof. inversion 1; auto. Qed.

Lemma merge_Forall : forall (P : nat -> Prop) l1 l2,
  Forall P l1 -> Forall P l2 -> Forall P (merge l1 l2).
Proof.
  intros P l1 l2 H1 H2.
  revert l2 H2 H1.
  induction l1 as [|x1 l1 IH]; intros l2 H2 H1.
  - simpl; exact H2.
  - inversion H1 as [|? ? Hx1 Hl1]; subst; clear H1.
    simpl.
    induction l2 as [|y2 l2 IHl2] in H2 |- *.
    + simpl. constructor; auto.
    + inversion H2 as [|? ? Hy2 Hl2]; subst; clear H2.
      simpl.
      destruct (x1 <=? y2) eqn:Heq.
      { constructor.
        - exact Hx1.
        - refine (IH (y2 :: l2) _ Hl1).
          constructor; [exact Hy2 | exact Hl2]. }
      { constructor.
        - exact Hy2.
        - apply IHl2. exact Hl2. }
Qed.

Lemma merge_cons_cons : forall x1 l1 y2 l2,
  merge (x1 :: l1) (y2 :: l2) =
  if x1 <=? y2 then x1 :: merge l1 (y2 :: l2) else y2 :: merge (x1 :: l1) l2.
Proof. reflexivity. Qed.

Lemma merge_sorted : forall l1 l2, sorted l1 -> sorted l2 -> sorted (merge l1 l2).
Proof.
  induction l1 as [|x1 l1 IH1]; induction l2 as [|y2 l2 IH2]; intros Hs1 Hs2.
  - simpl. exact Hs2.
  - simpl. exact Hs2.
  - simpl. exact Hs1.
  - rewrite merge_cons_cons.
    destruct (x1 <=? y2) eqn:Heq.
    + apply Nat.leb_le in Heq.
      apply sorted_cons_general.
      { apply IH1 with (l2 := y2 :: l2).
        - apply sorted_tail with (x := x1). exact Hs1.
        - exact Hs2. }
      { apply merge_Forall.
        { apply sorted_Forall_le. exact Hs1. }
        { constructor.
          { exact Heq. }
          apply (Forall_impl (P := le y2) (le x1)).
          { intros z Hz. apply Nat.le_trans with (m := y2); assumption. }
          apply sorted_Forall_le. exact Hs2. } }
    + apply Nat.leb_gt in Heq.
      apply sorted_cons_general.
      { apply IH2.
        - exact Hs1.
        - apply sorted_tail with (x := y2). exact Hs2. }
      { apply merge_Forall.
        { constructor.
          { apply Nat.lt_le_incl. exact Heq. }
          apply (Forall_impl (P := le x1) (le y2)).
          { intros z Hz. apply Nat.le_trans with (m := x1); [apply Nat.lt_le_incl; exact Heq | exact Hz]. }
          apply sorted_Forall_le. exact Hs1. }
        { apply (sorted_Forall_le y2). exact Hs2. } }
Qed.

Lemma split_length_sum : forall l,
  length (fst (split l)) + length (snd (split l)) = length l.
Proof.
  fix aux 1.
  intros l.
  destruct l as [|a l]; [reflexivity|].
  destruct l as [|b l]; [reflexivity|].
  simpl.
  destruct (split l) as [l1 l2] eqn:E.
  simpl.
  pose proof (aux l) as H.
  rewrite E in H. simpl in H.
  lia.
Qed.

Lemma split_fst_cons : forall a b l, exists l1', fst (split (a :: b :: l)) = a :: l1'.
Proof.
  intros a b l.
  destruct l as [|c l].
  - exists []. reflexivity.
  - change (split (a :: b :: c :: l))
      with (let (l1, l2) := split (c :: l) in (a :: l1, b :: l2)).
    destruct (split (c :: l)) as [x y] eqn:E.
    simpl. exists x. reflexivity.
Qed.

Lemma split_snd_cons : forall a b l, exists l2', snd (split (a :: b :: l)) = b :: l2'.
Proof.
  intros a b l.
  destruct l as [|c l].
  - exists []. reflexivity.
  - change (split (a :: b :: c :: l))
      with (let (l1, l2) := split (c :: l) in (a :: l1, b :: l2)).
    destruct (split (c :: l)) as [x y] eqn:E.
    simpl. exists y. reflexivity.
Qed.

Lemma split_fst_length_lt : forall a b l,
  length (fst (split (a :: b :: l))) < length (a :: b :: l).
Proof.
  intros a b l.
  assert (Hsum := split_length_sum (a :: b :: l)).
  destruct (split (a :: b :: l)) as [l1 l2] eqn:E.
  simpl in Hsum.
  assert (Hlen_snd_pos : length l2 > 0).
  { destruct (split_snd_cons a b l) as [l2' Hsnd].
    rewrite E in Hsnd. simpl in Hsnd.
    rewrite Hsnd. simpl. lia. }
  simpl. lia.
Qed.

Lemma split_snd_length_lt : forall a b l,
  length (snd (split (a :: b :: l))) < length (a :: b :: l).
Proof.
  intros a b l.
  assert (Hsum := split_length_sum (a :: b :: l)).
  destruct (split (a :: b :: l)) as [l1 l2] eqn:E.
  simpl in Hsum.
  assert (Hlen_fst_pos : length l1 > 0).
  { destruct (split_fst_cons a b l) as [l1' Hfst].
    rewrite E in Hfst. simpl in Hfst.
    rewrite Hfst. simpl. lia. }
  simpl. lia.
Qed.

(** ** Sorted Theorem *)

Lemma mergesort_sorted_fuel : forall fuel l,
  length l <= fuel -> sorted (mergesort fuel l).
Proof.
  induction fuel as [|fuel IH]; intros l Hle.
  - simpl.
    enough (l = []) by (subst; constructor).
    apply length_zero_iff_nil. lia.
  - destruct l as [|a l].
    + simpl. constructor.
    + destruct l as [|b l].
      * simpl. constructor.
      * simpl.
        destruct (split l) as [l1 l2] eqn:E.
        simpl.
        apply merge_sorted.
        -- apply IH.
           assert (Hbound : length l1 <= length l).
           { pose proof (split_length_sum l). rewrite E in H. simpl in H. lia. }
           simpl. simpl in Hle. lia.
        -- apply IH.
           assert (Hbound : length l2 <= length l).
           { pose proof (split_length_sum l). rewrite E in H. simpl in H. lia. }
           simpl. simpl in Hle. lia.
Qed.

Theorem mergesort_sorted : forall l,
  sorted (mergesort (length l) l).
Proof.
  intros l. apply mergesort_sorted_fuel. auto.
Qed.

Theorem mergesort_sorted_neg : ~ (forall l,
  sorted (mergesort (length l) l)).
Proof.
Admitted.

(** ** Permutation Theorem *)

Lemma merge_perm : forall l1 l2, Permutation (l1 ++ l2) (merge l1 l2).
Proof.
  induction l1 as [|x1 l1 IH]; intros l2; simpl.
  - apply Permutation_refl.
  - revert IH.
    induction l2 as [|y2 l2 IHl2]; intros IH.
    + simpl. rewrite app_nil_r. apply Permutation_refl.
    + simpl.
      destruct (x1 <=? y2) eqn:Heq.
      * simpl.
        apply perm_skip.
        apply IH.
      * simpl.
        apply Permutation_trans with (l' := x1 :: y2 :: l1 ++ l2).
        -- apply perm_skip.
           apply Permutation_sym.
           apply Permutation_middle.
        -- apply Permutation_trans with (l' := y2 :: x1 :: l1 ++ l2).
           ++ apply perm_swap.
           ++ apply perm_skip. apply IHl2. exact IH.
Qed.

Lemma split_perm : forall l,
  Permutation l (fst (split l) ++ snd (split l)).
Proof.
  fix aux 1.
  intros l.
  destruct l as [|a l]; simpl.
  - apply Permutation_refl.
  - destruct l as [|b l]; simpl.
    + apply Permutation_refl.
    + destruct (split l) as [l1 l2] eqn:E; simpl.
      pose proof (aux l) as Haux.
      rewrite E in Haux. simpl in Haux.
      apply Permutation_trans with (l' := a :: b :: (l1 ++ l2)).
      * apply perm_skip. apply perm_skip. exact Haux.
      * apply perm_skip. apply Permutation_middle.
Qed.

Lemma mergesort_perm_fuel : forall fuel l,
  length l <= fuel -> Permutation l (mergesort fuel l).
Proof.
  induction fuel as [|fuel IH]; intros l Hle.
  - simpl.
    enough (l = []) by (subst; apply Permutation_refl).
    apply length_zero_iff_nil. lia.
  - destruct l as [|a l].
    + simpl. apply Permutation_refl.
    + destruct l as [|b l].
      * simpl. apply Permutation_refl.
       * simpl.
         destruct (split l) as [l1 l2] eqn:E.
         simpl.
         pose proof (split_perm (a :: b :: l)) as Hsp.
         simpl in Hsp. rewrite E in Hsp. simpl in Hsp.
         apply Permutation_trans with (l' := (a :: l1) ++ (b :: l2)).
         -- exact Hsp.
         -- apply Permutation_trans with (l' := mergesort fuel (a :: l1) ++ mergesort fuel (b :: l2)).
            ++ apply Permutation_app.
               { apply IH.
                 assert (Hbound : length l1 <= length l).
                 { pose proof (split_length_sum l). rewrite E in H. simpl in H. lia. }
                 simpl. simpl in Hle. lia. }
               { apply IH.
                 assert (Hbound : length l2 <= length l).
                 { pose proof (split_length_sum l). rewrite E in H. simpl in H. lia. }
                 simpl. simpl in Hle. lia. }
            ++ apply merge_perm.
Qed.

Theorem mergesort_perm : forall l,
  Permutation l (mergesort (length l) l).
Proof.
  intros l. apply mergesort_perm_fuel. auto.
Qed.

Theorem mergesort_perm_neg : ~ (forall l,
  Permutation l (mergesort (length l) l)).
Proof.
Admitted.
