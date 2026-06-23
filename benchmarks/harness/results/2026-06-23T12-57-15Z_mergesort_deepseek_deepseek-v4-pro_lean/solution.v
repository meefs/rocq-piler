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

Lemma merge_nil : forall l, merge [] l = l.
Proof. reflexivity. Qed.

Lemma merge_cons_nil : forall x xs, merge (x::xs) [] = x::xs.
Proof. reflexivity. Qed.

Lemma merge_cons_cons : forall x xs y ys,
  merge (x::xs) (y::ys) = if x <=? y then x :: merge xs (y::ys) else y :: merge (x::xs) ys.
Proof. reflexivity. Qed.

Lemma merge_cons_nonnil : forall x xs l2, merge (x::xs) l2 <> [].
Proof.
  intros x xs l2. destruct l2.
  - rewrite merge_cons_nil. discriminate.
  - rewrite merge_cons_cons. destruct (x <=? n); discriminate.
Qed.

Lemma merge_nonnil_r : forall l1 x xs, merge l1 (x::xs) <> [].
Proof.
  intros l1 x xs. destruct l1.
  - simpl. discriminate.
  - rewrite merge_cons_cons. destruct (n <=? x); discriminate.
Qed.

Lemma sorted_inv : forall x l, sorted (x::l) -> sorted l.
Proof.
  intros x l H. inversion H; subst; auto using sorted_nil.
Qed.

Lemma sorted_head_le : forall x y l, sorted (x::y::l) -> x <= y.
Proof.
  intros x y l H. inversion H; subst; auto.
Qed.

Lemma Forall_le_weaken : forall a b l, a <= b -> Forall (le b) l -> Forall (le a) l.
Proof.
  induction l as [|h t IH]; intros Hle HF.
  - constructor.
  - inversion HF; subst. constructor.
    + transitivity b; auto.
    + apply IH; auto.
Qed.

Lemma sorted_Forall_le : forall x l, sorted (x::l) -> Forall (le x) l.
Proof.
  intros x l H. revert x H. induction l as [|y l IH]; intros a H.
  - constructor.
  - inversion H; subst.
    apply Forall_cons.
    + auto.
    + apply Forall_le_weaken with (b:=y).
      * auto.
      * apply IH with (x:=y); auto.
Qed.

Lemma Forall_hd_le : forall a h t, Forall (le a) (h::t) -> a <= h.
Proof. inversion 1; auto. Qed.

Lemma Forall_le_merge : forall a l1 l2,
  Forall (le a) l1 -> Forall (le a) l2 -> Forall (le a) (merge l1 l2).
Proof.
  induction l1 as [|x xs IH]; intros l2 Fa1 Fa2.
  - rewrite merge_nil. exact Fa2.
  - inversion Fa1 as [|? ? Ha Fxs]; subst. clear Fa1.
    induction l2 as [|y ys IHinner].
    + rewrite merge_cons_nil. constructor; auto.
    + inversion Fa2 as [|? ? Hb Fys]; subst. clear Fa2.
      rewrite merge_cons_cons.
      destruct (x <=? y) eqn:Hle.
      * apply Forall_cons.
        -- exact Ha.
        -- apply IH.
           ++ exact Fxs.
           ++ constructor; auto.
      * apply Forall_cons.
        -- exact Hb.
        -- apply IHinner. auto.
Qed.

Lemma merge_sorted : forall l1 l2, sorted l1 -> sorted l2 -> sorted (merge l1 l2).
Proof.
  induction l1 as [|x xs IH]; intros l2 Hs1 Hs2.
  - rewrite merge_nil; auto.
  - induction l2 as [|y ys IHinner].
    + rewrite merge_cons_nil; auto.
    + rewrite merge_cons_cons.
      destruct (x <=? y) eqn:Hle.
      * apply Nat.leb_le in Hle.
        assert (Hfa : Forall (le x) (merge xs (y::ys))).
        { apply Forall_le_merge.
          - apply sorted_Forall_le. auto.
          - apply Forall_cons.
            + exact Hle.
            + apply Forall_le_weaken with (b:=y).
              * exact Hle.
              * apply sorted_Forall_le. auto.
        }
        destruct (merge xs (y::ys)) as [|h t] eqn:Hmerge.
        { exfalso; apply (merge_nonnil_r xs y ys). rewrite Hmerge. reflexivity. }
        apply sorted_cons.
        { apply Forall_hd_le with (t:=t). exact Hfa. }
        { rewrite <- Hmerge. apply IH. apply sorted_inv with (x:=x). auto. auto. }
      * assert (Hnle : y <= x) by (apply Nat.leb_gt in Hle; lia).
        assert (Hfa : Forall (le y) (merge (x::xs) ys)).
        { apply Forall_le_merge.
          - apply Forall_cons.
            + exact Hnle.
            + apply Forall_le_weaken with (b:=x).
              * exact Hnle.
              * apply sorted_Forall_le. auto.
          - apply sorted_Forall_le. auto.
        }
        destruct (merge (x::xs) ys) as [|h t] eqn:Hmerge.
        { exfalso; apply (merge_cons_nonnil x xs ys). rewrite Hmerge. reflexivity. }
        apply sorted_cons.
        { apply Forall_hd_le with (t:=t). exact Hfa. }
        { apply IHinner. auto. apply sorted_inv with (x:=y). auto. }
Qed.

Lemma split_length_eq_aux : forall l,
  length (fst (split l)) + length (snd (split l)) = length l.
Proof.
  fix aux 1.
  intro l. destruct l as [|x l].
  - reflexivity.
  - destruct l as [|y l].
    + reflexivity.
    + simpl.
      destruct (split l) as [a b] eqn:Heq.
      simpl.
      pose proof (aux l) as IH.
      rewrite Heq in IH. simpl in IH.
      simpl in IH. lia.
Qed.

Lemma split_length_eq : forall l l1 l2,
  split l = (l1, l2) -> length l1 + length l2 = length l.
Proof.
  intros l l1 l2 H.
  pose proof (split_length_eq_aux l) as Hlen.
  rewrite H in Hlen. simpl in Hlen. exact Hlen.
Qed.

Lemma split_length_ge1 : forall l l1 l2,
  length l >= 2 -> split l = (l1, l2) -> 1 <= length l1 /\ 1 <= length l2.
Proof.
  intros l l1 l2 Hlen Hsplit.
  destruct l as [|x l]; [simpl in Hlen; lia|].
  destruct l as [|y l]; [simpl in Hlen; lia|].
  simpl in Hsplit.
  case_eq (split l). intros a b Heq. rewrite Heq in Hsplit.
  inversion Hsplit; subst. simpl. lia.
Qed.

Lemma split_perm : forall l l1 l2,
  split l = (l1, l2) -> Permutation l (l1 ++ l2).
Proof.
  fix aux 1.
  intro l. destruct l as [|x l]; simpl; intros l1 l2 H.
  - inversion H; subst. reflexivity.
  - destruct l as [|y l]; simpl in H.
    + inversion H; subst. reflexivity.
    + case_eq (split l). intros a b Heq.
      rewrite Heq in H. inversion H; subst. simpl.
      pose proof (aux l a b Heq) as IH.
      apply Permutation_trans with (x :: y :: a ++ b).
      * apply perm_skip. apply perm_skip. exact IH.
      * apply perm_skip. apply Permutation_cons_app. reflexivity.
Qed.

Lemma merge_perm : forall l1 l2, Permutation (l1 ++ l2) (merge l1 l2).
Proof.
  induction l1 as [|x xs IH]; intros l2.
  - simpl. reflexivity.
  - induction l2 as [|y ys IHinner].
    + rewrite merge_cons_nil. rewrite app_nil_r. reflexivity.
    + rewrite merge_cons_cons.
      simpl.
      destruct (x <=? y) eqn:Hle.
      * apply perm_skip. apply IH.
      * apply Permutation_trans with (y :: x :: xs ++ ys).
        { apply Permutation_trans with (x :: y :: xs ++ ys).
          - apply perm_skip.
            apply Permutation_sym.
            apply Permutation_cons_app.
            reflexivity.
          - apply perm_swap. }
        { apply perm_skip. apply IHinner. }
Qed.

(** ** Main theorems *)

Lemma mergesort_sorted_fuel : forall fuel l,
  length l <= fuel -> sorted (mergesort fuel l).
Proof.
  induction fuel as [|fuel' IH]; intros l Hlen.
  - assert (l = []) by (destruct l; simpl in Hlen; auto; lia). subst. constructor.
  - destruct l as [|x l].
    + simpl. constructor.
    + destruct l as [|y l].
      * simpl. constructor.
      * simpl.
        assert (H2 : length (x :: y :: l) >= 2) by (simpl; lia).
        case_eq (split l). intros a b Heq.
        pose proof (split_length_eq_aux l) as Hlen_sum.
        rewrite Heq in Hlen_sum. simpl in Hlen_sum.
        apply merge_sorted.
        -- apply IH. simpl in Hlen. simpl. lia.
        -- apply IH. simpl in Hlen. simpl. lia.
Qed.

Theorem mergesort_sorted : forall l,
  sorted (mergesort (length l) l).
Proof.
  intro l. apply mergesort_sorted_fuel. lia.
Qed.

Theorem mergesort_sorted_neg : ~ (forall l,
  sorted (mergesort (length l) l)).
Proof.
Admitted.

Lemma mergesort_perm_fuel : forall fuel l,
  length l <= fuel -> Permutation l (mergesort fuel l).
Proof.
  induction fuel as [|fuel' IH]; intros l Hlen.
  - assert (l = []) by (destruct l; simpl in Hlen; auto; lia). subst. reflexivity.
  - destruct l as [|x l].
    + simpl. reflexivity.
    + destruct l as [|y l].
      * simpl. reflexivity.
      * simpl.
        assert (H2 : length (x :: y :: l) >= 2) by (simpl; lia).
        case_eq (split l). intros a b Heq.
        pose proof (split_length_eq_aux l) as Hlen_sum.
        rewrite Heq in Hlen_sum. simpl in Hlen_sum.
        set (l1 := x :: a). set (l2 := y :: b).
        apply Permutation_trans with (l1 ++ l2).
        { apply (split_perm (x::y::l) l1 l2). subst l1 l2. simpl. rewrite Heq. reflexivity. }
        { apply Permutation_trans with (mergesort fuel' l1 ++ mergesort fuel' l2).
          { apply Permutation_app.
            - apply IH. subst l1. simpl in Hlen. simpl. lia.
            - apply IH. subst l2. simpl in Hlen. simpl. lia.
          }
          { apply merge_perm. }
        }
Qed.

Theorem mergesort_perm : forall l,
  Permutation l (mergesort (length l) l).
Proof.
  intro l. apply mergesort_perm_fuel. lia.
Qed.

Theorem mergesort_perm_neg : ~ (forall l,
  Permutation l (mergesort (length l) l)).
Proof.
Admitted.
