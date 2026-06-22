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

Lemma sorted_tail : forall x l, sorted (x :: l) -> sorted l.
Proof.
  intros x l H; inversion H; [apply sorted_nil | subst; exact H3].
Qed.

Lemma merge_nil_r : forall l, merge l [] = l.
Proof.
  induction l as [| x xs IH].
  - reflexivity.
  - simpl. reflexivity.
Qed.

(** The key lemma: merge of two sorted lists is sorted. *)
Lemma merge_sorted : forall l1 l2,
  sorted l1 -> sorted l2 -> sorted (merge l1 l2).
Proof.
intros l1; induction l1 as [| x xs IHxs]; [intros l2 _ H2; simpl; exact H2 | intro l2; induction l2 as [| y ys IHys]; [intros H1 _; rewrite merge_nil_r; exact H1 | idtac]].
  { intros H1 H2; simpl; destruct (x <=? y) eqn:Hxy.
    { apply Nat.leb_le in Hxy; assert (Hm: sorted (merge xs (y :: ys))) by (apply IHxs; [eapply sorted_tail; exact H1 | exact H2]); destruct (merge xs (y :: ys)) as [| z zs] eqn:Heqm; [apply sorted_singleton | apply sorted_cons; [| exact Hm]].
      destruct xs as [| x2 xs2]; [simpl in Heqm; injection Heqm; intros; subst; exact Hxy | simpl in Heqm; destruct (x2 <=? y) eqn:Hx2y; injection Heqm; intros; subst; [inversion H1; lia | exact Hxy]].
    }
    { change (sorted (y :: merge (x :: xs) ys)); apply Nat.leb_nle in Hxy; assert (Hm: sorted (merge (x :: xs) ys)) by (apply IHys; [exact H1 | eapply sorted_tail; exact H2]); destruct (merge (x :: xs) ys) as [| z zs] eqn:Heqm; [apply sorted_singleton | apply sorted_cons; [| exact Hm]].
      destruct ys as [| y2 ys2]; simpl in Heqm; [injection Heqm; intros; subst; lia | destruct (x <=? y2) eqn:Hxy2; injection Heqm; intros; subst; [apply Nat.leb_le in Hxy2; inversion H2; lia | inversion H2; lia]].
    }
  }
Qed.

(** ** Helper lemmas about split *)

Lemma split_spec : forall l l1 l2,
  split l = (l1, l2) ->
  length l1 + length l2 = length l /\ Permutation l (l1 ++ l2).
Proof.
intro l; apply (lt_wf_ind (length l) (fun n => forall l, length l = n -> forall l1 l2, split l = (l1, l2) -> length l1 + length l2 = length l /\ Permutation l (l1 ++ l2))); [| reflexivity].
  { (* 861e7150 *) intros n IHn l0 Hlen l1 l2 Hsplit; destruct l0 as [| a [| b rest]].
    { (* 6a6deb01 *) simpl in Hsplit; injection Hsplit; intros; subst; split; reflexivity.
    }
    { (* 705092df *) simpl in Hsplit; injection Hsplit; intros; subst; split; [reflexivity | apply Permutation_refl].
    }
    { (* bc62debd *) simpl in Hsplit; destruct (split rest) as [r1 r2] eqn:Hsr; injection Hsplit; intros; subst.
      { (* 80a1201b *) assert (Hlen_rest : length rest < length (a :: b :: rest)) by (simpl; lia); assert (IHrest := IHn (length rest) Hlen_rest rest eq_refl r1 r2 Hsr); destruct IHrest as [Hlen12 Hperm]; split; [simpl; lia | simpl; apply (Permutation_trans (l' := a :: b :: r1 ++ r2)); [apply perm_skip; apply perm_skip; exact Hperm | apply perm_skip; apply Permutation_middle]].
      }
    }
  }
Qed.

Lemma split_length : forall l l1 l2,
  split l = (l1, l2) ->
  length l1 + length l2 = length l.
Proof.
  intros l l1 l2 H. exact (proj1 (split_spec l l1 l2 H)).
Qed.

Lemma split_perm : forall l l1 l2,
  split l = (l1, l2) ->
  Permutation l (l1 ++ l2).
Proof.
  intros l l1 l2 H. exact (proj2 (split_spec l l1 l2 H)).
Qed.

Lemma split_length_lt_l : forall x y rest l1 l2,
  split (x :: y :: rest) = (l1, l2) ->
  length l1 < length (x :: y :: rest).
Proof.
  intros x y rest l1 l2 H.
  simpl in H.
  destruct (split rest) as [r1 r2] eqn:Hsplit.
  injection H; intros; subst.
  simpl.
  assert (Hlen := split_length rest r1 r2 Hsplit).
  lia.
Qed.

Lemma split_length_lt_r : forall x y rest l1 l2,
  split (x :: y :: rest) = (l1, l2) ->
  length l2 < length (x :: y :: rest).
Proof.
  intros x y rest l1 l2 H.
  simpl in H.
  destruct (split rest) as [r1 r2] eqn:Hsplit.
  injection H; intros; subst.
  simpl.
  assert (Hlen := split_length rest r1 r2 Hsplit).
  lia.
Qed.

(** ** Permutation lemma for merge *)

Lemma merge_perm : forall l1 l2, Permutation (l1 ++ l2) (merge l1 l2).
Proof.
intros l1; induction l1 as [| x xs IHxs].
  { (* 77c84906 *) intros l2; simpl; apply Permutation_refl.
  }
  { (* 30782dea *) intros l2; induction l2 as [| y ys IHys].
    { (* 466d63a3 *) simpl; rewrite app_nil_r; apply Permutation_refl.
    }
    { (* 5c15ad75 *) simpl; destruct (x <=? y) eqn:Hxy.
      { (* 9abafa5c *) apply perm_skip; apply IHxs.
      }
      { (* 4629d916 *) change (Permutation (x :: xs ++ y :: ys) (y :: merge (x :: xs) ys)); apply (Permutation_trans (l' := y :: (x :: xs) ++ ys)); [apply Permutation_sym; apply Permutation_middle | apply perm_skip; simpl; apply IHys].
      }
    }
  }
Qed.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)


Lemma mergesort_sorted_fuel : forall fuel l, length l <= fuel -> sorted (mergesort fuel l).
Proof.
intro fuel; induction fuel as [| fuel' IHfuel].
  { (* c15ed9fd *) intros l Hlen; destruct l; [apply sorted_nil | simpl in Hlen; lia].
  }
  { (* 88836f6a *) intros l Hlen; destruct l as [| x [| y rest]].
    { (* 3941e19d *) simpl; constructor.
    }
    { (* bfe5df30 *) simpl; constructor.
    }
    { (* 744d2e5c *) destruct (split (x :: y :: rest)) as [l1 l2] eqn:Hsplit.
      { (* 744d2e5c *) assert (Hsorted1: sorted (mergesort fuel' l1)) by (apply IHfuel; assert (Hlenl1 := split_length_lt_l x y rest l1 l2 Hsplit); lia).
        { (* 744d2e5c *) assert (Hsorted2: sorted (mergesort fuel' l2)) by (apply IHfuel; assert (Hlenl2 := split_length_lt_r x y rest l1 l2 Hsplit); lia).
          { (* 744d2e5c *) unfold mergesort; fold mergesort; rewrite Hsplit; apply merge_sorted; [exact Hsorted1 | exact Hsorted2].
          }
        }
      }
    }
  }
Qed.

Theorem mergesort_sorted : forall l,
  sorted (mergesort (length l) l).
Proof.
intro l; apply mergesort_sorted_fuel; lia.
Qed.

Theorem mergesort_sorted_neg : ~ (forall l,
  sorted (mergesort (length l) l)).
Proof.
Admitted.


Lemma mergesort_perm_fuel : forall fuel l, length l <= fuel -> Permutation l (mergesort fuel l).
Proof.
intro fuel; induction fuel as [| fuel' IHfuel].
  { (* 7a95d1e4 *) intros l Hlen; destruct l; [apply perm_nil | simpl in Hlen; lia].
  }
  { (* 3494fce9 *) intros l Hlen; destruct l as [| x [| y rest]].
    { (* ae797d6e *) simpl; apply Permutation_refl.
    }
    { (* 8d6ceac7 *) simpl; apply Permutation_refl.
    }
    { (* 325913f0 *) destruct (split (x :: y :: rest)) as [l1 l2] eqn:Hsplit.
      { (* 325913f0 *) assert (Hlenl1 := split_length_lt_l x y rest l1 l2 Hsplit); assert (Hlenl2 := split_length_lt_r x y rest l1 l2 Hsplit); assert (Hperm1: Permutation l1 (mergesort fuel' l1)) by (apply IHfuel; lia); assert (Hperm2: Permutation l2 (mergesort fuel' l2)) by (apply IHfuel; lia); unfold mergesort; fold mergesort; rewrite Hsplit; apply (Permutation_trans (l' := l1 ++ l2)); [apply split_perm; exact Hsplit | apply (Permutation_trans (l' := mergesort fuel' l1 ++ mergesort fuel' l2)); [apply Permutation_app; [exact Hperm1 | exact Hperm2] | apply merge_perm]].
      }
    }
  }
Qed.

Theorem mergesort_perm : forall l,
  Permutation l (mergesort (length l) l).
Proof.
intro l; apply mergesort_perm_fuel; lia.
Qed.

Theorem mergesort_perm_neg : ~ (forall l,
  Permutation l (mergesort (length l) l)).
Proof.
Admitted.
