From Stdlib Require Import Arith List Lia.
Import ListNotations.

(** * PCF + References: Type Preservation — Benchmark *)

Inductive ty : Type :=
  | TyNat | TyBool | TyArrow : ty -> ty -> ty | TyRef : ty -> ty.

Inductive tm : Type :=
  | Var : nat -> tm | Num : nat -> tm | BOOL : bool -> tm
  | Succ : tm -> tm | Pred : tm -> tm | IsZero : tm -> tm
  | If : tm -> tm -> tm -> tm
  | Lam : ty -> tm -> tm | App : tm -> tm -> tm | Fix : tm -> tm
  | Ref : tm -> tm | Deref : tm -> tm | Assign : tm -> tm -> tm | Loc : nat -> tm.

Definition ctx := list ty.
Definition store_ty := list ty.

Inductive has_type : ctx -> store_ty -> tm -> ty -> Prop :=
  | T_Var : forall G S x T, nth_error G x = Some T -> has_type G S (Var x) T
  | T_Num : forall G S n, has_type G S (Num n) TyNat
  | T_Bool : forall G S b, has_type G S (BOOL b) TyBool
  | T_Succ : forall G S t, has_type G S t TyNat -> has_type G S (Succ t) TyNat
  | T_Pred : forall G S t, has_type G S t TyNat -> has_type G S (Pred t) TyNat
  | T_IsZero : forall G S t, has_type G S t TyNat -> has_type G S (IsZero t) TyBool
  | T_If : forall G S t1 t2 t3 T, has_type G S t1 TyBool -> has_type G S t2 T -> has_type G S t3 T -> has_type G S (If t1 t2 t3) T
  | T_Lam : forall G S T1 T2 t, has_type (T1 :: G) S t T2 -> has_type G S (Lam T1 t) (TyArrow T1 T2)
  | T_App : forall G S t1 t2 T1 T2, has_type G S t1 (TyArrow T1 T2) -> has_type G S t2 T1 -> has_type G S (App t1 t2) T2
  | T_Fix : forall G S t T, has_type (T :: G) S t T -> has_type G S (Fix t) T
  | T_Ref : forall G S t T, has_type G S t T -> has_type G S (Ref t) (TyRef T)
  | T_Deref : forall G S t T, has_type G S t (TyRef T) -> has_type G S (Deref t) T
  | T_Assign : forall G S t1 t2 T, has_type G S t1 (TyRef T) -> has_type G S t2 T -> has_type G S (Assign t1 t2) TyNat
  | T_Loc : forall G S l T, nth_error S l = Some T -> has_type G S (Loc l) (TyRef T).

Inductive value : tm -> Prop :=
  | V_Num : forall n, value (Num n)
  | V_Bool : forall b, value (BOOL b)
  | V_Lam : forall T t, value (Lam T t)
  | V_Loc : forall l, value (Loc l).

Fixpoint shift_at (d : nat) (t : tm) : tm :=
  match t with
  | Var x => if x <? d then Var x else Var (x + 1)
  | Num n => Num n | BOOL b => BOOL b
  | Succ t1 => Succ (shift_at d t1) | Pred t1 => Pred (shift_at d t1)
  | IsZero t1 => IsZero (shift_at d t1)
  | If t1 t2 t3 => If (shift_at d t1) (shift_at d t2) (shift_at d t3)
  | Lam T t1 => Lam T (shift_at (S d) t1)
  | App t1 t2 => App (shift_at d t1) (shift_at d t2)
  | Fix t1 => Fix (shift_at (S d) t1)
  | Ref t1 => Ref (shift_at d t1) | Deref t1 => Deref (shift_at d t1)
  | Assign t1 t2 => Assign (shift_at d t1) (shift_at d t2)
  | Loc l => Loc l
  end.

Definition shift (t : tm) : tm := shift_at 0 t.

Fixpoint subst (j : nat) (s t : tm) : tm :=
  match t with
  | Var x => if Nat.eqb x j then s else Var x
  | Num n => Num n | BOOL b => BOOL b
  | Succ t1 => Succ (subst j s t1) | Pred t1 => Pred (subst j s t1)
  | IsZero t1 => IsZero (subst j s t1)
  | If t1 t2 t3 => If (subst j s t1) (subst j s t2) (subst j s t3)
  | Lam T t1 => Lam T (subst (S j) (shift s) t1)
  | App t1 t2 => App (subst j s t1) (subst j s t2)
  | Fix t1 => Fix (subst (S j) (shift s) t1)
  | Ref t1 => Ref (subst j s t1) | Deref t1 => Deref (subst j s t1)
  | Assign t1 t2 => Assign (subst j s t1) (subst j s t2)
  | Loc l => Loc l
  end.

Definition heap := list (nat * tm).

Fixpoint heap_lookup (l : nat) (mu : heap) : option tm :=
  match mu with
  | [] => None
  | (l', v) :: mu' => if Nat.eqb l l' then Some v else heap_lookup l mu'
  end.

Fixpoint heap_update (l : nat) (v : tm) (mu : heap) : heap :=
  match mu with
  | [] => []
  | (l', v') :: mu' => if Nat.eqb l l' then (l, v) :: mu'
                        else (l', v') :: heap_update l v mu'
  end.

Inductive heap_ok : heap -> store_ty -> Prop :=
  | heap_empty : forall S, heap_ok [] S
  | heap_cons : forall l v mu S T, heap_ok mu S -> has_type [] S v T -> nth_error S l = Some T -> heap_ok ((l, v) :: mu) S.

Inductive step : tm -> heap -> tm -> heap -> Prop :=
  | S_Succ : forall t mu t' mu', step t mu t' mu' -> step (Succ t) mu (Succ t') mu'
  | S_PredZero : forall mu, step (Pred (Num 0)) mu (Num 0) mu
  | S_PredSucc : forall n mu, step (Pred (Num (S n))) mu (Num n) mu
  | S_Pred : forall t mu t' mu', step t mu t' mu' -> step (Pred t) mu (Pred t') mu'
  | S_IsZeroZero : forall mu, step (IsZero (Num 0)) mu (BOOL true) mu
  | S_IsZeroSucc : forall n mu, step (IsZero (Num (S n))) mu (BOOL false) mu
  | S_IsZero : forall t mu t' mu', step t mu t' mu' -> step (IsZero t) mu (IsZero t') mu'
  | S_IfTrue : forall t1 t2 mu, step (If (BOOL true) t1 t2) mu t1 mu
  | S_IfFalse : forall t1 t2 mu, step (If (BOOL false) t1 t2) mu t2 mu
  | S_If : forall t1 mu t1' mu' t2 t3, step t1 mu t1' mu' -> step (If t1 t2 t3) mu (If t1' t2 t3) mu'
  | S_App1 : forall t1 mu t1' mu' t2, step t1 mu t1' mu' -> step (App t1 t2) mu (App t1' t2) mu'
  | S_App2 : forall v1 t2 mu t2' mu', value v1 -> step t2 mu t2' mu' -> step (App v1 t2) mu (App v1 t2') mu'
  | S_AppAbs : forall T t1 v2 mu, value v2 -> step (App (Lam T t1) v2) mu (subst 0 v2 t1) mu
  | S_Fix : forall t mu, step (Fix t) mu (subst 0 (Fix t) t) mu
  | S_Ref : forall t mu t' mu', step t mu t' mu' -> step (Ref t) mu (Ref t') mu'
  | S_RefV : forall v mu, value v -> step (Ref v) mu (Loc (length mu)) ((length mu, v) :: mu)
  | S_Deref : forall t mu t' mu', step t mu t' mu' -> step (Deref t) mu (Deref t') mu'
  | S_DerefLoc : forall l mu v, heap_lookup l mu = Some v -> step (Deref (Loc l)) mu v mu
  | S_Assign1 : forall t1 mu t1' mu' t2, step t1 mu t1' mu' -> step (Assign t1 t2) mu (Assign t1' t2) mu'
  | S_Assign2 : forall l t2 mu t2' mu', step t2 mu t2' mu' -> step (Assign (Loc l) t2) mu (Assign (Loc l) t2') mu'
  | S_AssignV : forall l v mu, value v -> step (Assign (Loc l) v) mu (Num 0) (heap_update l v mu).

Definition extends (S' S : store_ty) : Prop := exists S2, S' = S ++ S2.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)


Lemma extends_refl : forall S, extends S S.
Proof.
intros S.
unfold extends; exists nil; rewrite app_nil_r; reflexivity.
Qed.


Lemma store_weaken_ty : forall G S t T, has_type G S t T -> forall S', extends S' S -> has_type G S' t T.
Proof.
intros G S t T H; induction H; intros S' Hext; try (econstructor; eauto).
unfold extends in Hext; destruct Hext as [S2 Heq]; subst S'; rewrite nth_error_app1 by (apply nth_error_Some; rewrite H; discriminate); exact H.
Qed.


Lemma store_weaken_heap : forall mu S, heap_ok mu S -> forall S', extends S' S -> heap_ok mu S'.
Proof.
intros mu S H; induction H; intros S' Hext; try (econstructor; eauto using store_weaken_ty).
unfold extends in Hext; destruct Hext as [S2 Heq]; subst S'; rewrite nth_error_app1 by (apply nth_error_Some; rewrite H1; discriminate); exact H1.
Qed.


Lemma weaken_app_r : forall G S t T, has_type G S t T -> forall G', has_type (G ++ G') S t T.
Proof.
intros G S t T H; induction H; intros G'; try (econstructor; eauto).
rewrite nth_error_app1 by (apply nth_error_Some; rewrite H; discriminate); exact H.
Qed.


Lemma shift_closed_gen : forall G S t T, has_type G S t T -> forall d, length G <= d -> shift_at d t = t.
Proof.
intros G S t T H; induction H; intros d Hd; simpl; try (f_equal; solve [reflexivity | apply IHhas_type; lia | apply IHhas_type1; lia | apply IHhas_type2; lia | apply IHhas_type3; lia]); try reflexivity.
assert (Hxd : x <? d = true) by (apply Nat.ltb_lt; apply Nat.lt_le_trans with (length G); [ apply nth_error_Some; rewrite H; discriminate | exact Hd ]); rewrite Hxd; reflexivity.
f_equal; apply IHhas_type; simpl; lia.
f_equal; apply IHhas_type; simpl; lia.
Qed.


Lemma subst_lemma : forall t G1 U S u T, has_type (G1 ++ (U :: nil)) S t T -> has_type nil S u U -> has_type G1 S (subst (length G1) u t) T.
Proof.
intros t; induction t; intros G1 U S u T Hty Hu; inversion Hty; subst; simpl; try (econstructor; eauto).
destruct (Nat.eqb_spec n (length G1)) as [Heq | Hne].
subst n; rewrite nth_error_app2 in H2 by lia; rewrite Nat.sub_diag in H2; simpl in H2; injection H2 as H2; subst; change G1 with (nil ++ G1); apply weaken_app_r; exact Hu.
apply T_Var; assert (Hlt : n < length G1) by (assert (Hb : n < length (G1 ++ [U])) by (apply nth_error_Some; rewrite H2; discriminate); rewrite app_length in Hb; simpl in Hb; lia); rewrite nth_error_app1 in H2 by exact Hlt; exact H2.
assert (Hsh : shift u = u) by (unfold shift; apply (shift_closed_gen nil S u U Hu 0); simpl; lia); rewrite Hsh; apply (IHt (t :: G1) U S u T2); [ exact H4 | exact Hu ].
assert (Hsh : shift u = u) by (unfold shift; apply (shift_closed_gen nil S u U Hu 0); simpl; lia); rewrite Hsh; apply (IHt (T :: G1) U S u T); [ exact H2 | exact Hu ].
Qed.


Lemma heap_lookup_type : forall mu S l v T, heap_ok mu S -> heap_lookup l mu = Some v -> nth_error S l = Some T -> has_type nil S v T.
Proof.
intros mu S l v T Hheap; revert v T; induction Hheap as [S0 | l0 v0 mu0 S0 T0 Hheap IH Hty0 Hnth0]; intros v T Hlk Hnth; simpl in Hlk; [ discriminate Hlk | destruct (l =? l0) eqn:Heqb; [ apply Nat.eqb_eq in Heqb; subst l0; injection Hlk as Hlk; subst v; rewrite Hnth0 in Hnth; injection Hnth as Hnth; subst T; exact Hty0 | apply (IH v T Hlk Hnth) ] ].
Qed.


Lemma heap_ok_update : forall mu S l v T, heap_ok mu S -> has_type nil S v T -> nth_error S l = Some T -> heap_ok (heap_update l v mu) S.
Proof.
intros mu S l v T Hheap; induction Hheap as [S0 | l0 v0 mu0 S0 T0 Hheap IH Hty0 Hnth0]; intros Hv Hnth; simpl; [ apply heap_empty | destruct (l =? l0) eqn:Heqb; [ apply heap_cons with (T := T); [ exact Hheap | exact Hv | exact Hnth ] | apply heap_cons with (T := T0); [ apply IH; [ exact Hv | exact Hnth ] | exact Hty0 | exact Hnth0 ] ] ].
Qed.

Theorem preservation :
  forall t mu t' mu' T S,
    has_type [] S t T ->
    step t mu t' mu' ->
    heap_ok mu S ->
    length mu >= length S ->
    exists S',
      extends S' S /\
      heap_ok mu' S' /\
      has_type [] S' t' T.
Proof.
  intros t mu t' mu' T0 S0 Hty Hstep Hheap Hlen; revert T0 S0 Hty Hheap Hlen; induction Hstep; intros T0 S0 Hty Hheap Hlen; inversion Hty; subst.
  { (* S_Succ:8e7eacf0 *) solve [ destruct (IHHstep _ S0 ltac:(eassumption) Hheap Hlen) as [SS [Hext [Hheap' Hty']]]; exists SS; split; [exact Hext | split; [exact Hheap' | econstructor; eauto using store_weaken_ty ]] ]. }
  { (* S_PredZero:5ed523ea *) solve [ exists S0; split; [apply extends_refl | split; [exact Hheap | solve [assumption | econstructor; eauto] ]] ]. }
  { (* S_PredSucc:def6678d *) solve [ exists S0; split; [apply extends_refl | split; [exact Hheap | solve [assumption | econstructor; eauto] ]] ]. }
  { (* S_Pred:d1571abd *) solve [ destruct (IHHstep _ S0 ltac:(eassumption) Hheap Hlen) as [SS [Hext [Hheap' Hty']]]; exists SS; split; [exact Hext | split; [exact Hheap' | econstructor; eauto using store_weaken_ty ]] ]. }
  { (* S_IsZeroZero:0c5c638d *) solve [ exists S0; split; [apply extends_refl | split; [exact Hheap | solve [assumption | econstructor; eauto] ]] ]. }
  { (* S_IsZeroSucc:e2cb072c *) solve [ exists S0; split; [apply extends_refl | split; [exact Hheap | solve [assumption | econstructor; eauto] ]] ]. }
  { (* S_IsZero:35b0949d *) solve [ destruct (IHHstep _ S0 ltac:(eassumption) Hheap Hlen) as [SS [Hext [Hheap' Hty']]]; exists SS; split; [exact Hext | split; [exact Hheap' | econstructor; eauto using store_weaken_ty ]] ]. }
  { (* S_IfTrue:e2855274 *) solve [ exists S0; split; [apply extends_refl | split; [exact Hheap | solve [assumption | econstructor; eauto] ]] ]. }
  { (* S_IfFalse:0b2c15cd *) solve [ exists S0; split; [apply extends_refl | split; [exact Hheap | solve [assumption | econstructor; eauto] ]] ]. }
  { (* S_If:e4733374 *) solve [ destruct (IHHstep _ S0 ltac:(eassumption) Hheap Hlen) as [SS [Hext [Hheap' Hty']]]; exists SS; split; [exact Hext | split; [exact Hheap' | econstructor; eauto using store_weaken_ty ]] ]. }
  { (* S_App1:850d5fd9 *) solve [ destruct (IHHstep _ S0 ltac:(eassumption) Hheap Hlen) as [SS [Hext [Hheap' Hty']]]; exists SS; split; [exact Hext | split; [exact Hheap' | econstructor; eauto using store_weaken_ty ]] ]. }
  { (* S_App2:39a35521 *) solve [ destruct (IHHstep _ S0 ltac:(eassumption) Hheap Hlen) as [SS [Hext [Hheap' Hty']]]; exists SS; split; [exact Hext | split; [exact Hheap' | econstructor; eauto using store_weaken_ty ]] ]. }
  { (* S_AppAbs:dc04e8a2 *) match goal with H : has_type [] S0 (Lam _ _) _ |- _ => inversion H; subst end; exists S0; split; [ apply extends_refl | split; [ exact Hheap | eapply subst_lemma; [ simpl; eassumption | eassumption ] ] ].
  }
  { (* S_Fix:68f6aff8 *) exists S0; split; [ apply extends_refl | split; [ exact Hheap | eapply subst_lemma; [ simpl; exact H2 | exact Hty ] ] ].
  }
  { (* S_Ref:80b292c6 *) solve [ destruct (IHHstep _ S0 ltac:(eassumption) Hheap Hlen) as [SS [Hext [Hheap' Hty']]]; exists SS; split; [exact Hext | split; [exact Hheap' | econstructor; eauto using store_weaken_ty ]] ]. }
  { (* S_RefV:2af84cff *) assert (Hext : extends ((S0 ++ repeat TyNat (length mu - length S0)) ++ [T]) S0) by (unfold extends; exists (repeat TyNat (length mu - length S0) ++ [T]); rewrite app_assoc; reflexivity); assert (Hlenpad : length (S0 ++ repeat TyNat (length mu - length S0)) = length mu) by (rewrite app_length, repeat_length; lia); assert (Hnthloc : nth_error ((S0 ++ repeat TyNat (length mu - length S0)) ++ [T]) (length mu) = Some T) by (rewrite nth_error_app2 by (rewrite Hlenpad; lia); rewrite Hlenpad, Nat.sub_diag; reflexivity); exists ((S0 ++ repeat TyNat (length mu - length S0)) ++ [T]); split; [ exact Hext | split; [ apply heap_cons with (T := T); [ apply (store_weaken_heap mu S0 Hheap _ Hext) | apply (store_weaken_ty [] S0 v T H3 _ Hext) | exact Hnthloc ] | apply T_Loc; exact Hnthloc ] ].
  }
  { (* S_Deref:0d1ebd03 *) solve [ destruct (IHHstep _ S0 ltac:(eassumption) Hheap Hlen) as [SS [Hext [Hheap' Hty']]]; exists SS; split; [exact Hext | split; [exact Hheap' | econstructor; eauto using store_weaken_ty ]] ]. }
  { (* S_DerefLoc:b0b97791 *) inversion H3; subst; exists S0; split; [ apply extends_refl | split; [ exact Hheap | apply (heap_lookup_type mu S0 l v T0 Hheap H); assumption ] ].
  }
  { (* S_Assign1:fbdfea85 *) solve [ destruct (IHHstep _ S0 ltac:(eassumption) Hheap Hlen) as [SS [Hext [Hheap' Hty']]]; exists SS; split; [exact Hext | split; [exact Hheap' | econstructor; eauto using store_weaken_ty ]] ]. }
  { (* S_Assign2:0a3ed0c9 *) solve [ destruct (IHHstep _ S0 ltac:(eassumption) Hheap Hlen) as [SS [Hext [Hheap' Hty']]]; exists SS; split; [exact Hext | split; [exact Hheap' | econstructor; eauto using store_weaken_ty ]] ]. }
  { (* S_AssignV:eafaeec6 *) inversion H4; subst; exists S0; split; [ apply extends_refl | split; [ apply (heap_ok_update mu S0 l v T Hheap H6); assumption | apply T_Num ] ].
  }
Qed.

Theorem preservation_neg : ~ (
  forall t mu t' mu' T S,
    has_type [] S t T ->
    step t mu t' mu' ->
    heap_ok mu S ->
    length mu >= length S ->
    exists S',
      extends S' S /\
      heap_ok mu' S' /\
      has_type [] S' t' T).
Proof.
Admitted.
