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

Lemma extends_refl : forall S, extends S S.
Proof. intros S. exists []. rewrite app_nil_r. reflexivity. Qed.

Lemma extends_app : forall S S2, extends (S ++ S2) S.
Proof. intros. exists S2. reflexivity. Qed.

Lemma extends_nth_error : forall S' S l T,
  extends S' S -> nth_error S l = Some T -> nth_error S' l = Some T.
Proof.
  intros S' S l T [S2 HS] Hnth. subst.
  assert (l < length S) by (apply nth_error_Some; rewrite Hnth; discriminate).
  rewrite nth_error_app1 by assumption. assumption.
Qed.

Lemma weaken_append : forall G S t T,
  has_type G S t T -> forall G', has_type (G ++ G') S t T.
Proof.
  intros G S t T H. induction H; intros G'; simpl.
  - apply T_Var. assert (x < length G) by (apply nth_error_Some; rewrite H; discriminate).
    rewrite nth_error_app1 by assumption. assumption.
  - apply T_Num.
  - apply T_Bool.
  - apply T_Succ; auto.
  - apply T_Pred; auto.
  - apply T_IsZero; auto.
  - apply T_If; auto.
  - apply T_Lam. apply (IHhas_type G').
  - eapply T_App; eauto.
  - apply T_Fix. apply (IHhas_type G').
  - apply T_Ref; auto.
  - eapply T_Deref; eauto.
  - eapply T_Assign; eauto.
  - apply T_Loc; assumption.
Qed.

Lemma has_type_store_weaken : forall G S t T,
  has_type G S t T -> forall S', extends S' S -> has_type G S' t T.
Proof.
  intros G S t T H. induction H; intros S' Hext.
  - apply T_Var; assumption.
  - apply T_Num.
  - apply T_Bool.
  - apply T_Succ; auto.
  - apply T_Pred; auto.
  - apply T_IsZero; auto.
  - apply T_If; auto.
  - apply T_Lam; auto.
  - eapply T_App; eauto.
  - apply T_Fix; auto.
  - apply T_Ref; auto.
  - eapply T_Deref; eauto.
  - eapply T_Assign; eauto.
  - apply T_Loc. eapply extends_nth_error; eauto.
Qed.

Lemma heap_ok_store_weaken : forall mu S,
  heap_ok mu S -> forall S', extends S' S -> heap_ok mu S'.
Proof.
  intros mu S H. induction H; intros S' Hext.
  - apply heap_empty.
  - eapply heap_cons.
    + apply IHheap_ok; assumption.
    + eapply has_type_store_weaken; eauto.
    + eapply extends_nth_error; eauto.
Qed.

Lemma heap_lookup_typed : forall mu S,
  heap_ok mu S -> forall l v T,
  heap_lookup l mu = Some v -> nth_error S l = Some T -> has_type [] S v T.
Proof.
  intros mu S H. induction H; intros l0 v0 T0 Hlk Hnth.
  - simpl in Hlk. discriminate.
  - simpl in Hlk. destruct (Nat.eqb l0 l) eqn:E.
    + apply Nat.eqb_eq in E. subst l0. inversion Hlk; subst v0.
      rewrite Hnth in H1. inversion H1; subst T0. assumption.
    + eapply IHheap_ok; eauto.
Qed.

Lemma heap_update_ok : forall mu S,
  heap_ok mu S -> forall l v T,
  has_type [] S v T -> nth_error S l = Some T -> heap_ok (heap_update l v mu) S.
Proof.
  intros mu S H. induction H; intros l0 v0 T0 Hv Hnth.
  - simpl. apply heap_empty.
  - simpl. destruct (Nat.eqb l0 l) eqn:E.
    + apply Nat.eqb_eq in E. subst l0.
      eapply heap_cons; eassumption.
    + eapply heap_cons.
      * eapply IHheap_ok; eassumption.
      * eassumption.
      * eassumption.
Qed.

Lemma shift_closed : forall G S t T,
  has_type G S t T -> shift_at (length G) t = t.
Proof.
  intros G S t T H. induction H; simpl;
    try reflexivity;
    try (rewrite IHhas_type1, IHhas_type2, IHhas_type3; reflexivity);
    try (rewrite IHhas_type1, IHhas_type2; reflexivity);
    try (simpl in IHhas_type; rewrite IHhas_type; reflexivity).
  assert (Hlt : x < length G) by (apply nth_error_Some; rewrite H; discriminate).
  apply Nat.ltb_lt in Hlt. rewrite Hlt. reflexivity.
Qed.

Lemma subst_lemma : forall t G1 U S T v,
  has_type (G1 ++ [U]) S t T ->
  has_type [] S v U ->
  has_type G1 S (subst (length G1) v t) T.
Proof.
  induction t; intros G1 U S T v Ht Hv; simpl; inversion Ht; subst.
  - destruct (n =? length G1) eqn:E; [ apply Nat.eqb_eq in E; subst n; rewrite nth_error_app2 in H2 by lia; rewrite Nat.sub_diag in H2; simpl in H2; inversion H2; subst; change G1 with ([] ++ G1); apply weaken_append; assumption | apply Nat.eqb_neq in E; apply T_Var; assert (Hb : n < length (G1 ++ [U])) by (apply nth_error_Some; rewrite H2; discriminate); rewrite app_length in Hb; simpl in Hb; assert (n < length G1) by lia; rewrite nth_error_app1 in H2 by assumption; assumption ].
  - apply T_Num.
  - apply T_Bool.
  - apply T_Succ; eapply IHt; eassumption.
  - apply T_Pred; eapply IHt; eassumption.
  - apply T_IsZero; eapply IHt; eassumption.
  - apply T_If; [eapply IHt1 | eapply IHt2 | eapply IHt3]; eassumption.
  - apply T_Lam; assert (Hs : shift v = v) by (unfold shift; apply (shift_closed [] S v U Hv)); rewrite Hs; apply (IHt (t :: G1) U S T2 v); [ exact H4 | exact Hv ].
  - eapply T_App; [eapply IHt1 | eapply IHt2]; eassumption.
  - apply T_Fix; assert (Hs : shift v = v) by (unfold shift; apply (shift_closed [] S v U Hv)); rewrite Hs; apply (IHt (T :: G1) U S T v); [ exact H2 | exact Hv ].
  - apply T_Ref; eapply IHt; eassumption.
  - apply T_Deref; eapply IHt; eassumption.
  - eapply T_Assign; [eapply IHt1 | eapply IHt2]; eassumption.
  - apply T_Loc; exact H2.
Qed.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

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
  intros t mu t' mu' T S Hty Hstep Hheap Hlen; revert T S Hty Hheap Hlen; induction Hstep; intros T0 S0 Hty Hheap Hlen; inversion Hty; subst.
  { (* S_Succ:8e7eacf0 *) destruct (IHHstep TyNat S0 H2 Hheap Hlen) as [S' [Hext [Hok Hty']]]; exists S'; repeat split; [exact Hext | exact Hok | apply T_Succ; exact Hty'].
  }
  { (* S_PredZero:5ed523ea *) solve [ exists S0; repeat split; [apply extends_refl | assumption | econstructor; eassumption] ]. }
  { (* S_PredSucc:def6678d *) solve [ exists S0; repeat split; [apply extends_refl | assumption | econstructor; eassumption] ]. }
  { (* S_Pred:d1571abd *) destruct (IHHstep TyNat S0 H2 Hheap Hlen) as [S' [Hext [Hok Hty']]]; exists S'; repeat split; [exact Hext | exact Hok | apply T_Pred; exact Hty'].
  }
  { (* S_IsZeroZero:0c5c638d *) solve [ exists S0; repeat split; [apply extends_refl | assumption | econstructor; eassumption] ]. }
  { (* S_IsZeroSucc:e2cb072c *) solve [ exists S0; repeat split; [apply extends_refl | assumption | econstructor; eassumption] ]. }
  { (* S_IsZero:35b0949d *) destruct (IHHstep TyNat S0 H2 Hheap Hlen) as [S' [Hext [Hok Hty']]]; exists S'; repeat split; [exact Hext | exact Hok | apply T_IsZero; exact Hty'].
  }
  { (* S_IfTrue:e2855274 *) exists S0; repeat split; [apply extends_refl | exact Hheap | exact H6].
  }
  { (* S_IfFalse:0b2c15cd *) exists S0; repeat split; [apply extends_refl | exact Hheap | exact H7].
  }
  { (* S_If:e4733374 *) destruct (IHHstep TyBool S0 H4 Hheap Hlen) as [S' [Hext [Hok Hty']]]; exists S'; repeat split; [exact Hext | exact Hok | apply T_If; [exact Hty' | eapply has_type_store_weaken; [exact H6 | exact Hext] | eapply has_type_store_weaken; [exact H7 | exact Hext]]].
  }
  { (* S_App1:850d5fd9 *) destruct (IHHstep (TyArrow T1 T0) S0 H3 Hheap Hlen) as [S' [Hext [Hok Hty']]]; exists S'; repeat split; [exact Hext | exact Hok | eapply T_App; [exact Hty' | eapply has_type_store_weaken; [exact H5 | exact Hext]]].
  }
  { (* S_App2:39a35521 *) destruct (IHHstep T1 S0 H6 Hheap Hlen) as [S' [Hext [Hok Hty']]]; exists S'; repeat split; [exact Hext | exact Hok | eapply T_App; [eapply has_type_store_weaken; [exact H4 | exact Hext] | exact Hty']].
  }
  { (* S_AppAbs:dc04e8a2 *) inversion H4; subst; exists S0; repeat split; [apply extends_refl | exact Hheap | eapply (subst_lemma t1 []); eassumption].
  }
  { (* S_Fix:68f6aff8 *) exists S0; repeat split; [apply extends_refl | exact Hheap | eapply (subst_lemma t []); [exact H2 | apply T_Fix; exact H2]].
  }
  { (* S_Ref:80b292c6 *) destruct (IHHstep T S0 H2 Hheap Hlen) as [S' [Hext [Hok Hty']]]; exists S'; repeat split; [exact Hext | exact Hok | apply T_Ref; exact Hty'].
  }
  { (* S_RefV:2af84cff *) exists ((S0 ++ repeat TyNat (length mu - length S0)) ++ [T]); assert (Hlenpad : length (S0 ++ repeat TyNat (length mu - length S0)) = length mu) by (rewrite app_length, repeat_length; lia); assert (Hext : extends ((S0 ++ repeat TyNat (length mu - length S0)) ++ [T]) S0) by (exists (repeat TyNat (length mu - length S0) ++ [T]); rewrite app_assoc; reflexivity); repeat split; [ exact Hext | eapply heap_cons; [ eapply heap_ok_store_weaken; [exact Hheap | exact Hext] | eapply has_type_store_weaken; [exact H3 | exact Hext] | rewrite nth_error_app2 by lia; rewrite Hlenpad; rewrite Nat.sub_diag; reflexivity ] | apply T_Loc; rewrite nth_error_app2 by lia; rewrite Hlenpad; rewrite Nat.sub_diag; reflexivity ].
  }
  { (* S_Deref:0d1ebd03 *) destruct (IHHstep (TyRef T0) S0 H2 Hheap Hlen) as [S' [Hext [Hok Hty']]]; exists S'; repeat split; [exact Hext | exact Hok | apply T_Deref; exact Hty'].
  }
  { (* S_DerefLoc:b0b97791 *) inversion H3; subst; exists S0; repeat split; [apply extends_refl | exact Hheap | eapply heap_lookup_typed; [exact Hheap | exact H | eassumption]].
  }
  { (* S_Assign1:fbdfea85 *) destruct (IHHstep (TyRef T) S0 H3 Hheap Hlen) as [S' [Hext [Hok Hty']]]; exists S'; repeat split; [exact Hext | exact Hok | eapply T_Assign; [exact Hty' | eapply has_type_store_weaken; [exact H5 | exact Hext]]].
  }
  { (* S_Assign2:0a3ed0c9 *) destruct (IHHstep T S0 H5 Hheap Hlen) as [S' [Hext [Hok Hty']]]; exists S'; repeat split; [exact Hext | exact Hok | eapply T_Assign; [eapply has_type_store_weaken; [exact H3 | exact Hext] | exact Hty']].
  }
  { (* S_AssignV:eafaeec6 *) inversion H4; subst; exists S0; repeat split; [apply extends_refl | eapply heap_update_ok; [exact Hheap | exact H6 | eassumption] | apply T_Num].
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
