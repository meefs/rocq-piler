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
Proof.
unfold extends; intros; exists []; rewrite app_nil_r; reflexivity.
Qed.


Lemma extends_trans : forall S1 S2 S3, extends S2 S1 -> extends S3 S2 -> extends S3 S1.
Proof.
unfold extends; intros S1 S2 S3 [S12 H12] [S23 H23]; exists (S12 ++ S23); subst; rewrite app_assoc; reflexivity.
Qed.


Lemma nth_error_extends : forall S S' l T, nth_error S l = Some T -> extends S' S -> nth_error S' l = Some T.
Proof.
unfold extends; intros S S' l T Hnth [S2 Heq]; subst; rewrite nth_error_app1; auto; apply nth_error_Some; congruence.
Qed.


Lemma store_weakening : forall G S t T, has_type G S t T -> forall S', extends S' S -> has_type G S' t T.
Proof.
intros G S t T Hty; induction Hty; intros S' Hext; try (econstructor; eauto using nth_error_extends).
Qed.


Lemma shift_typing : forall G1 G2 S t T U, has_type (G1 ++ G2) S t T -> has_type (G1 ++ U :: G2) S (shift_at (length G1) t) T.
Proof.
  intros G1 G2 S t T U Hty; remember (G1 ++ G2) as G eqn:HeqG; revert G1 G2 U HeqG; induction Hty; intros G0 G2' U0 HeqG; subst; simpl.
  { (* T_Var:5bbb415e *) destruct (Nat.ltb_spec x (length G0)); apply T_Var; [ rewrite nth_error_app1 in *; auto; rewrite nth_error_app1; auto | rewrite nth_error_app2 in H by lia; rewrite nth_error_app2 by lia; replace (x + 1 - length G0) with (Datatypes.S (x - length G0)) by lia; simpl; auto ].
  }
  { (* T_Num:1053672d *) solve [ econstructor; eauto ]. }
  { (* T_Bool:5cb00524 *) solve [ econstructor; eauto ]. }
  { (* T_Succ:3eb45563 *) solve [ econstructor; eauto ]. }
  { (* T_Pred:a96873ce *) solve [ econstructor; eauto ]. }
  { (* T_IsZero:afbac220 *) solve [ econstructor; eauto ]. }
  { (* T_If:c50f215a *) solve [ econstructor; eauto ]. }
  { (* T_Lam:869824ee *) solve [ constructor; apply IHHty with (G1 := T1 :: G0) (G2 := G2'); simpl; auto ]. }
  { (* T_App:efea925a *) solve [ econstructor; eauto ]. }
  { (* T_Fix:22963b78 *) solve [ constructor; apply IHHty with (G1 := T :: G0) (G2 := G2'); simpl; auto ]. }
  { (* T_Ref:0cce2f95 *) solve [ econstructor; eauto ]. }
  { (* T_Deref:7d61e9d3 *) solve [ econstructor; eauto ]. }
  { (* T_Assign:c0ddd6cf *) solve [ econstructor; eauto ]. }
  { (* T_Loc:cdafd02c *) solve [ econstructor; eauto ]. }
Qed.

Lemma subst_typing : forall G S t T, has_type G S t T -> forall G1 U s, G = G1 ++ U :: nil -> has_type G1 S s U -> has_type G1 S (subst (length G1) s t) T.
Proof.
  intros G S t T Hty; induction Hty; intros G1 U0 s0 HeqG Hs.
  { (* T_Var:03204c71 *) subst; simpl; destruct (Nat.eqb_spec x (length G1)); [ subst; rewrite nth_error_app2 in H by lia; replace (length G1 - length G1) with 0 in H by lia; simpl in H; inversion H; subst; auto | apply T_Var; assert (x < length G1) by (destruct (Nat.lt_ge_cases x (length G1)); auto; exfalso; rewrite nth_error_app2 in H by lia; destruct (x - length G1) as [|[|k]] eqn:?; [lia | simpl in H; discriminate | simpl in H; discriminate ]); rewrite nth_error_app1 in H by auto; auto ].
  }
  { (* T_Num:cdd71c72 *) solve [ econstructor; eauto ]. }
  { (* T_Bool:c6504f68 *) solve [ econstructor; eauto ]. }
  { (* T_Succ:1d76d1f5 *) solve [ econstructor; eauto ]. }
  { (* T_Pred:fed74404 *) solve [ econstructor; eauto ]. }
  { (* T_IsZero:a35d6fd7 *) solve [ econstructor; eauto ]. }
  { (* T_If:f4f6ef26 *) solve [ econstructor; eauto ]. }
  { (* T_Lam:f8522300 *) subst; simpl; apply T_Lam; apply IHHty with (U := U0); [ rewrite <- app_comm_cons; auto | apply (shift_typing nil G1 S s0 U0 T1); simpl; auto ].
  }
  { (* T_App:b6346d3f *) solve [ econstructor; eauto ]. }
  { (* T_Fix:bacf224b *) subst; simpl; apply T_Fix; apply IHHty with (U := U0); [ rewrite <- app_comm_cons; auto | apply (shift_typing nil G1 S s0 U0 T); simpl; auto ].
  }
  { (* T_Ref:900cdf7e *) solve [ econstructor; eauto ]. }
  { (* T_Deref:19663764 *) solve [ econstructor; eauto ]. }
  { (* T_Assign:5987a96c *) solve [ econstructor; eauto ]. }
  { (* T_Loc:eb62760e *) solve [ econstructor; eauto ]. }
Qed.


Lemma heap_ok_extends : forall mu S S', heap_ok mu S -> extends S' S -> heap_ok mu S'.
Proof.
intros mu S S' Hok Hext; induction Hok; [ constructor | econstructor; eauto using store_weakening, nth_error_extends ].
Qed.


Lemma heap_lookup_has_type : forall mu S l v T, heap_ok mu S -> heap_lookup l mu = Some v -> nth_error S l = Some T -> has_type [] S v T.
Proof.
intros mu S l v T Hok; revert l v T; induction Hok; intros l0 v0 T0 Hlookup Hnth; [ simpl in Hlookup; discriminate | simpl in Hlookup; destruct (Nat.eqb_spec l0 l); [ inversion Hlookup; subst; congruence | eauto ] ].
Qed.


Lemma heap_ok_update : forall mu S l v T, heap_ok mu S -> has_type [] S v T -> nth_error S l = Some T -> heap_ok (heap_update l v mu) S.
Proof.
intros mu S l v T Hok Hty Hnth; induction Hok; simpl; [ constructor | destruct (Nat.eqb_spec l l0); [ subst; econstructor; eauto | econstructor; eauto ] ].
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
  intros t mu t' mu' T S Hty Hstep Hok Hlen; revert T S Hty Hok Hlen; induction Hstep; intros T0 S0 Hty Hok Hlen.
  { (* S_Succ:58387bbc *) solve [ inversion Hty; subst; edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto; exists S'; split; [ auto | split; [ auto | econstructor; eauto using store_weakening ] ] ]. }
  { (* S_PredZero:3961c05a *) solve [ inversion Hty; subst; exists S0; split; [ apply extends_refl | split; [ auto | constructor; auto ] ] ]. }
  { (* S_PredSucc:dc5b51a6 *) solve [ inversion Hty; subst; exists S0; split; [ apply extends_refl | split; [ auto | constructor; auto ] ] ]. }
  { (* S_Pred:060efb54 *) solve [ inversion Hty; subst; edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto; exists S'; split; [ auto | split; [ auto | econstructor; eauto using store_weakening ] ] ]. }
  { (* S_IsZeroZero:1253d94b *) solve [ inversion Hty; subst; exists S0; split; [ apply extends_refl | split; [ auto | constructor; auto ] ] ]. }
  { (* S_IsZeroSucc:db5ccf76 *) solve [ inversion Hty; subst; exists S0; split; [ apply extends_refl | split; [ auto | constructor; auto ] ] ]. }
  { (* S_IsZero:a2050d3f *) solve [ inversion Hty; subst; edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto; exists S'; split; [ auto | split; [ auto | econstructor; eauto using store_weakening ] ] ]. }
  { (* S_IfTrue:e2855274 *) solve [ inversion Hty; subst; exists S0; split; [ apply extends_refl | split; [ auto | auto ] ] ]. }
  { (* S_IfFalse:0b2c15cd *) solve [ inversion Hty; subst; exists S0; split; [ apply extends_refl | split; [ auto | auto ] ] ]. }
  { (* S_If:e4733374 *) solve [ inversion Hty; subst; edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto; exists S'; split; [ auto | split; [ auto | econstructor; eauto using store_weakening ] ] ]. }
  { (* S_App1:850d5fd9 *) solve [ inversion Hty; subst; edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto; exists S'; split; [ auto | split; [ auto | econstructor; eauto using store_weakening ] ] ]. }
  { (* S_App2:39a35521 *) solve [ inversion Hty; subst; edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto; exists S'; split; [ auto | split; [ auto | econstructor; eauto using store_weakening ] ] ]. }
  { (* S_AppAbs:dc04e8a2 *) inversion Hty; subst; inversion H4; subst; exists S0; split; [ apply extends_refl | split; [ auto | eapply subst_typing; eauto; simpl; auto ] ].
  }
  { (* S_Fix:68f6aff8 *) solve [ inversion Hty; subst; exists S0; split; [ apply extends_refl | split; [ auto | eapply subst_typing; eauto; simpl; auto ] ] ]. }
  { (* S_Ref:7841fed7 *) solve [ inversion Hty; subst; edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto; exists S'; split; [ auto | split; [ auto | econstructor; eauto using store_weakening ] ] ]. }
  { (* S_RefV:8dedfc67 *) inversion Hty; subst; exists (S0 ++ repeat TyNat (length mu - length S0) ++ [T]); assert (Hnth: nth_error (S0 ++ repeat TyNat (length mu - length S0) ++ [T]) (length mu) = Some T) by ( rewrite nth_error_app2 by lia; rewrite nth_error_app2 by (rewrite repeat_length; lia); rewrite repeat_length; replace (length mu - length S0 - (length mu - length S0)) with 0 by lia; simpl; reflexivity); assert (Hext: extends (S0 ++ repeat TyNat (length mu - length S0) ++ [T]) S0) by (unfold extends; eexists; reflexivity); split; [ auto | split; [ econstructor; [ eapply heap_ok_extends; eauto | eapply store_weakening; eauto | auto ] | apply T_Loc; auto ] ].
  }
  { (* S_Deref:0d1ebd03 *) solve [ inversion Hty; subst; edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto; exists S'; split; [ auto | split; [ auto | econstructor; eauto using store_weakening ] ] ]. }
  { (* S_DerefLoc:b0b97791 *) inversion Hty; subst; inversion H3; subst; exists S0; split; [ apply extends_refl | split; [ auto | eapply heap_lookup_has_type; eauto ] ].
  }
  { (* S_Assign1:8574e98b *) solve [ inversion Hty; subst; edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto; exists S'; split; [ auto | split; [ auto | econstructor; eauto using store_weakening ] ] ]. }
  { (* S_Assign2:d2034227 *) solve [ inversion Hty; subst; edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto; exists S'; split; [ auto | split; [ auto | econstructor; eauto using store_weakening ] ] ]. }
  { (* S_AssignV:fc5cb456 *) inversion Hty; subst; inversion H4; subst; exists S0; split; [ apply extends_refl | split; [ eapply heap_ok_update; eauto | constructor ] ].
  }
Qed.
