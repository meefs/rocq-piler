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


Lemma extends_refl : forall S : store_ty, extends S S.
Proof.
intros S; exists []; rewrite app_nil_r; reflexivity.
Qed.


Lemma extends_nth_error : forall (S' S : store_ty) l T, extends S' S -> nth_error S l = Some T -> nth_error S' l = Some T.
Proof.
intros S' S l T [S2 ->] H; rewrite nth_error_app1; [ exact H | apply nth_error_Some; congruence ].
Qed.


Lemma has_type_extends : forall G S t T, has_type G S t T -> forall S', extends S' S -> has_type G S' t T.
Proof.
induction 1; intros; econstructor; eauto using extends_nth_error.
Qed.


Lemma heap_ok_extends : forall mu S, heap_ok mu S -> forall S', extends S' S -> heap_ok mu S'.
Proof.
induction 1; intros; econstructor; eauto using has_type_extends, extends_nth_error.
Qed.


Lemma shift_at_preserves : forall G S t T, has_type G S t T -> forall G1 U G2, G = G1 ++ G2 -> has_type (G1 ++ U :: G2) S (shift_at (length G1) t) T.
Proof.
  induction 1; intros G1 U G2 HeqG; subst; simpl.
  { (* T_Var:eb261139 *) destruct (Nat.ltb_spec x (length G1)); simpl.
    { (* case_1:4659ce18 *) solve [ constructor; rewrite nth_error_app1 in * by assumption; assumption ]. }
    { (* case_2:bc8aed7a *) apply T_Var.
      { (* case_1:a058bc74 *) solve [ rewrite nth_error_app2 by lia; rewrite nth_error_app2 in H by lia; rewrite Nat.add_1_r, Nat.sub_succ_l by lia; simpl; assumption ]. }
    }
  }
  { (* T_Num:50d832a0 *) solve [ econstructor; eauto ]. }
  { (* T_Bool:30672327 *) solve [ econstructor; eauto ]. }
  { (* T_Succ:d8990af8 *) solve [ econstructor; eauto ]. }
  { (* T_Pred:8df5b4ca *) solve [ econstructor; eauto ]. }
  { (* T_IsZero:d42f8b82 *) solve [ econstructor; eauto ]. }
  { (* T_If:749fed39 *) solve [ econstructor; eauto ]. }
  { (* T_Lam:69d38cf0 *) solve [ constructor; rewrite app_comm_cons; apply IHhas_type; reflexivity ]. }
  { (* T_App:c958a56c *) solve [ econstructor; eauto ]. }
  { (* T_Fix:ed2ab74f *) solve [ constructor; rewrite app_comm_cons; apply IHhas_type; reflexivity ]. }
  { (* T_Ref:b996d552 *) solve [ econstructor; eauto ]. }
  { (* T_Deref:d6548e5e *) solve [ econstructor; eauto ]. }
  { (* T_Assign:54028baf *) solve [ econstructor; eauto ]. }
  { (* T_Loc:2d0e0989 *) solve [ econstructor; eauto ]. }
Qed.


Lemma shift_preserves : forall G S t T U, has_type G S t T -> has_type (U :: G) S (shift t) T.
Proof.
intros G S t T U H; apply (shift_at_preserves _ _ _ _ H [] U G); reflexivity.
Qed.


Lemma subst_preserves : forall G' ST t T, has_type G' ST t T -> forall G1 U v, G' = G1 ++ [U] -> has_type G1 ST v U -> has_type G1 ST (subst (length G1) v t) T.
Proof.
  induction 1; intros G1 U v HeqG Hv; subst; simpl.
  { (* T_Var:e4c46809 *) solve [ destruct (Nat.eqb_spec x (length G1)); [ subst; rewrite nth_error_app2, Nat.sub_diag in H by lia; simpl in H; injection H as H; subst; assumption | constructor; destruct (Nat.ltb_spec x (length G1)); [ rewrite nth_error_app1 in H by assumption; assumption | rewrite nth_error_app2 in H by lia; destruct (x - length G1) as [|k] eqn:E; [ lia | simpl in H; rewrite nth_error_nil in H; discriminate ] ] ] ]. }
  { (* T_Num:927fd3a3 *) solve [ econstructor; eauto ]. }
  { (* T_Bool:025574c6 *) solve [ econstructor; eauto ]. }
  { (* T_Succ:f98072e1 *) solve [ econstructor; eauto ]. }
  { (* T_Pred:1198af39 *) solve [ econstructor; eauto ]. }
  { (* T_IsZero:e208defe *) solve [ econstructor; eauto ]. }
  { (* T_If:e6d545c1 *) solve [ econstructor; eauto ]. }
  { (* T_Lam:2e162d1a *) constructor.
    { (* case_1:e8a6e70c *) solve [ apply (IHhas_type (T1 :: G1) U (shift v)); [ reflexivity | apply shift_preserves; assumption ] ]. }
  }
  { (* T_App:88d39e4f *) solve [ econstructor; eauto ]. }
  { (* T_Fix:40f83ee1 *) constructor.
    { (* case_1:28b9aa39 *) solve [ apply (IHhas_type (T :: G1) U (shift v)); [ reflexivity | apply shift_preserves; assumption ] ]. }
  }
  { (* T_Ref:7001e017 *) solve [ econstructor; eauto ]. }
  { (* T_Deref:997c1111 *) solve [ econstructor; eauto ]. }
  { (* T_Assign:2c201bd4 *) solve [ econstructor; eauto ]. }
  { (* T_Loc:e9553e36 *) solve [ econstructor; eauto ]. }
Qed.


Lemma heap_lookup_type : forall mu ST, heap_ok mu ST -> forall l v T, heap_lookup l mu = Some v -> nth_error ST l = Some T -> has_type [] ST v T.
Proof.
induction 1; intros l0 v0 T0 Hl Hn; simpl in *; [ discriminate | destruct (Nat.eqb_spec l0 l); [ subst; injection Hl as Hl; subst; replace T0 with T by congruence; assumption | eauto ] ].
Qed.


Lemma heap_update_ok : forall mu ST, heap_ok mu ST -> forall l v T, nth_error ST l = Some T -> has_type [] ST v T -> heap_ok (heap_update l v mu) ST.
Proof.
induction 1; intros l0 v0 T0 Hn Hv; simpl; [ constructor | destruct (Nat.eqb_spec l0 l); [ subst; econstructor; eauto | econstructor; eauto ] ].
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
  intros t mu t' mu' T S Ht Hstep Hok Hlen; revert T S Ht Hok Hlen; induction Hstep; intros Ty STy Ht Hok Hlen; inversion Ht; subst; clear Ht.
  { (* S_Succ:21f2b37f *) solve [ edestruct IHHstep as (S' & Hext & Hok' & Ht'); eauto; exists S'; split; [exact Hext|split; [exact Hok'|econstructor; eauto using has_type_extends]] ]. }
  { (* S_PredZero:3a3dc8d3 *) solve [ exists STy; split; [apply extends_refl|split; [assumption|constructor]] ]. }
  { (* S_PredSucc:beba42d8 *) solve [ exists STy; split; [apply extends_refl|split; [assumption|constructor]] ]. }
  { (* S_Pred:40239b57 *) solve [ edestruct IHHstep as (S' & Hext & Hok' & Ht'); eauto; exists S'; split; [exact Hext|split; [exact Hok'|econstructor; eauto using has_type_extends]] ]. }
  { (* S_IsZeroZero:70a55b34 *) solve [ exists STy; split; [apply extends_refl|split; [assumption|constructor]] ]. }
  { (* S_IsZeroSucc:93aac8fa *) solve [ exists STy; split; [apply extends_refl|split; [assumption|constructor]] ]. }
  { (* S_IsZero:e963d6ea *) solve [ edestruct IHHstep as (S' & Hext & Hok' & Ht'); eauto; exists S'; split; [exact Hext|split; [exact Hok'|econstructor; eauto using has_type_extends]] ]. }
  { (* S_IfTrue:6dc90292 *) solve [ exists STy; split; [apply extends_refl|split; [assumption|assumption]] ]. }
  { (* S_IfFalse:a03a929f *) solve [ exists STy; split; [apply extends_refl|split; [assumption|assumption]] ]. }
  { (* S_If:c22bb06f *) solve [ edestruct IHHstep as (S' & Hext & Hok' & Ht'); eauto; exists S'; split; [exact Hext|split; [exact Hok'|econstructor; eauto using has_type_extends]] ]. }
  { (* S_App1:ecd40415 *) solve [ edestruct IHHstep as (S' & Hext & Hok' & Ht'); eauto; exists S'; split; [exact Hext|split; [exact Hok'|econstructor; eauto using has_type_extends]] ]. }
  { (* S_App2:d0bc108b *) solve [ edestruct IHHstep as (S' & Hext & Hok' & Ht'); eauto; exists S'; split; [exact Hext|split; [exact Hok'|econstructor; eauto using has_type_extends]] ]. }
  { (* S_AppAbs:aee4f5af *) exists STy; split; [ apply extends_refl | split; [ assumption | match goal with HL : has_type [] _ (Lam _ _) _ |- _ => inversion HL; subst end ] ].
    { (* case_1:1044402e *) solve [ eapply subst_preserves; [ eassumption | reflexivity | assumption ] ]. }
  }
  { (* S_Fix:a0096667 *) exists STy; split; [ apply extends_refl | split; [ assumption | idtac ] ].
    { (* case_1:c1a1e1de *) solve [ eapply subst_preserves; [ eassumption | reflexivity | constructor; assumption ] ]. }
  }
  { (* S_Ref:c2640fd0 *) solve [ edestruct IHHstep as (S' & Hext & Hok' & Ht'); eauto; exists S'; split; [exact Hext|split; [exact Hok'|econstructor; eauto using has_type_extends]] ]. }
  { (* S_RefV:f3e7ac08 *) exists (STy ++ repeat T (length mu - length STy + 1)); split; [ eexists; reflexivity | split ].
    { (* case_1:8bb893b1 *) econstructor.
      { (* case_1:4087453b *) solve [ eapply heap_ok_extends; [ eassumption | eexists; reflexivity ] ]. }
      { (* case_2:c1c57953 *) solve [ eapply has_type_extends; [ eassumption | eexists; reflexivity ] ]. }
      { (* case_3:1be6bdfb *) solve [ rewrite nth_error_app2 by lia; apply nth_error_repeat; lia ]. }
    }
    { (* case_2:c3f76436 *) solve [ constructor; rewrite nth_error_app2 by lia; apply nth_error_repeat; lia ]. }
  }
  { (* S_Deref:092ee268 *) solve [ edestruct IHHstep as (S' & Hext & Hok' & Ht'); eauto; exists S'; split; [exact Hext|split; [exact Hok'|econstructor; eauto using has_type_extends]] ]. }
  { (* S_DerefLoc:1dd3ddbd *) exists STy; split; [ apply extends_refl | split; [ assumption | match goal with HL : has_type [] _ (Loc _) _ |- _ => inversion HL; subst end ] ].
    { (* case_1:1d5eb59d *) solve [ eapply heap_lookup_type; eauto ]. }
  }
  { (* S_Assign1:52091909 *) solve [ edestruct IHHstep as (S' & Hext & Hok' & Ht'); eauto; exists S'; split; [exact Hext|split; [exact Hok'|econstructor; eauto using has_type_extends]] ]. }
  { (* S_Assign2:c3fa3ab3 *) solve [ edestruct IHHstep as (S' & Hext & Hok' & Ht'); eauto; exists S'; split; [exact Hext|split; [exact Hok'|econstructor; eauto using has_type_extends]] ]. }
  { (* S_AssignV:e98e387c *) exists STy; split; [ apply extends_refl | split; [ match goal with HL : has_type [] _ (Loc _) _ |- _ => inversion HL; subst end | constructor ] ].
    { (* case_1:997c9f99 *) solve [ eapply heap_update_ok; eauto ]. }
  }
Qed.
