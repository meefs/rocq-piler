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
Proof. exists []. rewrite app_nil_r. reflexivity. Qed.

Lemma nth_error_extends : forall S S' l T,
  extends S' S -> nth_error S l = Some T -> nth_error S' l = Some T.
Proof.
  intros S S' l T [S2 HS']. subst.
  intro H. rewrite nth_error_app1.
  - exact H.
  - apply nth_error_Some. intros C. rewrite C in H. discriminate.
Qed.

Lemma has_type_store_weaken : forall G S t T S',
  has_type G S t T -> extends S' S -> has_type G S' t T.
Proof.
  intros G S t T S' Ht Hext.
  induction Ht.
  - apply T_Var; auto.
  - apply T_Num.
  - apply T_Bool.
  - apply T_Succ; auto.
  - apply T_Pred; auto.
  - apply T_IsZero; auto.
  - apply T_If; auto.
  - apply T_Lam; auto.
  - apply T_App with (T1 := T1); auto.
  - apply T_Fix; auto.
  - apply T_Ref; auto.
  - eapply T_Deref; eauto.
  - eapply T_Assign; eauto.
  - apply T_Loc. eapply nth_error_extends; eauto.
Qed.

Lemma heap_lookup_typing : forall mu S l v,
  heap_ok mu S ->
  heap_lookup l mu = Some v ->
  exists T, nth_error S l = Some T /\ has_type [] S v T.
Proof.
  induction mu as [|[l' v'] mu' IH]; intros S l v Hok Hlook; simpl in Hlook.
  - discriminate.
  - inversion Hok as [| l'' v'' mu'' S'' T' Hok' Hv' Hnth]; subst.
    destruct (Nat.eqb l l') eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst l'. inversion Hlook; subst v.
      exists T'. split; auto.
    + destruct (IH S l v Hok' Hlook) as [T [Hnth' Hv'']].
      exists T. split; auto.
Qed.

Lemma heap_update_heap_ok : forall mu S l v T,
  heap_ok mu S ->
  nth_error S l = Some T ->
  has_type [] S v T ->
  heap_ok (heap_update l v mu) S.
Proof.
  induction mu as [|[l' v'] mu' IH]; intros S l v T Hok Hnth Hv; simpl.
  - apply heap_empty.
  - inversion Hok as [| l'' v'' mu'' S'' T' Hok' Hv' Hnth']; subst.
    destruct (Nat.eqb l l') eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst l'.
      apply heap_cons with (T := T); auto.
    + apply heap_cons with (T := T'); auto.
      apply IH with (T := T); auto.
Qed.

Lemma subst_closed : forall S t s T T',
  has_type [T] S t T' ->
  has_type [] S s T ->
  has_type [] S (subst 0 s t) T'.
Proof.
Admitted.

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
  intros t mu t' mu' T S Ht Hstep Hok Hlen.
  induction Hstep; intros.
  - inversion Ht; subst. destruct IHHstep as [S' [Hext [Hok' Ht']]]; auto.
    exists S'. split; [|split]; auto. apply T_Succ; auto.
  - inversion Ht; subst. exists S. split; [apply extends_refl | split]; auto. apply T_Num.
  - inversion Ht; subst. exists S. split; [apply extends_refl | split]; auto. apply T_Num.
  - inversion Ht; subst. destruct IHHstep as [S' [Hext [Hok' Ht']]]; auto.
    exists S'. split; [|split]; auto. apply T_Pred; auto.
  - inversion Ht; subst. exists S. split; [apply extends_refl | split]; auto. apply T_Bool.
  - inversion Ht; subst. exists S. split; [apply extends_refl | split]; auto. apply T_Bool.
  - inversion Ht; subst. destruct IHHstep as [S' [Hext [Hok' Ht']]]; auto.
    exists S'. split; [|split]; auto. apply T_IsZero; auto.
  - inversion Ht; subst. exists S. split; [apply extends_refl | split]; auto.
  - inversion Ht; subst. exists S. split; [apply extends_refl | split]; auto.
  - inversion Ht; subst. destruct IHHstep as [S' [Hext [Hok' Ht1']]]; auto.
    exists S'. split; [|split]; auto.
    apply T_If with (t1 := t1') (t2 := t2) (t3 := t3) (T := T); auto;
      eapply has_type_store_weaken; eauto.
  - inversion Ht; subst. destruct IHHstep as [S' [Hext [Hok' Ht1']]]; auto.
    exists S'. split; [|split]; auto.
    eapply T_App; eauto. eapply has_type_store_weaken; eauto.
  - inversion Ht; subst. destruct IHHstep as [S' [Hext [Hok' Ht2']]]; auto.
    exists S'. split; [|split]; auto.
    eapply T_App; eauto. eapply has_type_store_weaken; eauto.
  - inversion Ht; subst. inversion H4; subst.
    exists S. split; [apply extends_refl | split]; auto.
    apply subst_closed with (T := T1); auto.
  - inversion Ht; subst.
    exists S. split; [apply extends_refl | split]; auto.
    apply subst_closed with (T := T); auto.
    apply T_Fix; auto.
  - inversion Ht; subst. destruct IHHstep as [S' [Hext [Hok' Ht']]]; auto.
    exists S'. split; [|split]; auto. apply T_Ref; auto.
  - inversion Ht; subst.
    exists (S ++ [T0]). split.
    { exists [T0]. reflexivity. }
    split.
    { apply heap_cons with (T := T0); auto.
      - eapply has_type_store_weaken; eauto. exists [T0]. reflexivity.
      - rewrite nth_error_app1. exact H3. simpl. lia. }
    { apply T_Loc. rewrite nth_error_app2. rewrite Nat.sub_diag. simpl. reflexivity. lia. }
  - inversion Ht; subst. destruct IHHstep as [S' [Hext [Hok' Ht']]]; auto.
    exists S'. split; [|split]; auto.
    eapply T_Deref; eauto.
  - inversion Ht; subst. simpl in H3.
    destruct (heap_lookup_typing mu S l v Hok H6) as [T0' [Hnth Hv]].
    rewrite Hnth in H3. inversion H3; subst.
    exists S. split; [apply extends_refl | split]; auto.
  - inversion Ht; subst. destruct IHHstep as [S' [Hext [Hok' Ht1']]]; auto.
    exists S'. split; [|split]; auto.
    eapply T_Assign; eauto. eapply has_type_store_weaken; eauto.
  - inversion Ht; subst. destruct IHHstep as [S' [Hext [Hok' Ht2']]]; auto.
    exists S'. split; [|split]; auto.
    eapply T_Assign; eauto. eapply has_type_store_weaken; eauto.
  - inversion Ht; subst.
    exists S. split; [apply extends_refl | split]; auto.
    { apply heap_update_heap_ok with (T := T0); auto. }
    { apply T_Num. }

  { (* preservation:5a703c5c *) admit. }

Admitted.

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
