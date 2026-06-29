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

Lemma shift_at_typing : forall xG0 xG1 xST xt xT xT',
  has_type (xG0 ++ xG1) xST xt xT ->
  has_type (xG0 ++ xT' :: xG1) xST (shift_at (length xG0) xt) xT.
Proof.
  intros xG0 xG1 xST xt xT xT' H.
  revert xG0 xG1 xST xT xT' H.
  induction xt; intros xG0 xG1 xST xT xT' H; inversion H; subst; simpl.
  - destruct (n <? length xG0) eqn:Hlt.
    + apply Nat.ltb_lt in Hlt.
      apply T_Var.
      rewrite nth_error_app1 by auto.
      rewrite nth_error_app1 in H3 by auto.
      exact H3.
    + apply Nat.ltb_nlt in Hlt.
      apply T_Var.
      rewrite (nth_error_app2 (n := n+1) xG0 (xT' :: xG1)) by lia.
      replace (n + 1 - length xG0) with ((n - length xG0) + 1) by (clear -Hlt; lia).
      destruct (n - length xG0) as [|k] eqn:Hsub; simpl.
      * rewrite (nth_error_app2 (n := n) xG0 xG1) in H3 by (apply Nat.nlt_ge; exact Hlt).
        rewrite Hsub in H3. simpl in H3. exact H3.
      * rewrite (nth_error_app2 (n := n) xG0 xG1) in H3 by (apply Nat.nlt_ge; exact Hlt).
        rewrite Hsub in H3. rewrite <- (Nat.add_1_r k) in H3. exact H3.
  - exact (T_Num (xG0 ++ xT' :: xG1) xST n).
  - exact (T_Bool (xG0 ++ xT' :: xG1) xST b).
  - match goal with [H: has_type (xG0 ++ xG1) xST xt TyNat |- _] =>
      exact (T_Succ (xG0 ++ xT' :: xG1) xST (shift_at (length xG0) xt)
        (IHxt xG0 xG1 xST TyNat xT' H)) end.
  - match goal with [H: has_type (xG0 ++ xG1) xST xt TyNat |- _] =>
      exact (T_Pred (xG0 ++ xT' :: xG1) xST (shift_at (length xG0) xt)
        (IHxt xG0 xG1 xST TyNat xT' H)) end.
  - match goal with [H: has_type (xG0 ++ xG1) xST xt TyNat |- _] =>
      exact (T_IsZero (xG0 ++ xT' :: xG1) xST (shift_at (length xG0) xt)
        (IHxt xG0 xG1 xST TyNat xT' H)) end.
  - match goal with
    | [h1: has_type (xG0 ++ xG1) xST xt1 TyBool,
       h2: has_type (xG0 ++ xG1) xST xt2 ?T,
       h3: has_type (xG0 ++ xG1) xST xt3 ?T |- _] =>
      exact (T_If (xG0 ++ xT' :: xG1) xST
        (shift_at (length xG0) xt1) (shift_at (length xG0) xt2) (shift_at (length xG0) xt3) T
        (IHxt1 xG0 xG1 xST TyBool xT' h1)
        (IHxt2 xG0 xG1 xST T xT' h2)
        (IHxt3 xG0 xG1 xST T xT' h3))
    end.
  - match goal with [h: has_type (t :: xG0 ++ xG1) xST xt ?t2 |- _] =>
      exact (T_Lam (xG0 ++ xT' :: xG1) xST t t2 (shift_at (Datatypes.S (length xG0)) xt)
        (IHxt (t :: xG0) xG1 xST t2 xT' h)) end.
  - match goal with
    | [h1: has_type (xG0 ++ xG1) xST xt1 (TyArrow ?t1 ?t2),
       h2: has_type (xG0 ++ xG1) xST xt2 ?t1 |- _] =>
      exact (T_App (xG0 ++ xT' :: xG1) xST
        (shift_at (length xG0) xt1) (shift_at (length xG0) xt2) t1 t2
        (IHxt1 xG0 xG1 xST (TyArrow t1 t2) xT' h1)
        (IHxt2 xG0 xG1 xST t1 xT' h2))
    end.
  - apply (T_Fix (xG0 ++ xT' :: xG1) xST (shift_at (Datatypes.S (length xG0)) xt)).
    apply (IHxt (xT :: xG0) xG1 xST xT xT' H3).
  - apply (T_Ref (xG0 ++ xT' :: xG1) xST (shift_at (length xG0) xt) T).
    apply (IHxt xG0 xG1 xST T xT' H3).
  - apply (T_Deref (xG0 ++ xT' :: xG1) xST (shift_at (length xG0) xt) xT).
    apply (IHxt xG0 xG1 xST (TyRef xT) xT' H3).
  - apply (T_Assign (xG0 ++ xT' :: xG1) xST
      (shift_at (length xG0) xt1) (shift_at (length xG0) xt2) T).
    apply (IHxt1 xG0 xG1 xST (TyRef T) xT' H4).
    apply (IHxt2 xG0 xG1 xST T xT' H6).
  - apply (T_Loc (xG0 ++ xT' :: xG1) xST n T). exact H3.
Qed.

Lemma has_type_weaken : forall G S t T T',
  has_type G S t T ->
  has_type (T' :: G) S (shift t) T.
Proof.
  intros. apply (shift_at_typing [] G S t T T' H).
Qed.

Lemma has_type_subst : forall xG T' S t T s,
  has_type (xG ++ [T']) S t T ->
  has_type xG S s T' ->
  has_type xG S (subst (length xG) s t) T.
Proof.
  intros xG T' S t T s Ht Hs.
  remember (xG ++ [T']) as Gext eqn:Heq.
  revert xG s Hs Heq.
  induction Ht; intros xG' s' Hs Heq; subst G; simpl.
  - apply T_Var.
    destruct (Nat.eqb x (length xG')) eqn:Heqb.
    + apply Nat.eqb_eq in Heqb; subst x.
      rewrite nth_error_app2 in H by lia.
      replace (length xG' - length xG') with 0 in H by lia.
      simpl in H; inversion H; subst; exact Hs.
    + destruct (x <? length xG') eqn:Hltb.
      * apply Nat.ltb_lt in Hltb.
        rewrite (nth_error_app1 (n := x) xG' [T'] Hltb) in H; exact H.
      * apply Nat.ltb_nlt in Hltb; apply Nat.nlt_ge in Hltb.
        rewrite (nth_error_app2 (n := x) xG' [T'] Hltb) in H; simpl in H.
        apply Nat.eqb_neq in Heqb.
        destruct (x - length xG') eqn:Hsub; [exfalso; apply Heqb; lia | inversion H].
  - apply T_Num.
  - apply T_Bool.
  - apply T_Succ; apply (IHHt xG' s' Hs (eq_refl _)).
  - apply T_Pred; apply (IHHt xG' s' Hs (eq_refl _)).
  - apply T_IsZero; apply (IHHt xG' s' Hs (eq_refl _)).
  - apply T_If; [apply (IHHt1 xG' s' Hs (eq_refl _)) | apply (IHHt2 xG' s' Hs (eq_refl _)) | apply (IHHt3 xG' s' Hs (eq_refl _))].
  - apply T_Lam.
    refine (IHHt (T1 :: xG') (shift s') _ (eq_refl _)).
    apply has_type_weaken. exact Hs.
  - apply T_App; [apply (IHHt1 xG' s' Hs (eq_refl _)) | apply (IHHt2 xG' s' Hs (eq_refl _))].
  - apply T_Fix.
    refine (IHHt (T :: xG') (shift s') _ (eq_refl _)).
    apply has_type_weaken. exact Hs.
  - apply T_Ref; apply (IHHt xG' s' Hs (eq_refl _)).
  - apply T_Deref; apply (IHHt xG' s' Hs (eq_refl _)).
  - apply T_Assign; [apply (IHHt1 xG' s' Hs (eq_refl _)) | apply (IHHt2 xG' s' Hs (eq_refl _))].
  - apply T_Loc; exact H.

  { (* has_type_subst:unknown *) admit. }

Admitted.

Lemma has_type_store_weaken : forall G S S' t T,
  has_type G S t T ->
  extends S' S ->
  has_type G S' t T.
Proof.
Admitted.

Lemma heap_ok_extends : forall mu S S',
  heap_ok mu S ->
  extends S' S ->
  heap_ok mu S'.
Proof.
Admitted.

Lemma heap_ok_lookup_type : forall mu S l v T,
  heap_ok mu S ->
  heap_lookup l mu = Some v ->
  nth_error S l = Some T ->
  has_type [] S v T.
Proof.
Admitted.

Lemma heap_ok_update : forall mu S l v T,
  heap_ok mu S ->
  nth_error S l = Some T ->
  has_type [] S v T ->
  heap_ok (heap_update l v mu) S.
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
