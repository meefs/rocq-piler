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

(** * Auxiliary lemmas *)

Lemma extends_refl : forall S, extends S S.
Proof.
  intros S. exists []. symmetry. apply app_nil_r.
Qed.

Lemma nth_error_extends : forall S S' i T,
  extends S' S ->
  nth_error S i = Some T ->
  nth_error S' i = Some T.
Proof.
  intros S S' i T [S2 H] Hnth. subst S'.
  assert (Hi : i < length S).
  { apply nth_error_Some. rewrite Hnth. discriminate. }
  rewrite nth_error_app1; auto.
Qed.

Lemma has_type_weaken_store : forall G S t T S',
  has_type G S t T ->
  extends S' S ->
  has_type G S' t T.
Proof.
  intros G S t T S' Ht Hext. revert S' Hext.
  induction Ht; intros S'' Hext.
  - apply T_Var. auto.
  - apply T_Num.
  - apply T_Bool.
  - apply T_Succ. auto.
  - apply T_Pred. auto.
  - apply T_IsZero. auto.
  - apply T_If; auto.
  - apply T_Lam. auto.
  - apply T_App with (T1:=T1); auto.
  - apply T_Fix. auto.
  - apply T_Ref. auto.
  - apply T_Deref. auto.
  - apply T_Assign with (T:=T); auto.
  - eapply T_Loc. eapply nth_error_extends; eauto.
Qed.

Lemma heap_ok_extends : forall mu S S',
  heap_ok mu S ->
  extends S' S ->
  heap_ok mu S'.
Proof.
  intros mu S S' Hok Hext. induction Hok.
  - apply heap_empty.
  - eapply heap_cons with (T:=T); eauto.
    + apply has_type_weaken_store with (S:=S); auto.
    + eapply nth_error_extends; eauto.
Qed.

Lemma heap_ok_lookup : forall mu S loc val Ty,
  heap_ok mu S ->
  heap_lookup loc mu = Some val ->
  nth_error S loc = Some Ty ->
  has_type [] S val Ty.
Proof.
  intros mu S loc val Ty Hok.
  induction Hok; simpl; intros Hlookup Hnth.
  - discriminate.
  - destruct (Nat.eqb loc l) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst l.
      simpl in Hlookup. injection Hlookup as ->.
      rewrite H0 in Hnth. injection Hnth as ->.
      apply H.
    + apply IHHok; auto.
Qed.

Lemma heap_ok_update : forall mu S loc val Ty,
  heap_ok mu S ->
  nth_error S loc = Some Ty ->
  has_type [] S val Ty ->
  heap_ok (heap_update loc val mu) S.
Proof.
  induction 1 as [S' | l v mu' S' T Hok IH Hty Hnth_loc]; simpl; intros Hnth Hval.
  - apply heap_empty.
  - destruct (Nat.eqb loc l) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst l.
      assert (T = Ty) by (rewrite Hnth_loc in Hnth; inversion Hnth; auto).
      subst Ty.
      apply (heap_cons loc val mu' S' T Hok Hval Hnth_loc).
    + apply (heap_cons l v (heap_update loc val mu') S' T).
      * apply IH; auto.
      * exact Hty.
      * exact Hnth_loc.
Qed.

Lemma heap_update_length : forall l v mu,
  length (heap_update l v mu) = length mu.
Proof.
  intros l v mu. induction mu; simpl; auto.
  destruct a as [l' v']. destruct (Nat.eqb l l'); simpl; auto.
Qed.

Lemma step_length_ge : forall t mu t' mu',
  step t mu t' mu' ->
  length mu' >= length mu.
Proof.
  intros t mu t' mu' Hstep. induction Hstep; simpl; try lia.
  - rewrite heap_update_length. lia.
Qed.

Lemma shift_at_has_type : forall G S t T G' d,
  has_type G S t T ->
  has_type (G ++ G') S (shift_at d t) T.
Proof.
Admitted.

Lemma subst_has_type : forall G S s t T U d,
  has_type (U :: G) S t T ->
  has_type G S s U ->
  has_type G S (subst d s t) T.
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
  intros t mu t' mu' T S Ht Hstep Hok Hlen. generalize dependent T. generalize dependent S. induction Hstep; intros S' Hok' Hlen' T' Ht'.
  { (* case_1:abfb0644 *) inversion Ht'; subst. apply IHHstep with (S:=S') (T:=TyNat) in H2; auto. destruct H2 as (S'' & Hext & Hok'' & Ht''). exists S''; split; [|split]; auto. apply T_Succ; auto.
  }
  { (* case_2:e7355e36 *)
    inversion Ht'; subst. exists S'; split; [apply extends_refl | split; auto]. }
  { (* case_3:7d75d83c *) inversion Ht'; subst. exists S'; split; [apply extends_refl | split; auto]. apply T_Num.
  }
  { (* case_4:7bd11d0c *) inversion Ht'; subst. apply IHHstep with (S:=S') (T:=TyNat) in H2; auto. destruct H2 as (S'' & Hext & Hok'' & Ht''). exists S''; split; [|split]; auto. apply T_Pred; auto.
  }
  { (* case_5:9901f26f *) inversion Ht'; subst. exists S'; split; [apply extends_refl | split; auto]. apply T_Bool.
  }
  { (* case_6:a6d20d70 *) inversion Ht'; subst. exists S'; split; [apply extends_refl | split; auto]. apply T_Bool.
  }
  { (* case_7:ae53be15 *) inversion Ht'; subst. apply IHHstep with (S:=S') (T:=TyNat) in H2; auto. destruct H2 as (S'' & Hext & Hok'' & Ht''). exists S''; split; [|split]; auto. apply T_IsZero; auto.
  }
  { (* case_8:3fa2e857 *) inversion Ht'; subst. exists S'; split; [apply extends_refl | split; auto].
  }
  { (* case_9:a09b3729 *) inversion Ht'; subst. exists S'; split; [apply extends_refl | split; auto].
  }
  { (* case_10:2e7ee512 *)
    inversion Ht'; subst.
    edestruct IHHstep with (S:=S') (T:=TyBool) as (S'' & Hext & Hok'' & Ht1'); eauto.
    exists S''; split; [|split]; auto.
    apply T_If; [apply Ht1' | eapply has_type_weaken_store; eauto | eapply has_type_weaken_store; eauto]. }
  { (* case_11:4c3e5988 *) inversion Ht'; subst. apply IHHstep with (S:=S') in H3; auto. destruct H3 as (S'' & Hext & Hok'' & Ht1'). exists S''; split; [|split]; auto. eapply T_App; [apply Ht1' | eapply has_type_weaken_store; eauto].
  }
  { (* case_12:1953d468 *)
    inversion Ht'; subst.
    eapply IHHstep with (S:=S') in H6; eauto.
    destruct H6 as (S'' & Hext & Hok'' & Ht2').
    exists S''; split; [|split]; auto.
    eapply T_App; [eapply has_type_weaken_store; eauto | apply Ht2']. }
  { (* case_13:205e9cc2 *)
    inversion Ht'; subst.
    inversion H4; subst.
    exists S'; split; [apply extends_refl | split; auto].
    eapply subst_has_type with (d:=0); eauto. }
  { (* case_14:1fb6cf85 *)
    inversion Ht'; subst.
    exists S'; split; [apply extends_refl | split; auto].
    eapply subst_has_type with (d:=0); eauto. }
  { (* case_15:487df458 *) inversion Ht'; subst. apply IHHstep with (S:=S') in H2; auto. destruct H2 as (S'' & Hext & Hok'' & Ht''). exists S''; split; [|split]; auto. apply T_Ref; auto.
  }
  { (* case_16:c20ed2cf *)
    inversion Ht'; subst.
    set (d := length mu - length S').
    exists (S' ++ repeat TyNat d ++ [T]).
    split; [ exists (repeat TyNat d ++ [T]); auto |].
    split.
    - apply heap_cons with (T:=T).
      + apply heap_ok_extends with (S:=S'); auto. exists (repeat TyNat d ++ [T]). auto.
      + apply has_type_weaken_store with (S:=S'); auto. exists (repeat TyNat d ++ [T]). auto.
      + rewrite nth_error_app2 by (unfold d; lia).
        rewrite nth_error_app2 by (rewrite repeat_length; lia).
        replace (length mu - length S' - length (repeat TyNat d)) with 0 by (rewrite repeat_length; unfold d; lia).
        simpl; reflexivity.
    - apply T_Loc.
      rewrite nth_error_app2 by (unfold d; lia).
      rewrite nth_error_app2 by (rewrite repeat_length; lia).
      replace (length mu - length S' - length (repeat TyNat d)) with 0 by (rewrite repeat_length; unfold d; lia).
      simpl; reflexivity. }
  { (* case_17:e9fff51f *) inversion Ht'; subst. apply IHHstep with (S:=S') in H2; auto. destruct H2 as (S'' & Hext & Hok'' & Ht''). exists S''; split; [|split]; auto. apply T_Deref; auto.
  }
  { (* case_18:a60052de *)
    inversion Ht'; subst.
    inversion H3; subst.
    assert (Hty : has_type [] S' v T').
    { eapply heap_ok_lookup; eauto. }
    exists S'; split; [apply extends_refl | split; auto]. }
  { (* case_19:9c5f86c1 *) inversion Ht'; subst. apply IHHstep with (S:=S') in H3; auto. destruct H3 as (S'' & Hext & Hok'' & Ht1'). exists S''; split; [|split]; auto. eapply T_Assign; [apply Ht1' | eapply has_type_weaken_store; eauto].
  }
  { (* case_20:99009212 *)
    inversion Ht'; subst.
    edestruct IHHstep with (S:=S') as (S'' & Hext & Hok'' & Ht2'); eauto.
    exists S''; split; [|split]; auto.
    eapply T_Assign; [eapply has_type_weaken_store; eauto | apply Ht2']. }
  { (* case_21:491dacc7 *)
    inversion Ht'; subst.
    inversion H4; subst.
    exists S'; split; [apply extends_refl | split; [eapply heap_ok_update; eauto | apply T_Num]]. }
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
