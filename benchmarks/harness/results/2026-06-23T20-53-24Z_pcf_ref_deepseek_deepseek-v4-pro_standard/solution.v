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

Lemma heap_ok_length_eq : forall mu S,
  heap_ok mu S -> length mu >= length S -> length mu = length S.
Proof.
Admitted.

Lemma heap_ok_nth_lookup : forall mu S l v,
  heap_ok mu S ->
  heap_lookup l mu = Some v ->
  exists T, nth_error S l = Some T /\ has_type [] S v T.
Proof.
  intros mu S l v Hh Hl; induction Hh; simpl in *.
  { (* heap_empty:f92870ab *) solve [ discriminate ]. }
  { (* heap_cons:94096376 *) simpl in Hl; destruct (l =? l0) eqn:Heq; [inversion Hl; subst; exists T; eauto | eauto].
    { (* 5272d269 *) apply Nat.eqb_eq in Heq; subst; split; eauto.
    }
  }
Qed.

Lemma has_type_weaken : forall G S t T S',
  has_type G S t T ->
  extends S' S ->
  has_type G S' t T.
Proof.
  intros G S t T S' Ht Hext.
  unfold extends in Hext. destruct Hext as [S2 ->].
  induction Ht.
  - econstructor. eauto.
  - econstructor.
  - econstructor.
  - econstructor. apply IHHt.
  - econstructor. apply IHHt.
  - econstructor. apply IHHt.
  - econstructor; [apply IHHt1 | apply IHHt2 | apply IHHt3].
  - econstructor. apply IHHt.
  - econstructor; [apply IHHt1 | apply IHHt2].
  - econstructor. apply IHHt.
  - econstructor. apply IHHt.
  - econstructor. apply IHHt.
  - econstructor; [apply IHHt1 | apply IHHt2].
  - econstructor.
    assert (l < length S).
    { apply nth_error_Some; rewrite H; discriminate. }
    erewrite nth_error_app1; eauto.
Qed.

Lemma heap_ok_extends : forall mu S S',
  heap_ok mu S ->
  extends S' S ->
  heap_ok mu S'.
Proof.
  intros mu S S' Hh Hext.
  unfold extends in Hext. destruct Hext as [S2 ->].
  induction Hh.
  - constructor.
  - econstructor; [apply IHHh; exists S2; reflexivity | eapply has_type_weaken; eauto; exists S2; reflexivity |].
    assert (l < length S).
    { apply nth_error_Some; rewrite H0; discriminate. }
    erewrite nth_error_app1; eauto.
Qed.

Lemma shift_at_has_type : forall G S t T d T0,
  has_type G S t T ->
  has_type (firstn d G ++ T0 :: skipn d G) S (shift_at d t) T.
Proof.
  intros G S t T d T0 Ht. revert d T0.
  induction Ht; intros d T0; simpl.
  - rename x into i.
    destruct (i <? d) eqn:Hiltb.
    + apply Nat.ltb_lt in Hiltb.
      apply T_Var.
      assert (Hi_lenG : i < length G) by
        (apply nth_error_Some; rewrite H; discriminate).
      assert (Hi_len : i < length (firstn d G)).
      { rewrite length_firstn. apply Nat.min_glb_lt_iff; split; auto. }
      pose proof (@nth_error_app1 ty (firstn d G) (T0 :: skipn d G) i Hi_len) as Hrew1.
      rewrite Hrew1.
      rewrite nth_error_firstn.
      apply Nat.ltb_lt in Hiltb.
      rewrite Hiltb. simpl. apply H.
    + apply Nat.ltb_nlt in Hiltb.
      assert (Hi_ge : i >= d) by lia.
      apply T_Var.
      assert (Hi_lenG : i < length G) by
        (apply nth_error_Some; rewrite H; discriminate).
      assert (Hfirst_len : length (firstn d G) = d).
      { apply firstn_length_le; lia. }
      assert (Hi_len2 : length (firstn d G) <= i + 1).
      { rewrite Hfirst_len; lia. }
      pose proof (@nth_error_app2 ty (firstn d G) (T0 :: skipn d G) (i+1) Hi_len2) as Hrew2.
      rewrite Hrew2.
      rewrite Hfirst_len.
      assert (i + 1 - d = Datatypes.S (i - d)) by lia.
      rewrite H0.
      simpl. rewrite nth_error_skipn.
      replace (d + (i - d)) with i by lia.
      apply H.
  - apply T_Num.
  - apply T_Bool.
  - apply T_Succ. apply IHHt.
  - apply T_Pred. apply IHHt.
  - apply T_IsZero. apply IHHt.
  - eapply T_If; [apply IHHt1 | apply IHHt2 | apply IHHt3].
  - apply T_Lam. apply (IHHt (Datatypes.S d) T0).
  - eapply T_App; [apply IHHt1 | apply IHHt2].
  - apply T_Fix. apply (IHHt (Datatypes.S d) T0).
  - apply T_Ref. apply IHHt.
  - apply T_Deref. apply IHHt.
  - eapply T_Assign; [apply IHHt1 | apply IHHt2].
  - apply T_Loc. auto.
Qed.
Lemma shift_has_type : forall G S t T T0,
  has_type G S t T ->
  has_type (T0 :: G) S (shift t) T.
Proof.
  intros G S t T T0 Ht.
  unfold shift.
  apply (shift_at_has_type G S t T 0 T0 Ht).
Qed.

Lemma has_type_subst : forall G S j s t T U,
  has_type (firstn j G ++ T :: skipn j G) S t U ->
  has_type G S s T ->
  has_type (firstn j G ++ skipn j G) S (subst j s t) U.
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
  intros t mu t' mu' T S Ht Hstep Hh Hlen; induction Hstep.
  { (* S_Succ:b7cb6052 *) solve [ admit ]. }
  { (* S_PredZero:8a988606 *) solve [ admit ]. }
    { (* c043d13e *) inversion Ht; subst. exists S; split; [|split]; [unfold extends; exists []; rewrite app_nil_r; reflexivity | eauto | econstructor; eauto using T_Num].
    }
    { (* 1a947feb *) admit. }
    { (* 4c5cc523 *) inversion Ht; subst. exists S; split; [|split]; [unfold extends; exists []; rewrite app_nil_r; reflexivity | eauto | econstructor; eauto using T_Bool].
    }
    { (* 0e761689 *) inversion Ht; subst. exists S; split; [|split]; [unfold extends; exists []; rewrite app_nil_r; reflexivity | eauto | econstructor; eauto using T_Bool].
    }
    { (* 02725275 *) admit. }
    { (* cafe6220 *) inversion Ht; subst. exists S; split; [|split]; [unfold extends; exists []; rewrite app_nil_r; reflexivity | eauto | eauto].
    }
    { (* 05469720 *) inversion Ht; subst. exists S; split; [|split]; [unfold extends; exists []; rewrite app_nil_r; reflexivity | eauto | eauto].
    }
    { (* c3de78ea *) admit. }
    { (* 2509b3b0 *) admit. }
    { (* 03ad82fc *) admit. }
    { (* 76e710a9 *) admit. }
    { (* 0616077c *) admit. }
    { (* be46bb6f *) admit. }
    { (* 8f256d55 *) admit. }
    { (* b1179dd2 *) admit. }
    { (* add14de8 *) admit. }
    { (* fffef7ca *) admit. }
    { (* 58478d5e *) admit. }
    { (* 7c7815fd *) admit. }
  { (* S_PredSucc:c043d13e *) solve [ admit ]. }
  { (* S_Pred:1a947feb *) solve [ admit ]. }
  { (* S_IsZeroZero:4c5cc523 *) solve [ admit ]. }
  { (* S_IsZeroSucc:0e761689 *) solve [ admit ]. }
  { (* S_IsZero:02725275 *) solve [ admit ]. }
  { (* S_IfTrue:cafe6220 *) solve [ admit ]. }
  { (* S_IfFalse:05469720 *) solve [ admit ]. }
  { (* S_If:c3de78ea *) solve [ admit ]. }
  { (* S_App1:2509b3b0 *) solve [ admit ]. }
  { (* S_App2:03ad82fc *) solve [ admit ]. }
  { (* S_AppAbs:76e710a9 *) solve [ admit ]. }
  { (* S_Fix:0616077c *) solve [ admit ]. }
  { (* S_Ref:be46bb6f *) solve [ admit ]. }
  { (* S_RefV:8f256d55 *) solve [ admit ]. }
  { (* S_Deref:b1179dd2 *) solve [ admit ]. }
  { (* S_DerefLoc:add14de8 *) solve [ admit ]. }
  { (* S_Assign1:fffef7ca *) solve [ admit ]. }
  { (* S_Assign2:58478d5e *) solve [ admit ]. }
  { (* S_AssignV:7c7815fd *) solve [ admit ]. }
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
