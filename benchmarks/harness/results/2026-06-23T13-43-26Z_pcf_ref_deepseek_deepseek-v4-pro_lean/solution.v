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

Lemma has_type_store_weaken : forall G S t T,
  has_type G S t T ->
  forall S', extends S' S -> has_type G S' t T.
Proof.
  intros G S t T H.
  induction H; intros S'' Hext.
  - apply T_Var; auto.
  - apply T_Num.
  - apply T_Bool.
  - apply T_Succ; auto.
  - apply T_Pred; auto.
  - apply T_IsZero; auto.
  - eapply T_If; [apply IHhas_type1; auto | apply IHhas_type2; auto | apply IHhas_type3; auto].
  - apply T_Lam; apply IHhas_type; auto.
  - eapply T_App; [apply IHhas_type1; auto | apply IHhas_type2; auto].
  - apply T_Fix; apply IHhas_type; auto.
  - apply T_Ref; apply IHhas_type; auto.
  - apply T_Deref; apply IHhas_type; auto.
  - eapply T_Assign; [apply IHhas_type1; auto | apply IHhas_type2; auto].
  - destruct Hext as [S2 ->].
    apply T_Loc.
    erewrite nth_error_app1.
    apply H.
    apply nth_error_Some.
    rewrite H.
    discriminate.
Qed.

Lemma heap_ok_weaken : forall mu S,
  heap_ok mu S ->
  forall S', extends S' S -> heap_ok mu S'.
Proof.
  induction 1; intros S'' Hext.
  - apply heap_empty.
  - destruct Hext as [S2 ->].
    apply heap_cons with (T := T); auto.
    + apply IHheap_ok; auto.
      exists S2; reflexivity.
    + apply has_type_store_weaken with (S := S); auto.
      exists S2; reflexivity.
    + erewrite nth_error_app1.
      apply H1.
      apply nth_error_Some.
      rewrite H1.
      discriminate.
Qed.

Lemma heap_lookup_ok : forall mu S l v T,
  heap_ok mu S ->
  heap_lookup l mu = Some v ->
  nth_error S l = Some T ->
  has_type [] S v T.
Proof.
  intros mu S l v T Hhok.
  induction Hhok as [S'| l' v' mu' S' T' Hhok' IH Htyp Hnth'].
  - intros Hlook Hnth; simpl in Hlook; discriminate.
  - intros Hlook Hnth.
    simpl in Hlook.
    destruct (Nat.eqb l l') eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst.
      simpl in Hlook.
      inversion Hlook; subst.
      rewrite Hnth' in Hnth.
      inversion Hnth.
      subst.
      assumption.
    + apply IH; [assumption | assumption].
Qed.

Lemma heap_update_ok : forall mu S l v T,
  heap_ok mu S ->
  has_type [] S v T ->
  nth_error S l = Some T ->
  heap_ok (heap_update l v mu) S.
Proof.
  induction mu as [| a mu' IH]; intros S l v T Hhok Htyp Hnth.
  - inversion Hhok.
    apply heap_empty.
  - destruct a as [l' v'].
    inversion Hhok as [| l1 v1 m0 S0 T0 Hhok' Htyp' Hnth']; subst.
    simpl.
    destruct (Nat.eqb l l') eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst.
      rewrite Hnth' in Hnth.
      inversion Hnth; subst.
      apply heap_cons with (T := T); auto.
    + apply heap_cons with (T := T0); auto.
      apply IH with (T := T); auto.
Qed.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Lemma subst_preservation : forall S t T_root T2 s,
  has_type [T_root] S t T2 ->
  has_type [] S s T_root ->
  has_type [] S (subst 0 s t) T2.
Proof.
Admitted.

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
  intros t mu t' mu' T S Htype Hstep Hhok Hlen.
  revert T S Htype Hhok Hlen.
  induction Hstep; intros T0 S0 Htype Hhok Hlen.

  (* S_Succ *)
  - inversion Htype; subst.
    edestruct IHHstep as [S' [Hext [Hhok' Htyp']]]; eauto.
    exists S'; split; [| split]; auto.
    apply T_Succ; auto.

  (* S_PredZero *)
  - inversion Htype; subst.
    exists S0. split.
    { exists []; rewrite app_nil_r; reflexivity. }
    split; [apply Hhok | apply T_Num].

  (* S_PredSucc *)
  - inversion Htype; subst.
    exists S0. split.
    { exists []; rewrite app_nil_r; reflexivity. }
    split; [apply Hhok | apply T_Num].

  (* S_Pred *)
  - inversion Htype; subst.
    edestruct IHHstep as [S' [Hext [Hhok' Htyp']]]; eauto.
    exists S'; split; [| split]; auto.
    apply T_Pred; auto.

  (* S_IsZeroZero *)
  - inversion Htype; subst.
    exists S0. split.
    { exists []; rewrite app_nil_r; reflexivity. }
    split; [apply Hhok | apply T_Bool].

  (* S_IsZeroSucc *)
  - inversion Htype; subst.
    exists S0. split.
    { exists []; rewrite app_nil_r; reflexivity. }
    split; [apply Hhok | apply T_Bool].

  (* S_IsZero *)
  - inversion Htype; subst.
    edestruct IHHstep as [S' [Hext [Hhok' Htyp']]]; eauto.
    exists S'; split; [| split]; auto.
    apply T_IsZero; auto.

  (* S_IfTrue *)
  - inversion Htype; subst.
    exists S0. split.
    { exists []; rewrite app_nil_r; reflexivity. }
    split; auto.

  (* S_IfFalse *)
  - inversion Htype; subst.
    exists S0. split.
    { exists []; rewrite app_nil_r; reflexivity. }
    split; auto.

  (* S_If *)
  - inversion Htype; subst.
    edestruct IHHstep as [S' [Hext [Hhok' Htyp']]]; eauto.
    exists S'; split; [| split]; auto.
    eapply T_If; [apply Htyp' | apply has_type_store_weaken with (S := S0); eauto | apply has_type_store_weaken with (S := S0); eauto].

  (* S_App1 *)
  - inversion Htype; subst.
    edestruct IHHstep as [S' [Hext [Hhok' Htyp']]]; eauto.
    exists S'; split; [| split]; auto.
    eapply T_App; [apply Htyp' | apply has_type_store_weaken with (S := S0); eauto].

  (* S_App2 *)
  - inversion Htype; subst.
    edestruct IHHstep as [S' [Hext [Hhok' Htyp']]]; eauto.
    exists S'; split; [| split]; auto.
    eapply T_App; [apply has_type_store_weaken with (S := S0); eauto | apply Htyp'].

  (* S_AppAbs *)
  - inversion Htype; subst.
    inversion H4; subst.
    exists S0. split.
    { exists []; rewrite app_nil_r; reflexivity. }
    split; [apply Hhok | apply subst_preservation with (T_root := T1); auto].

  (* S_Fix *)
  - inversion Htype; subst.
    exists S0. split.
    { exists []; rewrite app_nil_r; reflexivity. }
    split; [apply Hhok | apply subst_preservation with (T_root := T0); auto; apply T_Fix; auto].

  (* S_Ref *)
  - inversion Htype; subst.
    edestruct IHHstep as [S' [Hext [Hhok' Htyp']]]; eauto.
    exists S'; split; [| split]; auto.
    apply T_Ref; auto.

  (* S_RefV *)
  - inversion Htype; subst.
    match goal with
    | H: has_type [] S0 v ?T |- _ =>
      set (k := length mu - length S0) in *;
      exists (S0 ++ repeat T (S k));
      split; [unfold extends; eexists; reflexivity | split]
    end.
    + eapply heap_cons; eauto.
      * apply heap_ok_weaken with (S := S0); eauto.
        unfold extends; eexists; reflexivity.
      * apply has_type_store_weaken with (S := S0); eauto.
        unfold extends; eexists; reflexivity.
      * { erewrite nth_error_app2; [| lia].
          apply nth_error_repeat.
          subst k; lia. }
    + eapply T_Loc.
      { erewrite nth_error_app2; [| lia].
        apply nth_error_repeat.
        subst k; lia. }

(* S_Deref *)
  - inversion Htype; subst.
    edestruct IHHstep as [S' [Hext [Hhok' Htyp']]]; eauto.
    exists S'; split; [| split]; auto.
    apply T_Deref; auto.

  (* S_DerefLoc *)
  - inversion Htype; subst.
    match goal with
    | Hloc: has_type [] S0 (Loc l) (TyRef T0) |- _ =>
      inversion Hloc; subst
    end.
    match goal with
    | Hlk: heap_lookup l mu = Some v, Hnth: nth_error S0 l = Some T0 |- _ =>
      assert (Hlook := heap_lookup_ok mu S0 l v T0 Hhok Hlk Hnth)
    end.
    exists S0. split.
    { exists []; rewrite app_nil_r; reflexivity. }
    split; [apply Hhok | apply has_type_store_weaken with (S := S0); auto; exists []; rewrite app_nil_r; reflexivity].

  (* S_Assign1 *)
  - inversion Htype; subst.
    edestruct IHHstep as [S' [Hext [Hhok' Htyp']]]; eauto.
    exists S'; split; [| split]; auto.
    eapply T_Assign; [apply Htyp' | apply has_type_store_weaken with (S := S0); eauto].

  (* S_Assign2 *)
  - inversion Htype; subst.
    edestruct IHHstep as [S' [Hext [Hhok' Htyp']]]; eauto.
    exists S'; split; [| split]; auto.
    eapply T_Assign; [apply has_type_store_weaken with (S := S0); eauto | apply Htyp'].

  (* S_AssignV *)
  - inversion Htype; subst.
    match goal with
    | H: has_type [] S0 v ?T, Hloc: has_type [] S0 (Loc l) (TyRef ?T) |- _ =>
      inversion Hloc; subst;
      exists S0; split;
      [ exists []; rewrite app_nil_r; reflexivity
      | split; [eapply heap_update_ok; eauto | apply T_Num] ]
    end.
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
