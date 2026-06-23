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

Lemma nth_error_Some_length : forall {A} (l : list A) n x,
  nth_error l n = Some x -> n < length l.
Proof.
  intros A l n x H. revert l n x H.
  fix IH 1.
  intros l0 n0 x0 H0.
  destruct l0 as [|a l1]; destruct n0 as [|n']; simpl in H0;
    [discriminate H0|discriminate H0| |].
  inversion H0; subst; lia.
  apply (IH l1 n' x0 H0); simpl; lia.
Qed.

Lemma nth_error_app1 : forall {A} (l1 l2 : list A) n,
  n < length l1 -> nth_error (l1 ++ l2) n = nth_error l1 n.
Proof.
  induction l1; simpl; intros n H.
  lia.
  destruct n; simpl; auto.
  apply IHl1; lia.
Qed.

Lemma nth_error_app2 : forall {A} (l1 l2 : list A) n,
  n >= length l1 -> nth_error (l1 ++ l2) n = nth_error l2 (n - length l1).
Proof.
  induction l1; simpl; intros n H.
  rewrite Nat.sub_0_r; auto.
  destruct n; simpl; try lia.
  apply IHl1; lia.
Qed.

Lemma nth_error_extends : forall S S' l T,
  extends S' S -> nth_error S l = Some T -> nth_error S' l = Some T.
Proof.
  intros S S' l T [S2 ->] H.
  apply nth_error_app1.
  eapply nth_error_Some_length; eauto.
Qed.

Lemma extends_refl : forall S, extends S S.
Proof. intro S; exists []; rewrite app_nil_r; auto. Qed.

(** * Weakening with respect to the store typing *)

Lemma has_type_weaken : forall G S S' t T,
  has_type G S t T -> extends S' S -> has_type G S' t T.
Proof.
  intros G S S' t T H; revert S'.
  induction H; intros S' Hext;
    try solve [econstructor; eauto using nth_error_extends].
  - econstructor; eauto using nth_error_extends.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto; eapply IHhas_type1; eauto.
    eapply IHhas_type2; eauto.
    eapply IHhas_type3; eauto.
  - econstructor; eauto.
  - econstructor; eauto; eapply IHhas_type1; eauto.
    eapply IHhas_type2; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto; eapply IHhas_type1; eauto.
    eapply IHhas_type2; eauto.
  - econstructor; eauto using nth_error_extends.
Qed.

Lemma heap_ok_extends : forall mu S S',
  heap_ok mu S -> extends S' S -> heap_ok mu S'.
Proof.
  induction 1; intros S' Hext.
  constructor.
  econstructor; eauto.
  eapply has_type_weaken; eauto.
  eapply nth_error_extends; eauto.
Qed.

(** * Heap lookup and update lemmas *)

Lemma heap_lookup_ok : forall mu S l v T,
  heap_ok mu S ->
  heap_lookup l mu = Some v ->
  nth_error S l = Some T ->
  has_type [] S v T.
Proof.
  induction mu as [|[l' v'] mu' IH]; simpl; intros S l v T Hok Hlk Hnth.
  inversion Hlk.
  inversion Hok; subst.
  destruct (Nat.eqb l l') eqn:Heq.
  apply Nat.eqb_eq in Heq; subst l'.
  inversion Hlk; subst.
  rewrite Hnth in H3; injection H3; intros; subst; auto.
  eapply IH; eauto.
Qed.

Lemma heap_update_ok : forall mu S l v T,
  heap_ok mu S ->
  has_type [] S v T ->
  nth_error S l = Some T ->
  heap_ok (heap_update l v mu) S.
Proof.
  induction mu as [|[l' v'] mu' IH]; simpl; intros S l v T Hok Hty Hnth.
  constructor.
  inversion Hok; subst.
  destruct (Nat.eqb l l') eqn:Heq.
  apply Nat.eqb_eq in Heq; subst l'.
  rewrite Hnth in H3; injection H3; intros; subst.
  econstructor; eauto.
  econstructor; eauto.
  eapply IH; eauto.
Qed.

(** * Shift (weakening) lemma for De Bruijn indices *)

Lemma nth_error_insert_shift : forall {A} d (l : list A) x T' y,
  nth_error l x = Some y ->
  nth_error (firstn d l ++ T' :: skipn d l) (if x <? d then x else S x) = Some y.
Proof.
  intros A d l x T' y H.
  assert (x < length l) by (eapply nth_error_Some_length; eauto).
  destruct (x <? d) eqn:Hlt.
  apply Nat.ltb_lt in Hlt.
  apply nth_error_app1.
  rewrite firstn_length. apply Nat.min_glb_lt; auto.
  clear -Hlt H. revert x Hlt H.
  induction l; simpl; intros x Hlt H; try (inversion H).
  destruct d; simpl; try lia.
  destruct x; simpl.
  lia.
  apply IHl; auto. lia.
  apply Nat.ltb_nlt in Hlt.
  rewrite nth_error_app2.
  rewrite firstn_length_le by lia.
  replace (S x - d) with (S (x - d)) by lia.
  simpl.
  induction l; simpl in *; intros; try (inversion H).
  destruct d; simpl in *.
  rewrite Nat.sub_0_r. simpl. auto.
  destruct x; simpl in *; try lia.
  apply IHl; auto. lia.
Qed.

Lemma shift_at_typing : forall d G S t T T',
  has_type G S t T ->
  has_type (firstn d G ++ T' :: skipn d G) S (shift_at d t) T.
Proof.
  induction 1; simpl.
  apply T_Var. eapply nth_error_insert_shift; eauto.
  apply T_Num.
  apply T_Bool.
  apply T_Succ. apply IHhas_type.
  apply T_Pred. apply IHhas_type.
  apply T_IsZero. apply IHhas_type.
  apply T_If; try apply IHhas_type1; try apply IHhas_type2; try apply IHhas_type3.
  apply T_Lam.
  replace (firstn (S d) (T1 :: G) ++ T' :: skipn (S d) (T1 :: G))
    with (T1 :: firstn d G ++ T' :: skipn d G) by
    (simpl; rewrite firstn_cons, skipn_cons; reflexivity).
  apply IHhas_type.
  apply T_App; [apply IHhas_type1 | apply IHhas_type2].
  apply T_Fix.
  replace (firstn (S d) (T :: G) ++ T' :: skipn (S d) (T :: G))
    with (T :: firstn d G ++ T' :: skipn d G) by
    (simpl; rewrite firstn_cons, skipn_cons; reflexivity).
  apply IHhas_type.
  apply T_Ref. apply IHhas_type.
  apply T_Deref. apply IHhas_type.
  apply T_Assign; [apply IHhas_type1 | apply IHhas_type2].
  apply T_Loc. simpl. eapply nth_error_insert_shift; eauto.
Qed.

Lemma shift_typing : forall G S t T T',
  has_type G S t T -> has_type (T' :: G) S (shift t) T.
Proof.
  intros. unfold shift.
  replace (T' :: G) with (firstn 0 G ++ T' :: skipn 0 G) by reflexivity.
  apply shift_at_typing with (d := 0); auto.
Qed.

(** * Substitution lemma *)

Lemma firstn_skipn_id : forall {A} n (l : list A),
  firstn n l ++ skipn n l = l.
Proof.
  induction n; simpl; auto.
  destruct l; simpl; auto.
  rewrite IHn; auto.
Qed.

Lemma has_type_subst_gen : forall G j s t U T,
  has_type G s U ->
  (forall k, j < k -> nth_error (firstn j G ++ U :: skipn j G) k = None) ->
  has_type (firstn j G ++ U :: skipn j G) t T ->
  has_type (firstn j G ++ skipn j G) (subst j s t) T.
Proof.
  intros G j s t U T Hs Hnone Ht.
  revert G j s U Hs Hnone.
  induction Ht; intros G0 j0 s0 U0 Hs Hnone; simpl.
  - destruct (x =? j0) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst x.
      inversion H; subst; clear H.
      rewrite firstn_skipn_id; auto.
    + apply T_Var.
      inversion H; subst; clear H.
      assert (x < j0 \/ x > j0) as [Hlt|Hgt] by lia.
      * rewrite nth_error_app1.
        rewrite firstn_length.
        apply Nat.min_glb_lt.
        eapply nth_error_Some_length; eauto.
        apply Nat.ltb_lt; eauto.
        apply nth_error_app1 in H1.
        rewrite firstn_length.
        apply Nat.min_glb_lt.
        eapply nth_error_Some_length; eauto.
        apply Nat.ltb_lt; eauto.
        apply nth_error_app1.
        rewrite firstn_length.
        apply Nat.min_glb_lt.
        eapply nth_error_Some_length; eauto.
        apply Nat.ltb_lt; eauto.
        apply nth_error_firstn_some with (d := j0).
        -- lia.
        -- apply nth_error_app1 in H1; auto.
           rewrite firstn_length.
           apply Nat.min_glb_lt; eauto.
           eapply nth_error_Some_length; eauto.
      * exfalso.
        apply Hnone in Hgt.
        rewrite H1 in Hgt; inversion Hgt.
  - apply T_Num.
  - apply T_Bool.
  - apply T_Succ; eapply IHHt; eauto.
  - apply T_Pred; eapply IHHt; eauto.
  - apply T_IsZero; eapply IHHt; eauto.
  - apply T_If; eauto.
  - apply T_Lam.
    eapply IHHt with (G0 := T1 :: G0) (j0 := S j0) (s0 := shift s0) (U0 := U0).
    + apply shift_typing; auto.
    + intros k Hk.
      simpl; rewrite firstn_cons, skipn_cons.
      destruct k; simpl; try lia.
      rewrite <- firstn_skipn_id.
      apply Hnone; lia.
    + simpl; rewrite firstn_cons, skipn_cons; auto.
  - apply T_App; eauto.
  - apply T_Fix.
    eapply IHHt with (G0 := T :: G0) (j0 := S j0) (s0 := shift s0) (U0 := U0).
    + apply shift_typing; auto.
    + intros k Hk.
      simpl; rewrite firstn_cons, skipn_cons.
      destruct k; simpl; try lia.
      rewrite <- firstn_skipn_id.
      apply Hnone; lia.
    + simpl; rewrite firstn_cons, skipn_cons; auto.
  - apply T_Ref; eapply IHHt; eauto.
  - apply T_Deref; eapply IHHt; eauto.
  - apply T_Assign; eauto.
  - apply T_Loc; simpl.
    rewrite <- firstn_skipn_id.
    inversion H; subst.
    apply nth_error_insert_shift with (d := j0); auto.
Qed.

Lemma has_type_subst_0 : forall S s t U T,
  has_type [] S s U ->
  has_type [U] S t T ->
  has_type [] S (subst 0 s t) T.
Proof.
  intros.
  apply has_type_subst_gen with (G := []) (j := 0) (U := U); auto.
  intros k Hk; simpl; destruct k; simpl; try lia; auto.
Qed.

Lemma has_type_fix_subst : forall S t T,
  has_type [T] S t T ->
  has_type [] S (subst 0 (Fix t) t) T.
Proof.
  intros.
  apply has_type_subst_gen with (G := []) (j := 0) (U := T); auto.
  apply T_Fix with (G := []); simpl; auto.
  intros k Hk; simpl; destruct k; simpl; try lia; auto.
Qed.

(** * Type Preservation *)

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
  revert S T Ht.
  induction Hstep; intros S T Ht Hok.
  - (* S_Succ *)
    inversion Ht; subst.
    apply IHHstep in H3; auto.
    destruct H3 as [S' [Hext [Hok' Ht']]].
    exists S'; split; auto; split; auto.
    eapply has_type_weaken; eauto.
    econstructor; eauto.
  - (* S_PredZero *)
    inversion Ht; subst.
    inversion H3; subst.
    exists S; split; [apply extends_refl | split; auto].
    apply T_Num.
  - (* S_PredSucc *)
    inversion Ht; subst.
    inversion H3; subst.
    exists S; split; [apply extends_refl | split; auto].
    apply T_Num.
  - (* S_Pred *)
    inversion Ht; subst.
    apply IHHstep in H3; auto.
    destruct H3 as [S' [Hext [Hok' Ht']]].
    exists S'; split; auto; split; auto.
    eapply has_type_weaken; eauto.
    econstructor; eauto.
  - (* S_IsZeroZero *)
    inversion Ht; subst.
    inversion H3; subst.
    exists S; split; [apply extends_refl | split; auto].
    apply T_Bool.
  - (* S_IsZeroSucc *)
    inversion Ht; subst.
    inversion H3; subst.
    exists S; split; [apply extends_refl | split; auto].
    apply T_Bool.
  - (* S_IsZero *)
    inversion Ht; subst.
    apply IHHstep in H2; auto.
    destruct H2 as [S' [Hext [Hok' Ht']]].
    exists S'; split; auto; split; auto.
    eapply has_type_weaken; eauto.
    econstructor; eauto.
  - (* S_IfTrue *)
    inversion Ht; subst.
    exists S; split; [apply extends_refl | split; auto].
  - (* S_IfFalse *)
    inversion Ht; subst.
    exists S; split; [apply extends_refl | split; auto].
  - (* S_If *)
    inversion Ht; subst.
    apply IHHstep in H4; auto.
    destruct H4 as [S' [Hext [Hok' Ht']]].
    exists S'; split; auto; split; auto.
    eapply has_type_weaken; eauto.
    econstructor; eauto.
  - (* S_App1 *)
    inversion Ht; subst.
    apply IHHstep in H3; auto.
    destruct H3 as [S' [Hext [Hok' Ht']]].
    exists S'; split; auto; split; auto.
    eapply has_type_weaken; eauto.
    econstructor; eauto.
  - (* S_App2 *)
    inversion Ht; subst.
    apply IHHstep in H5; auto.
    destruct H5 as [S' [Hext [Hok' Ht']]].
    exists S'; split; auto; split; auto.
    eapply has_type_weaken; eauto.
    econstructor; eauto.
  - (* S_AppAbs *)
    inversion Ht; subst.
    inversion H3; subst.
    exists S; split; [apply extends_refl | split; auto].
    apply has_type_subst_0 with (U := T1); auto.
  - (* S_Fix *)
    inversion Ht; subst.
    inversion H3; subst.
    exists S; split; [apply extends_refl | split; auto].
    apply has_type_fix_subst; auto.
  - (* S_Ref *)
    inversion Ht; subst.
    apply IHHstep in H2; auto.
    destruct H2 as [S' [Hext [Hok' Ht']]].
    exists S'; split; auto; split; auto.
    eapply has_type_weaken; eauto.
    econstructor; eauto.
  - (* S_RefV *)
    inversion Ht; subst.
    exists (S ++ [T]).
    assert (Hext : extends (S ++ [T]) S).
    { exists [T]; reflexivity. }
    split; auto. split.
    apply heap_ok_extends with (S := S); auto.
    econstructor; eauto.
    apply nth_error_app2; simpl; lia.
    apply T_Loc.
    apply nth_error_app2; simpl; lia.
  - (* S_Deref *)
    inversion Ht; subst.
    apply IHHstep in H2; auto.
    destruct H2 as [S' [Hext [Hok' Ht']]].
    exists S'; split; auto; split; auto.
    eapply has_type_weaken; eauto.
    econstructor; eauto.
  - (* S_DerefLoc *)
    inversion Ht; subst.
    inversion H3; subst.
    eapply heap_lookup_ok in H5; eauto.
    exists S; split; [apply extends_refl | split; auto].
  - (* S_Assign1 *)
    inversion Ht; subst.
    apply IHHstep in H3; auto.
    destruct H3 as [S' [Hext [Hok' Ht']]].
    exists S'; split; auto; split; auto.
    eapply has_type_weaken; eauto.
    econstructor; eauto.
  - (* S_Assign2 *)
    inversion Ht; subst.
    apply IHHstep in H5; auto.
    destruct H5 as [S' [Hext [Hok' Ht']]].
    exists S'; split; auto; split; auto.
    eapply has_type_weaken; eauto.
    econstructor; eauto.
  - (* S_AssignV *)
    inversion Ht; subst.
    inversion H3; subst.
    exists S; split; [apply extends_refl | split; auto].
    apply T_Num.
    eapply heap_update_ok; eauto.
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
  intro H. apply H in preservation. exact preservation.
Qed.
