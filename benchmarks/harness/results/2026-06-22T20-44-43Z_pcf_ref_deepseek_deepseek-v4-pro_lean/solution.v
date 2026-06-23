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
  | T_Var : forall G S_ty x T, nth_error G x = Some T -> has_type G S_ty (Var x) T
  | T_Num : forall G S_ty n, has_type G S_ty (Num n) TyNat
  | T_Bool : forall G S_ty b, has_type G S_ty (BOOL b) TyBool
  | T_Succ : forall G S_ty t, has_type G S_ty t TyNat -> has_type G S_ty (Succ t) TyNat
  | T_Pred : forall G S_ty t, has_type G S_ty t TyNat -> has_type G S_ty (Pred t) TyNat
  | T_IsZero : forall G S_ty t, has_type G S_ty t TyNat -> has_type G S_ty (IsZero t) TyBool
  | T_If : forall G S_ty t1 t2 t3 T, has_type G S_ty t1 TyBool -> has_type G S_ty t2 T -> has_type G S_ty t3 T -> has_type G S_ty (If t1 t2 t3) T
  | T_Lam : forall G S_ty T1 T2 t, has_type (T1 :: G) S_ty t T2 -> has_type G S_ty (Lam T1 t) (TyArrow T1 T2)
  | T_App : forall G S_ty t1 t2 T1 T2, has_type G S_ty t1 (TyArrow T1 T2) -> has_type G S_ty t2 T1 -> has_type G S_ty (App t1 t2) T2
  | T_Fix : forall G S_ty t T, has_type (T :: G) S_ty t T -> has_type G S_ty (Fix t) T
  | T_Ref : forall G S_ty t T, has_type G S_ty t T -> has_type G S_ty (Ref t) (TyRef T)
  | T_Deref : forall G S_ty t T, has_type G S_ty t (TyRef T) -> has_type G S_ty (Deref t) T
  | T_Assign : forall G S_ty t1 t2 T, has_type G S_ty t1 (TyRef T) -> has_type G S_ty t2 T -> has_type G S_ty (Assign t1 t2) TyNat
  | T_Loc : forall G S_ty l T, nth_error S_ty l = Some T -> has_type G S_ty (Loc l) (TyRef T).

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
  | heap_empty : forall S_ty, heap_ok [] S_ty
  | heap_cons : forall l v mu S_ty T, heap_ok mu S_ty -> has_type [] S_ty v T -> nth_error S_ty l = Some T -> heap_ok ((l, v) :: mu) S_ty.

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

Definition extends (S' S0 : store_ty) : Prop := exists S2, S' = S0 ++ S2.

(** ** Auxiliary Lemmas *)

Lemma extends_refl : forall S_ty, extends S_ty S_ty.
Proof. intro S_ty. exists []. rewrite app_nil_r. reflexivity. Qed.

Lemma extends_app : forall S_ty S2, extends (S_ty ++ S2) S_ty.
Proof. intros. exists S2. auto. Qed.

Lemma nth_error_app_left : forall (A : Type) (l1 l2 : list A) (n : nat) (x : A),
  nth_error l1 n = Some x ->
  nth_error (l1 ++ l2) n = Some x.
Proof.
  induction l1; intros; simpl in *.
  - destruct n; inversion H.
  - destruct n; simpl; auto.
Qed.

Lemma nth_error_app_right : forall (A : Type) (l1 l2 : list A) (n : nat) (x : A),
  nth_error l2 n = Some x ->
  nth_error (l1 ++ l2) (length l1 + n) = Some x.
Proof.
  induction l1; intros; simpl.
  - auto.
  - apply IHl1. auto.
Qed.

Lemma nth_error_app_left_inv : forall (A : Type) (l1 l2 : list A) (n : nat) (x : A),
  n < length l1 ->
  nth_error (l1 ++ l2) n = Some x ->
  nth_error l1 n = Some x.
Proof.
  induction l1; intros; simpl in *.
  - lia.
  - destruct n; simpl in *; auto.
    apply IHl1 with (l2 := l2); auto. lia.
Qed.

Lemma nth_error_extends : forall S_ty S_ty' l T,
  extends S_ty' S_ty ->
  nth_error S_ty l = Some T ->
  nth_error S_ty' l = Some T.
Proof.
  intros S_ty S_ty' l T [S2 ->] H.
  apply nth_error_app_left. exact H.
Qed.

Lemma nth_error_app_singleton : forall (A : Type) (G : list A) (U : A),
  nth_error (G ++ [U]) (length G) = Some U.
Proof. induction G; simpl; auto. Qed.

Lemma has_type_weakening_store : forall G S_ty t T S_ty2,
  has_type G S_ty t T ->
  extends S_ty2 S_ty ->
  has_type G S_ty2 t T.
Proof.
  intros G S_ty t T S_ty2 Ht Hext.
  revert S_ty2 Hext.
  induction Ht; intros S_ty2 Hext.
  - apply T_Var; auto.
  - apply T_Num.
  - apply T_Bool.
  - apply T_Succ; apply IHHt; auto.
  - apply T_Pred; apply IHHt; auto.
  - apply T_IsZero; apply IHHt; auto.
  - apply T_If; [apply IHHt1 | apply IHHt2 | apply IHHt3]; auto.
  - apply T_Lam; apply IHHt; auto.
  - eapply T_App; [apply IHHt1 | apply IHHt2]; auto.
  - apply T_Fix; apply IHHt; auto.
  - apply T_Ref; apply IHHt; auto.
  - apply T_Deref; apply IHHt; auto.
  - eapply T_Assign; [apply IHHt1 | apply IHHt2]; auto.
  - apply T_Loc. eapply nth_error_extends; eauto.
Qed.

Lemma heap_ok_extends : forall mu S_ty S_ty2,
  heap_ok mu S_ty ->
  extends S_ty2 S_ty ->
  heap_ok mu S_ty2.
Proof.
  intros mu S_ty S_ty2 Hok Hext.
  revert S_ty2 Hext.
  induction Hok; intros S_ty2 Hext.
  - apply heap_empty.
  - refine (heap_cons l v mu S_ty2 T _ _ _).
    + apply IHHok; auto.
    + eapply has_type_weakening_store; eauto.
    + eapply nth_error_extends; eauto.
Qed.

(** ** Store Typing Extension for Allocation *)

Fixpoint replicate_ty (n : nat) : store_ty :=
  match n with
  | 0 => []
  | S n' => TyNat :: replicate_ty n'
  end.

Lemma length_replicate_ty : forall n, length (replicate_ty n) = n.
Proof. induction n; simpl; auto. Qed.

Definition store_extend (S_ty : store_ty) (n : nat) (T : ty) : store_ty :=
  S_ty ++ replicate_ty (n - length S_ty) ++ [T].

Lemma store_extend_extends : forall S_ty n T,
  extends (store_extend S_ty n T) S_ty.
Proof.
  intros. unfold store_extend.
  exists (replicate_ty (n - length S_ty) ++ [T]). auto.
Qed.

Lemma nth_error_pad_right : forall k T,
  nth_error (replicate_ty k ++ [T]) k = Some T.
Proof.
  induction k; simpl; auto.
Qed.

Lemma nth_error_store_extend : forall S_ty n T,
  n >= length S_ty ->
  nth_error (store_extend S_ty n T) n = Some T.
Proof.
  intros S_ty n T Hge. unfold store_extend.
  assert (Hn : n = length S_ty + (n - length S_ty)) by lia.
  set (k := n - length S_ty).
  rewrite Hn at 1.
  apply nth_error_app_right.
  apply nth_error_pad_right.
Qed.

Lemma length_store_extend : forall S_ty n T,
  n >= length S_ty ->
  length (store_extend S_ty n T) = S n.
Proof.
  intros S_ty n T Hge. unfold store_extend.
  rewrite !length_app. cbn.
  rewrite length_replicate_ty. lia.
Qed.

(** ** Shift Lemma *)

Lemma nth_error_shift_lt : forall (A : Type) (G1 G2 : list A) (U : A) x T,
  x < length G1 ->
  nth_error (G1 ++ G2) x = Some T ->
  nth_error (G1 ++ U :: G2) x = Some T.
Proof.
  induction G1 as [|a G1]; intros G2 U x T Hlt Hnth; simpl in *.
  - lia.
  - destruct x; simpl in *.
    + auto.
    + apply IHG1 with (G2 := G2) (U := U); lia || auto.
Qed.

Lemma nth_error_shift_ge : forall (A : Type) (G1 G2 : list A) (U : A) x T,
  x >= length G1 ->
  nth_error (G1 ++ G2) x = Some T ->
  nth_error (G1 ++ U :: G2) (x + 1) = Some T.
Proof.
  induction G1 as [|a G1]; intros G2 U x T Hge Hnth; simpl in *.
  - rewrite Nat.add_1_r. auto.
  - destruct x; simpl in *.
    + inversion Hge.
    + apply IHG1 with (G2 := G2) (U := U); lia || auto.
Qed.

Lemma shift_at_typing_Var : forall G1 G2 S_ty x T U,
  nth_error (G1 ++ G2) x = Some T ->
  has_type (G1 ++ U :: G2) S_ty (shift_at (length G1) (Var x)) T.
Proof.
  intros G1 G2 S_ty x T U H.
  unfold shift_at.
  destruct (Nat.ltb x (length G1)) eqn:Heq; simpl.
  - apply T_Var. eapply nth_error_shift_lt; eauto. apply Nat.ltb_lt; auto.
  - apply T_Var.
    revert x H Heq.
    induction G1 as [|a G1]; intros x H Heq; simpl in *.
    + rewrite Nat.add_1_r. exact H.
    + destruct (Compare_dec.le_lt_dec (S (length G1)) x).
      * destruct x as [|x']; simpl in *.
        { inversion l. }
        { apply IHG1; [exact H | exact Heq]. }
      * exfalso.
        assert (x < S (length G1)) by lia.
        apply (proj2 (Nat.ltb_lt x (S (length G1)))) in H0.
        rewrite H0 in Heq. discriminate.
Qed.

Lemma shift_at_typing : forall G1 G2 S_ty t T U,
  has_type (G1 ++ G2) S_ty t T ->
  has_type (G1 ++ U :: G2) S_ty (shift_at (length G1) t) T.
Proof.
  intros G1 G2 S_ty t T U Ht.
  remember (G1 ++ G2) as G eqn:HeqG.
  revert G1 G2 U HeqG.
  induction Ht; intros G1 G2 U HeqG; subst G; simpl.
  - (* T_Var *)
    apply shift_at_typing_Var; auto.
  - (* T_Num *) apply T_Num.
  - (* T_Bool *) apply T_Bool.
  - (* T_Succ *) apply T_Succ. apply IHHt; reflexivity.
  - (* T_Pred *) apply T_Pred. apply IHHt; reflexivity.
  - (* T_IsZero *) apply T_IsZero. apply IHHt; reflexivity.
  - (* T_If *)
    apply T_If; [apply IHHt1 | apply IHHt2 | apply IHHt3]; reflexivity.
  - (* T_Lam *)
    eapply T_Lam.
    replace (T1 :: G1 ++ U :: G2) with ((T1 :: G1) ++ U :: G2) by reflexivity.
    replace (S (length G1)) with (length (T1 :: G1)) by reflexivity.
    apply IHHt; reflexivity.
  - (* T_App *)
    eapply T_App; [apply IHHt1 | apply IHHt2]; reflexivity.
  - (* T_Fix *)
    eapply T_Fix.
    replace (T :: G1 ++ U :: G2) with ((T :: G1) ++ U :: G2) by reflexivity.
    replace (S (length G1)) with (length (T :: G1)) by reflexivity.
    apply IHHt; reflexivity.
  - (* T_Ref *) apply T_Ref. apply IHHt; reflexivity.
  - (* T_Deref *) apply T_Deref. apply IHHt; reflexivity.
  - (* T_Assign *)
    eapply T_Assign; [apply IHHt1 | apply IHHt2]; reflexivity.
  - (* T_Loc *) apply T_Loc. auto.
Qed.

Lemma shift_typing : forall G S_ty t T U,
  has_type G S_ty t T ->
  has_type (U :: G) S_ty (shift t) T.
Proof.
  intros G S_ty t T U H.
  unfold shift.
  replace (U :: G) with (([] : ctx) ++ U :: G) by reflexivity.
  replace G with (([] : ctx) ++ G) by reflexivity.
  apply shift_at_typing with (G1 := [] : ctx) (G2 := G); auto.
Qed.

(** ** Substitution Lemma *)

Lemma subst_preserves_typing : forall Gamma ST s t T U,
  has_type (Gamma ++ [U]) ST t T ->
  has_type Gamma ST s U ->
  has_type Gamma ST (subst (length Gamma) s t) T.
Proof.
  intros Gamma ST s t T U Ht Hs.
  revert Gamma ST s T U Hs Ht.
  induction t; intros Gamma ST s T U Hs Ht; inversion Ht; subst; simpl.
  - (* Var *)
    simpl.
    case_eq (Nat.eqb n (length Gamma)); intro Heq.
    + apply Nat.eqb_eq in Heq. subst n. simpl.
      rewrite nth_error_app_singleton in H. inversion H; subst. exact Hs.
    + apply T_Var.
      assert (n < length Gamma \/ n > length Gamma) as [Hlt | Hgt] by (apply Nat.eqb_neq in Heq; lia).
      * apply nth_error_app_left_inv with (l2 := [U]) in H; auto.
      * exfalso.
        assert (Hnone : nth_error (Gamma ++ [U]) n = None).
        { apply nth_error_None. rewrite app_length. simpl. lia. }
        rewrite Hnone in H. inversion H.
  - (* Num *) apply T_Num.
  - (* Bool *) apply T_Bool.
  - (* Succ *) apply T_Succ; apply (IHt Gamma ST s TyNat U Hs H).
  - (* Pred *) apply T_Pred; apply (IHt Gamma ST s TyNat U Hs H).
  - (* IsZero *) apply T_IsZero; apply (IHt Gamma ST s TyNat U Hs H).
  - (* If *)
    eapply T_If;
      [apply (IHt1 Gamma ST s TyBool U Hs H)
      |apply (IHt2 Gamma ST s T U Hs H0)
      |apply (IHt3 Gamma ST s T U Hs H1)].
  - (* Lam *)
    apply T_Lam with (T1 := T1) (T2 := T2).
    apply (IHt (T1 :: Gamma) ST (shift s) T2 U); [apply shift_typing; auto | exact H].
  - (* App *)
    eapply T_App;
      [apply (IHt1 Gamma ST s (TyArrow T1 T2) U Hs H)
      |apply (IHt2 Gamma ST s T1 U Hs H0)].
  - (* Fix *)
    apply T_Fix with (T := T0).
    apply (IHt (T0 :: Gamma) ST (shift s) T0 U); [apply shift_typing; auto | exact H].
  - (* Ref *) apply T_Ref. apply (IHt Gamma ST s T0 U Hs H).
  - (* Deref *) apply T_Deref. apply (IHt Gamma ST s (TyRef T0) U Hs H).
  - (* Assign *)
    eapply T_Assign;
      [apply (IHt1 Gamma ST s (TyRef T0) U Hs H)
      |apply (IHt2 Gamma ST s T0 U Hs H0)].
  - (* Loc *) apply T_Loc. auto.
Qed.

(** ** Heap Lemmas *)

Lemma heap_lookup_ok : forall mu S_ty l v,
  heap_ok mu S_ty ->
  heap_lookup l mu = Some v ->
  exists T, nth_error S_ty l = Some T /\ has_type [] S_ty v T.
Proof.
  induction mu as [|[l' v'] mu']; intros S_ty l v Hok Hlook; simpl in *.
  - inversion Hlook.
  - destruct (Nat.eqb_spec l l').
    + subst. inversion Hok; subst. injection Hlook; intros; subst.
      exists T. auto.
    + inversion Hok; subst.
      apply IHmu' with (S_ty := S_ty) (l := l) (v := v); auto.
      destruct (Nat.eqb l l') eqn:Heq; [contradiction | auto].
Qed.

Lemma length_heap_update : forall mu l v,
  length (heap_update l v mu) = length mu.
Proof.
  induction mu as [|[l' v'] mu']; intros; simpl.
  - auto.
  - destruct (Nat.eqb_spec l l'); subst; simpl; auto.
Qed.

Lemma heap_update_ok : forall mu S_ty l v T,
  heap_ok mu S_ty ->
  nth_error S_ty l = Some T ->
  has_type [] S_ty v T ->
  heap_ok (heap_update l v mu) S_ty.
Proof.
  induction 1; intros Hnth Hv; simpl.
  - apply heap_empty.
  - destruct (Nat.eqb_spec l0 l).
    + subst. injection H1; intros; subst.
      apply heap_cons with (T := T0); auto.
      apply IHheap_ok; auto.
    + apply heap_cons with (T := T0); auto.
      apply IHheap_ok; auto.
Qed.

(** ** Main Preservation Theorem *)

Lemma preservation_lemma : forall t mu t' mu',
  step t mu t' mu' ->
  forall S_ty T,
  has_type [] S_ty t T ->
  heap_ok mu S_ty ->
  length mu >= length S_ty ->
  exists S_ty',
    extends S_ty' S_ty /\
    heap_ok mu' S_ty' /\
    has_type [] S_ty' t' T /\
    length mu' >= length S_ty'.
Proof.
  induction 1; intros S_ty T Ht Hok Hlen.
  - (* S_Succ *)
    inversion Ht; subst.
    destruct (IHstep S_ty TyNat H2 Hok Hlen) as [S_ty' [Hext [Hok' [Ht' Hlen']]]].
    exists S_ty'. split; auto. split; auto. split.
    + apply T_Succ; auto.
    + auto.
  - (* S_PredZero *)
    inversion Ht; subst. inversion H3; subst.
    exists S_ty. split; [apply extends_refl |]. split; auto. split.
    + apply T_Num.
    + auto.
  - (* S_PredSucc *)
    inversion Ht; subst. inversion H3; subst.
    exists S_ty. split; [apply extends_refl |]. split; auto. split.
    + apply T_Num.
    + auto.
  - (* S_Pred *)
    inversion Ht; subst.
    destruct (IHstep S_ty TyNat H2 Hok Hlen) as [S_ty' [Hext [Hok' [Ht' Hlen']]]].
    exists S_ty'. split; auto. split; auto. split.
    + apply T_Pred; auto.
    + auto.
  - (* S_IsZeroZero *)
    inversion Ht; subst. inversion H3; subst.
    exists S_ty. split; [apply extends_refl |]. split; auto. split.
    + apply T_Bool.
    + auto.
  - (* S_IsZeroSucc *)
    inversion Ht; subst. inversion H3; subst.
    exists S_ty. split; [apply extends_refl |]. split; auto. split.
    + apply T_Bool.
    + auto.
  - (* S_IsZero *)
    inversion Ht; subst.
    destruct (IHstep S_ty TyNat H2 Hok Hlen) as [S_ty' [Hext [Hok' [Ht' Hlen']]]].
    exists S_ty'. split; auto. split; auto. split.
    + apply T_IsZero; auto.
    + auto.
  - (* S_IfTrue *)
    inversion Ht; subst.
    exists S_ty. split; [apply extends_refl |]. split; auto. split; auto.
  - (* S_IfFalse *)
    inversion Ht; subst.
    exists S_ty. split; [apply extends_refl |]. split; auto. split; auto.
  - (* S_If *)
    inversion Ht; subst.
    destruct (IHstep S_ty TyBool H2 Hok Hlen) as [S_ty' [Hext [Hok' [Ht' Hlen']]]].
    exists S_ty'. split; auto. split; auto. split.
    + apply T_If; auto; eapply has_type_weakening_store; eauto.
    + auto.
  - (* S_App1 *)
    inversion Ht; subst.
    destruct (IHstep S_ty (TyArrow T1 T) H2 Hok Hlen) as [S_ty' [Hext [Hok' [Ht' Hlen']]]].
    exists S_ty'. split; auto. split; auto. split.
    + apply T_App with (T1 := T1); auto. eapply has_type_weakening_store; eauto.
    + auto.
  - (* S_App2 *)
    inversion Ht; subst.
    destruct (IHstep S_ty T1 H4 Hok Hlen) as [S_ty' [Hext [Hok' [Ht' Hlen']]]].
    exists S_ty'. split; auto. split; auto. split.
    + apply T_App with (T1 := T1); auto. eapply has_type_weakening_store; eauto.
    + auto.
  - (* S_AppAbs *)
    inversion Ht; subst.
    inversion H2; subst.
    exists S_ty. split; [apply extends_refl |]. split; auto. split.
    + eapply (subst_preserves_typing [] S_ty v2 t T2 T1); eauto.
    + auto.
  - (* S_Fix *)
    inversion Ht; subst.
    exists S_ty. split; [apply extends_refl |]. split; auto. split.
    + eapply (subst_preserves_typing [] S_ty (Fix t) t T T); eauto.
      apply H2.
    + auto.
  - (* S_Ref *)
    inversion Ht; subst.
    destruct (IHstep S_ty T0 H2 Hok Hlen) as [S_ty' [Hext [Hok' [Ht' Hlen']]]].
    exists S_ty'. split; auto. split; auto. split.
    + apply T_Ref; auto.
    + auto.
  - (* S_RefV *)
    inversion Ht; subst.
    set (S_ty' := store_extend S_ty (length mu) T0).
    exists S_ty'. split.
    { apply store_extend_extends. }
    split.
    { apply heap_cons with (T := T0).
      - apply heap_ok_extends with (S_ty := S_ty); auto. apply store_extend_extends.
      - eapply has_type_weakening_store; eauto. apply store_extend_extends.
      - apply nth_error_store_extend. auto. }
    split.
    { apply T_Loc. apply nth_error_store_extend. auto. }
    { simpl. rewrite (length_store_extend S_ty (length mu) T0 Hlen). lia. }
  - (* S_Deref *)
    inversion Ht; subst.
    destruct (IHstep S_ty (TyRef T) H2 Hok Hlen) as [S_ty' [Hext [Hok' [Ht' Hlen']]]].
    exists S_ty'. split; auto. split; auto. split.
    + apply T_Deref; auto.
    + auto.
  - (* S_DerefLoc *)
    inversion Ht; subst. inversion H2; subst.
    destruct (heap_lookup_ok mu S_ty l v Hok H4) as [T' [Hnth Hv]].
    rewrite Hnth in H3. injection H3; intros; subst.
    exists S_ty. split; [apply extends_refl |]. split; auto. split; auto.
  - (* S_Assign1 *)
    inversion Ht; subst.
    destruct (IHstep S_ty (TyRef T) H2 Hok Hlen) as [S_ty' [Hext [Hok' [Ht' Hlen']]]].
    exists S_ty'. split; auto. split; auto. split.
    + apply T_Assign with (T := T); auto. eapply has_type_weakening_store; eauto.
    + auto.
  - (* S_Assign2 *)
    inversion Ht; subst. inversion H2; subst.
    destruct (IHstep S_ty T0 H6 Hok Hlen) as [S_ty' [Hext [Hok' [Ht' Hlen']]]].
    exists S_ty'. split; auto. split; auto. split.
    + apply T_Assign with (T := T0); auto. eapply has_type_weakening_store; eauto.
    + auto.
  - (* S_AssignV *)
    inversion Ht; subst. inversion H2; subst.
    exists S_ty. split; [apply extends_refl |]. split.
    + apply heap_update_ok with (T := T); auto.
    + split.
      * apply T_Num.
      * rewrite length_heap_update. auto.
Qed.

(** ** Conjecture pairs
     For each conjecture, both the statement and its negation are given.
     Prove exactly one of each pair. *)

Theorem preservation :
  forall t mu t' mu' T S_ty,
    has_type [] S_ty t T ->
    step t mu t' mu' ->
    heap_ok mu S_ty ->
    length mu >= length S_ty ->
    exists S_ty',
      extends S_ty' S_ty /\
      heap_ok mu' S_ty' /\
      has_type [] S_ty' t' T.
Proof.
  intros t mu t' mu' T S_ty Ht Hstep Hok Hlen.
  destruct (preservation_lemma t mu t' mu' Hstep S_ty T Ht Hok Hlen) as [S_ty' [Hext [Hok' [Ht' _]]]].
  exists S_ty'. auto.
Qed.

Theorem preservation_neg : ~ (
  forall t mu t' mu' T S_ty,
    has_type [] S_ty t T ->
    step t mu t' mu' ->
    heap_ok mu S_ty ->
    length mu >= length S_ty ->
    exists S_ty',
      extends S_ty' S_ty /\
      heap_ok mu' S_ty' /\
      has_type [] S_ty' t' T).
Proof.
Admitted.
