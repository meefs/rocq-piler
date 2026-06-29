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

Lemma nth_error_app_Some : forall A (l1 l2 : list A) n x,
  nth_error l1 n = Some x -> nth_error (l1 ++ l2) n = Some x.
Proof.
  intros A l1 l2 n x H.
  revert l1 H.
  induction n; intros l1 H.
  - destruct l1; unfold nth_error in H; simpl in H.
    + inversion H.
    + inversion H; subst; auto.
  - destruct l1; unfold nth_error in H; simpl in H; unfold nth_error; simpl.
    + inversion H.
    + apply IHn. exact H.
Qed.

Lemma extends_refl : forall S, extends S S.
Proof. intros S. exists []. rewrite app_nil_r. auto. Qed.

Lemma extends_append : forall S S', extends (S ++ S') S.
Proof. intros S S'. exists S'. auto. Qed.

Lemma extends_trans : forall S1 S2 S3, extends S1 S2 -> extends S2 S3 -> extends S1 S3.
Proof.
  intros S1 S2 S3 H12 H23.
  destruct H12 as [S12 HS12].
  destruct H23 as [S23 HS23].
  subst.
  exists (S23 ++ S12).
  rewrite app_assoc. auto.
Qed.

Lemma nth_error_app_l : forall A (l1 l2 : list A) n,
  n < length l1 -> nth_error (l1 ++ l2) n = nth_error l1 n.
Proof.
  induction l1; intros l2 n H; simpl in H; try lia.
  destruct n; simpl; auto.
  apply IHl1. lia.
Qed.

Lemma has_type_store_extends : forall G S t T S',
  has_type G S t T -> extends S' S -> has_type G S' t T.
Proof.
  intros G S t T S' Ht Hext.
  revert S' Hext.
  induction Ht; intros S' Hext.
  - apply T_Var; auto.
  - apply T_Num.
  - apply T_Bool.
  - eapply T_Succ; eauto.
  - eapply T_Pred; eauto.
  - eapply T_IsZero; eauto.
  - eapply T_If; eauto.
  - eapply T_Lam; eauto.
  - eapply T_App; eauto.
  - eapply T_Fix; eauto.
  - eapply T_Ref; eauto.
  - eapply T_Deref; eauto.
  - eapply T_Assign; eauto.
  - destruct Hext as [S2 HS2]; subst.
    apply T_Loc. apply nth_error_app_Some. exact H.
Qed.

Lemma heap_ok_store_extends : forall mu S S',
  heap_ok mu S -> extends S' S -> heap_ok mu S'.
Proof.
  intros mu S S' Hok Hext.
  induction Hok as [S0 | l v mu S0 T Hok' IH Ht Hnth].
  - apply heap_empty.
  - destruct Hext as [S2 HS2]; subst.
    apply heap_cons with (T := T).
    + apply IH; exists S2; auto.
    + apply has_type_store_extends with (S := S0); auto.
      exists S2; auto.
    + apply nth_error_app_Some; exact Hnth.
Qed.

Lemma heap_ok_lookup : forall mu S l v T,
  heap_ok mu S ->
  heap_lookup l mu = Some v ->
  nth_error S l = Some T ->
  has_type [] S v T.
Proof.
  induction mu as [| [l' v'] mu']; intros S l v T Hok Hlook Hnth; simpl in Hlook.
  - discriminate.
  - inversion Hok as [| l'' v'' mu'' S'' T'' Hok' Ht Hnth']; subst; clear Hok.
    destruct (Nat.eqb l l') eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst.
      inversion Hlook; subst; clear Hlook.
      rewrite Hnth' in Hnth; inversion Hnth; subst; auto.
    + eapply IHmu'; eauto.
Qed.

Lemma heap_ok_update : forall mu S l v T,
  heap_ok mu S ->
  nth_error S l = Some T ->
  has_type [] S v T ->
  heap_ok (heap_update l v mu) S.
Proof.
  intros mu S l v T Hok Hnth Htv.
  induction Hok as [S0 | l' v' mu' S0 T' Hok' IH Ht' Hnth'].
  - apply heap_empty.
  - simpl. destruct (Nat.eqb l l') eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst l'.
      apply heap_cons with (T := T); auto.
    + apply heap_cons with (T := T'); auto.
Qed.

Lemma has_type_value_nat : forall S v,
  has_type [] S v TyNat -> value v -> exists n, v = Num n.
Proof.
  intros S v Ht Hv. inversion Hv; subst.
  - exists n; auto.
  - inversion Ht.
  - inversion Ht.
  - inversion Ht.
Qed.

Lemma has_type_value_bool : forall S v,
  has_type [] S v TyBool -> value v -> exists b, v = BOOL b.
Proof.
  intros S v Ht Hv. inversion Hv; subst.
  - inversion Ht.
  - exists b; auto.
  - inversion Ht.
  - inversion Ht.
Qed.

Lemma has_type_value_arrow : forall S v T1 T2,
  has_type [] S v (TyArrow T1 T2) -> value v -> exists t, v = Lam T1 t.
Proof.
  intros S v T1 T2 Ht Hv. inversion Hv; subst.
  - inversion Ht.
  - inversion Ht.
  - inversion Ht; subst; exists t; auto.
  - inversion Ht.
Qed.

Lemma has_type_value_ref : forall S v T,
  has_type [] S v (TyRef T) -> value v -> exists l, v = Loc l.
Proof.
  intros S v T Ht Hv. inversion Hv; subst.
  - inversion Ht.
  - inversion Ht.
  - inversion Ht.
  - exists l; auto.
Qed.

Lemma nth_error_Some_length : forall A (l : list A) n x,
  nth_error l n = Some x -> n < length l.
Proof. intros A l n x H. apply -> nth_error_Some. congruence. Qed.

Lemma nth_error_shift_insert : forall A (l : list A) d x (U y : A),
  nth_error l x = Some y ->
  nth_error (firstn d l ++ U :: skipn d l) (if x <? d then x else x+1) = Some y.
Proof.
  intros A l d x U y H.
  destruct (x <? d) eqn:Hxd.
  - apply Nat.ltb_lt in Hxd.
    rewrite nth_error_app1.
    + rewrite nth_error_firstn. rewrite (proj2 (Nat.ltb_lt x d) Hxd). exact H.
    + rewrite length_firstn. assert (x < length l). { apply nth_error_Some. intro Hc. rewrite H in Hc. discriminate. } lia.
  - apply Nat.ltb_ge in Hxd.
    rewrite nth_error_app2.
    { rewrite length_firstn.
      rewrite Nat.min_l.
      - replace (x + 1 - d) with (S (x - d)) by lia.
        simpl. rewrite nth_error_skipn.
        replace (d + (x - d)) with x by lia.
        exact H.
      - assert (x < length l). { apply nth_error_Some. intro Hc. rewrite H in Hc. discriminate. } lia. }
    { rewrite length_firstn. assert (x < length l). { apply nth_error_Some. intro Hc. rewrite H in Hc. discriminate. } lia. }
Qed.

Lemma nth_error_cons_S : forall A (a:A) (l:list A) n,
  nth_error (a :: l) (S n) = nth_error l n.
Proof. intros. unfold nth_error. reflexivity. Qed.

Lemma nth_error_shift_ge : forall A (l : list A) d x (U y : A),
  nth_error l x = Some y ->
  d <= x ->
  nth_error (U :: skipn d l) (x + 1 - d) = Some y.
Proof.
  intros A l d x U y Hnth Hge.
  assert (Heq: x + 1 - d = (x - d) + 1) by lia.
  rewrite Heq.
  rewrite Nat.add_1_r.
  rewrite nth_error_cons_S.
  rewrite nth_error_skipn.
  replace (d + (x - d)) with x by lia.
  exact Hnth.
Qed.

Lemma has_type_shift_at : forall G St d t T U,
  has_type G St t T ->
  has_type (firstn d G ++ U :: skipn d G) St (shift_at d t) T.
Proof.
  intros G St d t T U Ht.
  revert d.
  induction Ht; intros d; simpl.
  - destruct (x <? d) eqn:Hx.
    + apply T_Var. rewrite nth_error_app1.
      * rewrite nth_error_firstn. rewrite Hx. exact H.
      * rewrite length_firstn. apply Nat.ltb_lt in Hx. assert (x < length G). { apply nth_error_Some. intro Hc. rewrite H in Hc. discriminate. } lia.
    + apply T_Var. apply Nat.ltb_ge in Hx. rewrite nth_error_app2.
      * rewrite length_firstn. rewrite Nat.min_l.
        { apply nth_error_shift_ge with (U := U); auto. }
        { assert (x < length G). { apply nth_error_Some. intro Hc. rewrite H in Hc. discriminate. } lia. }
      * rewrite length_firstn. assert (x < length G). { apply nth_error_Some. intro Hc. rewrite H in Hc. discriminate. } lia.
  - apply T_Num.
  - apply T_Bool.
  - apply T_Succ. apply IHHt.
  - apply T_Pred. apply IHHt.
  - apply T_IsZero. apply IHHt.
  - eapply T_If; [apply IHHt1|apply IHHt2|apply IHHt3].
  - apply T_Lam. simpl. apply (IHHt (1 + d)).
  - eapply T_App; [apply IHHt1|apply IHHt2].
  - apply T_Fix. simpl. apply (IHHt (1 + d)).
  - apply T_Ref. apply IHHt.
  - apply T_Deref. apply IHHt.
  - eapply T_Assign; [apply IHHt1|apply IHHt2].
  - apply T_Loc. auto.
Qed.

Lemma has_type_shift_gen : forall G S t T U,
  has_type G S t T ->
  has_type (U :: G) S (shift t) T.
Proof.
  intros. apply has_type_shift_at with (d := 0); auto.
Qed.

Lemma nth_error_skip_firstn : forall A (l : list A) j x y,
  nth_error l x = Some y ->
  x <> j ->
  nth_error (firstn j l ++ skipn j l) x = Some y.
Proof.
  induction l as [|a l' IH]; intros j x y Hnth Hneq; simpl.
  - destruct x; simpl in Hnth; discriminate.
  - destruct j; simpl.
    + (* j = 0 *) simpl. exact Hnth.
    + (* j = S j *)
      destruct x; simpl in Hnth.
      * (* x = 0 *) simpl. exact Hnth.
      * (* x = S x *) simpl. apply IH with (j := j); auto.
Qed.

Lemma has_type_subst_gen : forall G St j s t T U,
  has_type G St s U ->
  has_type (firstn j G ++ U :: skipn j G) St t T ->
  has_type (firstn j G ++ skipn j G) St (subst j s t) T.
Proof.
  intros G St j s t T U Hs.
  revert G j s Hs.
  induction 2; intros G' j' s' Hs'; simpl.
  - apply T_Var in H0; auto.
    destruct (Nat.eqb x j') eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst.
      apply nth_error_app2 in H0; [| rewrite length_firstn; apply Nat.le_min_l].
      simpl in H0.
      rewrite length_firstn in H0.
      destruct (j' - length (firstn j' G')) eqn:Hd.
      * inversion H0; subst. rewrite firstn_skipn. exact Hs'.
      * exfalso.
        apply nth_error_Some in H0. simpl in H0.
        rewrite skipn_length in H0. lia.
    + apply T_Var.
      apply nth_error_skip_firstn; auto.
      intro Heqx. apply Nat.eqb_neq in Heq. auto.
  - apply T_Num.
  - apply T_Bool.
  - apply T_Succ. eapply IHhas_type; eauto.
  - apply T_Pred. eapply IHhas_type; eauto.
  - apply T_IsZero. eapply IHhas_type; eauto.
  - apply T_If.
    + eapply IHhas_type1; eauto.
    + eapply IHhas_type2; eauto.
    + eapply IHhas_type3; eauto.
  - apply T_Lam.
    eapply IHhas_type.
    + apply has_type_shift_gen. exact Hs'.
    + simpl. rewrite firstn_cons, skipn_cons. auto.
  - apply T_App.
    + eapply IHhas_type1; eauto.
    + eapply IHhas_type2; eauto.
  - apply T_Fix.
    eapply IHhas_type.
    + apply has_type_shift_gen. exact Hs'.
    + simpl. rewrite firstn_cons, skipn_cons. auto.
  - apply T_Ref. eapply IHhas_type; eauto.
  - apply T_Deref. eapply IHhas_type; eauto.
  - apply T_Assign.
    + eapply IHhas_type1; eauto.
    + eapply IHhas_type2; eauto.
  - apply T_Loc. auto.
Qed.

Lemma has_type_subst0 : forall S v t T U,
  has_type [] S v U ->
  has_type [U] S t T ->
  has_type [] S (subst 0 v t) T.
Proof.
  intros S v t T U Hv Ht.
  apply has_type_subst_gen with (G := []) (j := 0) (s := v) (U := U); auto.
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
  intros t mu t' mu' T S Ht Hstep Hok Hlen.
  revert T Ht.
  induction Hstep; intros T Ht; inversion Ht; subst.
  - (* S_Succ *)
    apply IHHstep in H3; auto.
    destruct H3 as [S' [Hext [Hok' Ht']]].
    exists S'; split; [|split]; auto.
    apply T_Succ; auto.
  - (* S_PredZero *)
    exists S; split; [apply extends_refl|split; auto].
    apply T_Num.
  - (* S_PredSucc *)
    exists S; split; [apply extends_refl|split; auto].
    apply T_Num.
  - (* S_Pred *)
    apply IHHstep in H3; auto.
    destruct H3 as [S' [Hext [Hok' Ht']]].
    exists S'; split; [|split]; auto.
    apply T_Pred; auto.
  - (* S_IsZeroZero *)
    exists S; split; [apply extends_refl|split; auto].
    apply T_Bool.
  - (* S_IsZeroSucc *)
    exists S; split; [apply extends_refl|split; auto].
    apply T_Bool.
  - (* S_IsZero *)
    apply IHHstep in H3; auto.
    destruct H3 as [S' [Hext [Hok' Ht']]].
    exists S'; split; [|split]; auto.
    apply T_IsZero; auto.
  - (* S_IfTrue *)
    exists S; split; [apply extends_refl|split; auto].
  - (* S_IfFalse *)
    exists S; split; [apply extends_refl|split; auto].
  - (* S_If *)
    apply IHHstep in H6; auto.
    destruct H6 as [S' [Hext [Hok' Ht']]].
    exists S'; split; [|split]; auto.
    eapply T_If; eauto.
    + eapply has_type_store_extends; eauto.
    + eapply has_type_store_extends; eauto.
  - (* S_App1 *)
    apply IHHstep in H4; auto.
    destruct H4 as [S' [Hext [Hok' Ht']]].
    exists S'; split; [|split]; auto.
    eapply T_App; eauto.
    eapply has_type_store_extends; eauto.
  - (* S_App2 *)
    apply IHHstep in H6; auto.
    destruct H6 as [S' [Hext [Hok' Ht']]].
    exists S'; split; [|split]; auto.
    eapply T_App; eauto.
    eapply has_type_store_extends; eauto.
  - (* S_AppAbs *)
    inversion H4; subst.
    exists S; split; [apply extends_refl|split; auto].
    apply has_type_subst0 with (U := T0); auto.
  - (* S_Fix *)
    exists S; split; [apply extends_refl|split; auto].
    apply has_type_subst0 with (U := T); auto.
  - (* S_Ref *)
    apply IHHstep in H3; auto.
    destruct H3 as [S' [Hext [Hok' Ht']]].
    exists S'; split; [|split]; auto.
    apply T_Ref; auto.
  - (* S_RefV *)
    inversion H3; subst; clear H3.
    remember (length mu - length S) as n.
    exists (S ++ repeat T0 n ++ [T0]).
    split.
    { exists (repeat T0 n ++ [T0]). auto. }
    split.
    { apply heap_cons with (T := T0).
      - apply heap_ok_store_extends with (S := S); auto.
        exists (repeat T0 n ++ [T0]). auto.
      - apply has_type_store_extends with (S := S); auto.
        exists (repeat T0 n ++ [T0]). auto.
      - rewrite nth_error_app2.
        + replace (length (S ++ repeat T0 n)) with (length mu).
          2: { rewrite app_length, repeat_length. subst n. lia. }
          simpl. auto.
        + rewrite app_length, repeat_length. subst n. lia.
    }
    { apply T_Loc. apply nth_error_app_Some.
      rewrite nth_error_app2.
      - replace (length (S ++ repeat T0 n)) with (length mu).
        2: { rewrite app_length, repeat_length. subst n. lia. }
        simpl. auto.
      - rewrite app_length, repeat_length. subst n. lia.
    }
  - (* S_Deref *)
    apply IHHstep in H3; auto.
    destruct H3 as [S' [Hext [Hok' Ht']]].
    exists S'; split; [|split]; auto.
    eapply T_Deref; eauto.
  - (* S_DerefLoc *)
    apply T_Loc in H2. inversion H2; subst.
    exists S; split; [apply extends_refl|split; auto].
    eapply heap_ok_lookup; eauto.
  - (* S_Assign1 *)
    apply IHHstep in H5; auto.
    destruct H5 as [S' [Hext [Hok' Ht']]].
    exists S'; split; [|split]; auto.
    eapply T_Assign; eauto.
    eapply has_type_store_extends; eauto.
  - (* S_Assign2 *)
    apply IHHstep in H6; auto.
    destruct H6 as [S' [Hext [Hok' Ht']]].
    exists S'; split; [|split]; auto.
    apply T_Loc in H4. inversion H4; subst.
    eapply T_Assign; eauto.
    eapply has_type_store_extends; eauto.
  - (* S_AssignV *)
    exists S; split; [apply extends_refl|split; auto].
    + eapply heap_ok_update; eauto.
      apply T_Loc in H3. inversion H3; subst. auto.
    + apply T_Num.
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
