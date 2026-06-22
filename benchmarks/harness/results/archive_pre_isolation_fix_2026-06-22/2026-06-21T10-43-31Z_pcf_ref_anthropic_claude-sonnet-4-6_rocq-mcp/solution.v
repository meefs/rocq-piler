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

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)



(** ** Auxiliary lemmas *)

(** Store extension is reflexive *)
Lemma extends_refl : forall S, extends S S.
Proof.
  intros S. exists []. rewrite app_nil_r. reflexivity.
Qed.

(** Store extension preserves nth_error *)
Lemma extends_nth_error : forall S S' l T,
  extends S' S -> nth_error S l = Some T -> nth_error S' l = Some T.
Proof.
  intros S S' l T [S2 ->] H.
  rewrite nth_error_app1; auto.
  eapply nth_error_Some. rewrite H. discriminate.
Qed.

(** Typing is preserved under store extension *)
Lemma has_type_store_ext : forall G S S' t T,
  extends S' S ->
  has_type G S t T ->
  has_type G S' t T.
Proof.
  intros G S S' t T Hext Hty.
  induction Hty; try econstructor; eauto using extends_nth_error.
Qed.

(** heap_ok is preserved under store extension *)
Lemma heap_ok_store_ext : forall mu S S',
  extends S' S ->
  heap_ok mu S ->
  heap_ok mu S'.
Proof.
  intros mu S S' Hext Hok.
  induction Hok.
  - constructor.
  - econstructor; eauto using has_type_store_ext, extends_nth_error.
Qed.

(** Weakening: typing is monotone in the context *)
Lemma weakening : forall G S t T,
  has_type G S t T ->
  forall G',
  (forall x U, nth_error G x = Some U -> nth_error G' x = Some U) ->
  has_type G' S t T.
Proof.
  intros G S t T Hty.
  induction Hty; intros G' Hwk; try econstructor; eauto.
  - apply IHHty. intros [|x] U Hu; simpl in *; auto.
  - apply IHHty. intros [|x] U Hu; simpl in *; auto.
Qed.

(** Shift-at: shifting variables in a typing context *)
Lemma shift_at_typing : forall d G S t T T0,
  has_type G S t T ->
  has_type (firstn d G ++ T0 :: skipn d G) S (shift_at d t) T.
Proof.
  intros d G S t T T0 Hty.
  generalize dependent d.
  induction Hty; intros d; simpl; try econstructor; eauto.
  - (* Var *)
    destruct (x <? d) eqn:E.
    + apply Nat.ltb_lt in E. constructor.
      rewrite nth_error_app1.
      * rewrite nth_error_firstn. rewrite <- Nat.ltb_lt in E. rewrite E. auto.
      * rewrite length_firstn.
        assert (Hxlen: x < length G) by (apply nth_error_Some; rewrite H; discriminate).
        apply Nat.min_glb; lia.
    + apply Nat.ltb_nlt in E.
      assert (Hxlen: x < length G) by (apply nth_error_Some; rewrite H; discriminate).
      assert (Hlen: d <= length G) by lia.
      constructor.
      rewrite nth_error_app2 by (rewrite length_firstn; lia).
      rewrite length_firstn, Nat.min_l by lia.
      destruct (x + 1 - d) eqn:Hd. lia.
      simpl. rewrite nth_error_skipn. replace (d + n) with x by lia. auto.
  - specialize (IHHty (Datatypes.S d)). simpl in IHHty. exact IHHty.
  - specialize (IHHty (Datatypes.S d)). simpl in IHHty. exact IHHty.
Qed.

(** Shift at 0 inserts a type at position 0 *)
Lemma shift_typing : forall G S t T T0,
  has_type G S t T ->
  has_type (T0 :: G) S (shift_at 0 t) T.
Proof.
  intros G S t T T0 Hty.
  apply (shift_at_typing 0 G S t T T0 Hty).
Qed.



(** Substitution preserves typing when j = length G (the "append" case) *)
Lemma substitution_preserves_typing : forall t G S s Ts T,
  has_type G S s Ts ->
  has_type (G ++ [Ts]) S t T ->
  has_type G S (subst (length G) s t) T.
Proof.
  intro t.
  induction t; intros G S s Ts T Hs Ht; simpl; inversion Ht; subst.
  all: try solve [
    (destruct (Nat.eqb n (length G)) eqn:E;
     [apply Nat.eqb_eq in E; subst;
      rewrite nth_error_app2 in H2 by lia; replace (length G - length G) with 0 in H2 by lia;
      simpl in H2; inversion H2; subst; exact Hs
     | apply Nat.eqb_neq in E; constructor;
       destruct (Nat.lt_total n (length G)) as [Hlt | [Heq | Hgt]];
       [rewrite nth_error_app1 in H2 by lia; exact H2
       | exfalso; auto
       | rewrite nth_error_app2 in H2 by lia;
         destruct (n - length G) eqn:Hd; [lia |];
         simpl in H2; destruct n0; simpl in H2; discriminate]])
  | constructor
  | econstructor; eauto
  | (apply T_Lam; apply (IHt (t :: G) S (shift s) Ts T2);
     [apply shift_typing; exact Hs | simpl; exact H4])
  | (apply T_Fix; apply (IHt (T :: G) S (shift s) Ts T);
     [apply shift_typing; exact Hs | simpl; exact H3])
  ].
  apply T_Fix. apply (IHt (T :: G) S (shift s) Ts T).
  - apply shift_typing. exact Hs.
  - simpl. exact H2.
Qed.

(** Special case: substitution at position 0 *)
Lemma subst0_preserves_typing : forall S s Ts t T,
  has_type [] S s Ts ->
  has_type [Ts] S t T ->
  has_type [] S (subst 0 s t) T.
Proof.
  intros S s Ts t T Hs Ht.
  apply (substitution_preserves_typing t [] S s Ts T Hs).
  simpl. exact Ht.
Qed.



(** Lookup in a well-typed heap gives a well-typed value *)
Lemma heap_lookup_typing : forall mu S l v T,
  heap_ok mu S ->
  heap_lookup l mu = Some v ->
  nth_error S l = Some T ->
  has_type [] S v T.
Proof.
  intros mu S l v T Hok Hlook Hnth.
  induction Hok.
  - simpl in Hlook. discriminate.
  - simpl in Hlook.
    destruct (Nat.eqb l l0) eqn:E.
    + apply Nat.eqb_eq in E. subst.
      inversion Hlook. subst.
      rewrite H0 in Hnth. inversion Hnth. subst. exact H.
    + apply IHHok; auto.
Qed.

(** Update of a well-typed heap preserves heap_ok *)
Lemma heap_update_ok : forall mu S l v T,
  heap_ok mu S ->
  has_type [] S v T ->
  nth_error S l = Some T ->
  heap_ok (heap_update l v mu) S.
Proof.
  intros mu S l v T Hok Hv Hnth.
  induction Hok; simpl.
  - constructor.
  - destruct (Nat.eqb l l0) eqn:E.
    + apply Nat.eqb_eq in E. subst.
      rewrite H0 in Hnth. inversion Hnth. subst.
      econstructor; eauto.
    + econstructor; eauto.
Qed.

(** extends S' S means S is a prefix of S' *)
Lemma extends_trans : forall S1 S2 S3,
  extends S2 S1 -> extends S3 S2 -> extends S3 S1.
Proof.
  intros S1 S2 S3 [S12 ->] [S23 ->].
  exists (S12 ++ S23). rewrite app_assoc. reflexivity.
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
  intros t mu t' mu' Ty S Hty Hstep Hok Hlen.
  generalize dependent Ty.
  induction Hstep; intros Ty Hty; inversion Hty; subst.
  all: try match goal with
    | IHHstep : heap_ok _ _ -> _ -> forall _, has_type _ _ ?t _ -> _,
      Hs : has_type _ _ ?t _ |- _ =>
      destruct (IHHstep Hok Hlen _ Hs) as [S' [Hext [Hok' Hty']]];
      exists S'; repeat split; auto;
      try (econstructor; eauto using has_type_store_ext)
    end.
  all: try (exists S; split; [apply extends_refl | split; [exact Hok | constructor; auto]]).
  - exists S. split; [apply extends_refl | split; [exact Hok | exact H6]].
  - exists S. split; [apply extends_refl | split; [exact Hok | exact H7]].
  - (* S_AppAbs *)
    exists S. split; [apply extends_refl | split; [exact Hok |]].
    inversion H4. subst.
    apply (subst0_preserves_typing S v2 T1 t1 Ty H6 H3).
  - (* S_Fix *)
    exists S. split; [apply extends_refl | split; [exact Hok |]].
    apply (subst0_preserves_typing S (Fix t) Ty t Ty).
    + apply T_Fix. exact H2.
    + exact H2.
  - (* S_RefV *)
    pose (S' := S ++ repeat TyNat (length mu - length S) ++ [T]).
    exists S'.
    assert (Hext: extends S' S). {
      exists (repeat TyNat (length mu - length S) ++ [T]). reflexivity.
    }
    assert (Hloc: nth_error S' (length mu) = Some T). {
      unfold S'.
      rewrite (app_assoc S (repeat TyNat (length mu - length S)) [T]).
      rewrite nth_error_app2 by (rewrite length_app, repeat_length; lia).
      rewrite length_app, repeat_length.
      replace (length mu - (length S + (length mu - length S))) with 0 by lia.
      simpl. reflexivity.
    }
    split. exact Hext. split.
    + econstructor.
      * apply (heap_ok_store_ext mu S S' Hext Hok).
      * apply (has_type_store_ext [] S S' v T Hext H3).
      * exact Hloc.
    + apply T_Loc. exact Hloc.
  - (* S_DerefLoc *)
    exists S. split; [apply extends_refl | split; [exact Hok |]].
    inversion H3. subst.
    apply (heap_lookup_typing mu S l v Ty Hok H H5).
  - (* S_AssignV *)
    exists S. split; [apply extends_refl | split; [| constructor]].
    inversion H4. subst.
    apply (heap_update_ok mu S l v T Hok H6 H5).
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
