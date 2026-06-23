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

Fixpoint insert_at (k : nat) (H : ty) (G : ctx) : ctx :=
  match k, G with
  | 0, _ => H :: G
  | S k', T :: G' => T :: insert_at k' H G'
  | _, [] => [H]
  end.

Lemma nth_error_insert_at_lt : forall k H G x T,
  nth_error G x = Some T ->
  x < k ->
  nth_error (insert_at k H G) x = Some T.
Proof.
  induction k as [|k IH]; intros H G x T Heq Hlt; simpl in *.
  - lia.
  - destruct G as [|t G']; simpl in *.
    + destruct x; simpl in Heq; discriminate.
    + destruct x as [|x']; simpl in *.
      * simpl in Heq. injection Heq. intros ->. reflexivity.
      * apply IH; auto. lia.
Qed.

Lemma nth_error_insert_at_ge : forall k H G x T,
  nth_error G x = Some T ->
  x >= k ->
  nth_error (insert_at k H G) (S x) = Some T.
Proof.
  induction k as [|k IH]; intros H G x T Heq Hge; simpl in *.
  - destruct G as [|t G']; simpl in *.
    + destruct x; simpl in Heq; discriminate.
    + destruct x as [|x']; simpl in *.
      * assumption.
      * assumption.
  - destruct G as [|t G']; simpl in *.
    + destruct x; try lia; destruct x; simpl in Heq; discriminate.
    + destruct x as [|x']; simpl in *.
      * exfalso; lia.
      * apply IH; auto. lia.
Qed.

Lemma shift_at_typing : forall k G St t T H,
  has_type G St t T ->
  has_type (insert_at k H G) St (shift_at k t) T.
Proof.
  intros k G St t T H Ht.
  generalize dependent k.
  induction Ht; intros k; simpl.

  - (* T_Var *)
    simpl shift_at.
    destruct (x <? k) eqn:Hlt.
    + apply T_Var. apply nth_error_insert_at_lt with (x:=x); auto. apply Nat.ltb_lt. assumption.
    + assert (~ x < k). { apply (proj1 (Nat.ltb_nlt x k)). exact Hlt. }
      assert (x >= k) by lia.
      rewrite (Nat.add_comm x 1).
      apply T_Var. apply nth_error_insert_at_ge; auto.

  - (* T_Num *) apply T_Num.
  - (* T_Bool *) apply T_Bool.
  - (* T_Succ *) apply T_Succ. apply IHHt; auto.
  - (* T_Pred *) apply T_Pred. apply IHHt; auto.
  - (* T_IsZero *) apply T_IsZero. apply IHHt; auto.
  - (* T_If *)
    apply T_If with (T:=T); [apply IHHt1 with (k:=k) | apply IHHt2 with (k:=k) | apply IHHt3 with (k:=k)].

  - (* T_Lam *)
    apply T_Lam.
    apply IHHt with (k := Nat.succ k).

  - (* T_App *)
    apply T_App with (T1:=T1); [apply IHHt1 with (k:=k) | apply IHHt2 with (k:=k)].

  - (* T_Fix *)
    apply T_Fix.
    apply IHHt with (k := Nat.succ k).

  - (* T_Ref *) apply T_Ref. apply IHHt; auto.
  - (* T_Deref *) apply T_Deref. apply IHHt; auto.
  - (* T_Assign *) apply T_Assign with (T:=T); [apply IHHt1 with (k:=k) | apply IHHt2 with (k:=k)].

  - (* T_Loc *) apply T_Loc. assumption.
Qed.

Lemma shift_typing : forall G S t T H,
  has_type G S t T ->
  has_type (H :: G) S (shift t) T.
Proof.
  intros. unfold shift. rewrite <- (firstn_skipn 0 G) at 1. simpl.
  apply shift_at_typing with (k:=0). assumption.
Qed.

Lemma subst_preserves_typing : forall T1 G1 S t T,
  has_type (G1 ++ [T1]) S t T ->
  forall s, has_type G1 S s T1 ->
  has_type G1 S (subst (length G1) s t) T.
Proof.
  intros T1 G1 S t T Ht.
  remember (G1 ++ [T1]) as Gfull eqn:HG.
  revert G1 HG.
  induction Ht; intros G1' HG s Hs; simpl subst; simpl.

  - (* T_Var *)
    rename x into i.
    rewrite HG in H.
    set (n := length G1') in *.
    destruct (Nat.eqb i n) eqn:Heq'.
    + apply Nat.eqb_eq in Heq'. subst i.
      rewrite nth_error_app2 in H by lia.
      rewrite Nat.sub_diag in H. simpl in H.
      inversion H; subst. assumption.
    + apply Nat.eqb_neq in Heq'.
      apply T_Var.
      assert (i < n).
      { assert (Hlen : i < length (G1' ++ [T1])).
        { apply (proj1 (nth_error_Some (A:=ty) (G1' ++ [T1]) i)).
          rewrite H. discriminate. }
        rewrite length_app in Hlen. simpl in Hlen.
        unfold n in Hlen. lia. }
      rewrite nth_error_app1 in H by assumption.
      exact H.

  - (* T_Num *) apply T_Num.
  - (* T_Bool *) apply T_Bool.
  - (* T_Succ *)
    apply T_Succ. apply (IHHt G1' HG s Hs).

  - (* T_Pred *)
    apply T_Pred. apply (IHHt G1' HG s Hs).

  - (* T_IsZero *)
    apply T_IsZero. apply (IHHt G1' HG s Hs).

  - (* T_If *)
    apply T_If with (T:=T);
      [apply (IHHt1 G1' HG s Hs) |
       apply (IHHt2 G1' HG s Hs) |
       apply (IHHt3 G1' HG s Hs)].

  - (* T_Lam *)
    apply T_Lam.
    apply (IHHt (T0 :: G1')); [rewrite HG; reflexivity|].
    apply shift_typing. exact Hs.

  - (* T_App *)
    apply T_App with (T1:=T0);
      [apply (IHHt1 G1' HG s Hs) |
       apply (IHHt2 G1' HG s Hs)].

  - (* T_Fix *)
    apply T_Fix.
    apply (IHHt (T :: G1')); [rewrite HG; reflexivity|].
    apply shift_typing. exact Hs.

  - (* T_Ref *)
    apply T_Ref. apply (IHHt G1' HG s Hs).

  - (* T_Deref *)
    apply T_Deref. apply (IHHt G1' HG s Hs).

  - (* T_Assign *)
    apply T_Assign with (T:=T);
      [apply (IHHt1 G1' HG s Hs) |
       apply (IHHt2 G1' HG s Hs)].

  - (* T_Loc *)
    apply T_Loc. assumption.
Qed.

Lemma weakening_store : forall G S t T S',
  has_type G S t T ->
  extends S' S ->
  has_type G S' t T.
Proof.
  intros G S t T S' Ht Hext.
  destruct Hext as [S2 H].
  subst S'.
  induction Ht.

  - (* T_Var *) apply T_Var. assumption.
  - (* T_Num *) apply T_Num.
  - (* T_Bool *) apply T_Bool.
  - (* T_Succ *) apply T_Succ. apply IHHt.
  - (* T_Pred *) apply T_Pred. apply IHHt.
  - (* T_IsZero *) apply T_IsZero. apply IHHt.
  - (* T_If *) apply T_If with (T:=T); [apply IHHt1 | apply IHHt2 | apply IHHt3].
  - (* T_Lam *) apply T_Lam. apply IHHt.
  - (* T_App *) apply T_App with (T1:=T1); [apply IHHt1 | apply IHHt2].
  - (* T_Fix *) apply T_Fix. apply IHHt.
  - (* T_Ref *) apply T_Ref. apply IHHt.
  - (* T_Deref *) apply T_Deref. apply IHHt.
  - (* T_Assign *) apply T_Assign with (T:=T); [apply IHHt1 | apply IHHt2].
  - (* T_Loc *)
    apply T_Loc.
    assert (l < length S).
    { apply (proj1 (nth_error_Some (A:=ty) S l)). rewrite H. discriminate. }
    rewrite nth_error_app1; assumption.
Qed.

Lemma heap_ok_extends : forall mu S S',
  heap_ok mu S ->
  extends S' S ->
  heap_ok mu S'.
Proof.
  intros mu S S' Hh Hext.
  induction Hh.
  - apply heap_empty.
  - apply heap_cons with (T:=T).
    + apply IHHh. assumption.
    + apply weakening_store with (S:=S); assumption.
    + destruct Hext as [S2 Heq]. subst S'.
      assert (l < length S) by (apply (proj1 (nth_error_Some (A:=ty) S l)); rewrite H0; discriminate).
      rewrite nth_error_app1; assumption.
Qed.

Lemma heap_ok_lookup : forall mu l v S,
  heap_ok mu S ->
  heap_lookup l mu = Some v ->
  exists T, nth_error S l = Some T /\ has_type [] S v T.
Proof.
  intros mu l v S Hh Hlook.
  induction Hh.
  - simpl in Hlook. discriminate.
  - simpl in Hlook.
    destruct (Nat.eqb l l0) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst l0.
      inversion Hlook. subst v0.
      exists T. auto.
    + apply IHHh. assumption.
Qed.

Lemma heap_ok_update : forall mu l v S T,
  heap_ok mu S ->
  has_type [] S v T ->
  nth_error S l = Some T ->
  heap_ok (heap_update l v mu) S.
Proof.
  intros mu l v S T Hh Htv Hnl.
  induction Hh as [|l0 v0 mu' S' T0 Hh' IH Htv0 Hnl0].
  - simpl. apply heap_empty.
  - simpl.
    destruct (Nat.eqb l l0) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst l0.
      rewrite Hnl0 in Hnl. inversion Hnl. subst T0.
      apply heap_cons with (T:=T); auto.
    + apply heap_cons with (T:=T0); auto.
Qed.

Lemma has_type_deref_loc_inv : forall S l T,
  has_type [] S (Deref (Loc l)) T ->
  nth_error S l = Some T.
Proof.
  intros. inversion H. subst.
  match goal with H1 : has_type [] S (Loc l) _ |- _ => inversion H1; subst; assumption end.
Qed.

Theorem preservation :
  forall t mu t' mu' T S,
    has_type [] S t T ->
    step t mu t' mu' ->
    heap_ok mu S ->
    length mu = length S ->
    exists S',
      extends S' S /\
      heap_ok mu' S' /\
      has_type [] S' t' T.
Proof.
  intros t mu t' mu' T S Ht Hstep Hh Hlen.
  induction Hstep in T, S, Ht, Hh, Hlen |- *; simpl.

  - (* S_Succ *)
    inversion Ht; subst; clear Ht.
    destruct (IHHstep TyNat S H2 Hh Hlen) as [S' [Hext [Hh' Ht']]].
    exists S'. split; auto. split; auto. apply T_Succ. assumption.

  - (* S_PredZero *)
    inversion Ht; subst; clear Ht.
    inversion H2; subst.
    exists S. split; [exists []; rewrite app_nil_r; reflexivity | split; [auto | apply T_Num]].

  - (* S_PredSucc *)
    inversion Ht; subst; clear Ht.
    inversion H2; subst.
    exists S. split; [exists []; rewrite app_nil_r; reflexivity | split; [auto | apply T_Num]].

  - (* S_Pred *)
    inversion Ht; subst; clear Ht.
    destruct (IHHstep TyNat S H2 Hh Hlen) as [S' [Hext [Hh' Ht']]].
    exists S'. split; auto. split; auto. apply T_Pred. assumption.

  - (* S_IsZeroZero *)
    inversion Ht; subst; clear Ht.
    inversion H2; subst.
    exists S. split; [exists []; rewrite app_nil_r; reflexivity | split; [auto | apply T_Bool]].

  - (* S_IsZeroSucc *)
    inversion Ht; subst; clear Ht.
    inversion H2; subst.
    exists S. split; [exists []; rewrite app_nil_r; reflexivity | split; [auto | apply T_Bool]].

  - (* S_IsZero *)
    inversion Ht; subst; clear Ht.
    destruct (IHHstep TyNat S H2 Hh Hlen) as [S' [Hext [Hh' Ht']]].
    exists S'. split; auto. split; auto. apply T_IsZero. assumption.

  - (* S_IfTrue *)
    inversion Ht; subst; clear Ht.
    inversion H4; subst.
    exists S. split; [exists []; rewrite app_nil_r; reflexivity | split; [auto | auto]].

  - (* S_IfFalse *)
    inversion Ht; subst; clear Ht.
    inversion H4; subst.
    exists S. split; [exists []; rewrite app_nil_r; reflexivity | split; [auto | auto]].

  - (* S_If *)
    inversion Ht; subst; clear Ht.
    destruct (IHHstep TyBool S H4 Hh Hlen) as [S' [Hext [Hh' Ht']]].
    exists S'. split; auto. split; auto.
    eapply T_If; eauto.
    apply weakening_store with (S:=S); eauto.
    apply weakening_store with (S:=S); eauto.

  - (* S_App1 *)
    inversion Ht; subst; clear Ht.
    match goal with H : has_type [] S t1 ?T1type |- _ =>
      destruct (IHHstep T1type S H Hh Hlen) as [S' [Hext [Hh' Ht']]]
    end.
    exists S'. split; auto. split; auto.
    eapply T_App; eauto.
    apply weakening_store with (S:=S); eauto.

  - (* S_App2 *)
    inversion Ht; subst; clear Ht.
    match goal with H : has_type [] S t2 ?Ta |- _ =>
      destruct (IHHstep Ta S H Hh Hlen) as [S' [Hext [Hh' Ht']]]
    end.
    exists S'. split; auto. split; auto.
    eapply T_App; eauto.
    apply weakening_store with (S:=S); eauto.

  - (* S_AppAbs *)
    inversion Ht; subst; clear Ht.
    match goal with H : has_type [] S (Lam _ _) _ |- _ =>
      inversion H; subst; clear H
    end.
    match goal with H : has_type [] S v2 ?Targ |- _ =>
      exists S; split; [exists []; rewrite app_nil_r; reflexivity | split; auto];
      apply subst_preserves_typing with (G1:=[])(s:=v2)(T1:=Targ); auto
    end.

  - (* S_Fix *)
    inversion Ht; subst; clear Ht.
    exists S. split; [exists []; rewrite app_nil_r; reflexivity | split; auto].
    apply subst_preserves_typing with (G1:=[])(s:=Fix t)(T1:=T); auto.
    match goal with H : has_type (?Tfix :: []) S t ?Tfix |- _ => apply T_Fix in H; assumption end.

  - (* S_Ref *)
    inversion Ht; subst; clear Ht.
    match goal with H : has_type [] S t ?T0 |- _ =>
      destruct (IHHstep T0 S H Hh Hlen) as [S' [Hext [Hh' Ht']]]
    end.
    exists S'. split; auto. split; auto. apply T_Ref. assumption.

  - (* S_RefV *)
    inversion Ht; subst; clear Ht.
    exists (S ++ [T0]).
    split.
    + exists [T0]. reflexivity.
    + split.
      * apply heap_cons with (T:=T0).
        { apply heap_ok_extends with (S:=S); auto. exists [T0]; reflexivity. }
        { apply weakening_store with (S:=S); auto. exists [T0]; reflexivity. }
        { rewrite nth_error_app2 by lia.
          rewrite Hlen. rewrite Nat.sub_diag. simpl. reflexivity. }
      * apply T_Loc.
        rewrite nth_error_app2 by lia.
        rewrite Hlen. rewrite Nat.sub_diag. simpl. reflexivity.

  - (* S_Deref *)
    inversion Ht; subst; clear Ht.
    match goal with H : has_type [] S t ?T0 |- _ =>
      destruct (IHHstep T0 S H Hh Hlen) as [S' [Hext [Hh' Ht']]]
    end.
    exists S'. split; auto. split; auto. apply T_Deref. assumption.

  - (* S_DerefLoc *)
    apply has_type_deref_loc_inv in Ht.
    apply (heap_ok_lookup mu l v S Hh) in H; auto.
    destruct H as [T' [Hnl Htv]].
    rewrite Ht in Hnl.
    assert (T = T') by congruence. subst T'.
    exists S. split; [exists []; rewrite app_nil_r; reflexivity | split; auto].

  - (* S_Assign1 *)
    inversion Ht; subst; clear Ht.
    match goal with H : has_type [] S t1 ?T1type |- _ =>
      destruct (IHHstep T1type S H Hh Hlen) as [S' [Hext [Hh' Ht']]]
    end.
    exists S'. split; auto. split; auto.
    eapply T_Assign; eauto.
    apply weakening_store with (S:=S); eauto.

  - (* S_Assign2 *)
    inversion Ht; subst; clear Ht.
    match goal with H : has_type [] S t2 ?Ta |- _ =>
      destruct (IHHstep Ta S H Hh Hlen) as [S' [Hext [Hh' Ht']]]
    end.
    exists S'. split; auto. split; auto.
    eapply T_Assign; eauto.
    apply weakening_store with (S:=S); eauto.

  - (* S_AssignV *)
    inversion Ht; subst; clear Ht.
    match goal with H : has_type [] S (Loc l) _ |- _ => inversion H; subst; clear H end.
    exists S. split; [exists []; rewrite app_nil_r; reflexivity | split; [eapply heap_ok_update; eauto | apply T_Num]].
Qed.

Theorem preservation_neg : ~ (
  forall t mu t' mu' T S,
    has_type [] S t T ->
    step t mu t' mu' ->
    heap_ok mu S ->
    length mu = length S ->
    exists S',
      extends S' S /\
      heap_ok mu' S' /\
      has_type [] S' t' T).
Proof.
Admitted.
