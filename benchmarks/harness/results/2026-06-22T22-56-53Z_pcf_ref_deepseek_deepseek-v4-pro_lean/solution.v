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

Lemma nth_error_Some_len : forall A (l : list A) n x,
  nth_error l n = Some x -> n < length l.
Proof.
  intros A l n x H.
  apply (proj1 (nth_error_Some l n)).
  rewrite H. discriminate.
Qed.

Lemma extends_nth_error : forall S' S n T,
  extends S' S ->
  nth_error S n = Some T ->
  nth_error S' n = Some T.
Proof.
  intros S' S n T [S2 ->] Hnth.
  apply nth_error_Some_len in Hnth as Hlt.
  rewrite nth_error_app1; auto.
Qed.

Lemma weakening_has_type : forall G S t T S2,
  has_type G S t T ->
  extends S2 S ->
  has_type G S2 t T.
Proof.
  intros G S t T S2 Ht Hext.
  induction Ht.
  - apply T_Var. assumption.
  - apply T_Num.
  - apply T_Bool.
  - apply T_Succ. apply IHHt. assumption.
  - apply T_Pred. apply IHHt. assumption.
  - apply T_IsZero. apply IHHt. assumption.
  - eapply T_If; eauto.
  - apply T_Lam. apply IHHt. assumption.
  - eapply T_App; eauto.
  - apply T_Fix. apply IHHt. assumption.
  - apply T_Ref. apply IHHt. assumption.
  - apply T_Deref. apply IHHt. assumption.
  - eapply T_Assign; eauto.
  - eapply T_Loc. eapply extends_nth_error; eauto.
Qed.

Lemma weakening_heap_ok : forall mu S S2,
  heap_ok mu S ->
  extends S2 S ->
  heap_ok mu S2.
Proof.
  intros mu S S2 Hok Hext.
  induction Hok.
  - constructor.
  - econstructor; eauto.
    + eapply weakening_has_type; eauto.
    + eapply extends_nth_error; eauto.
Qed.

Lemma heap_lookup_ok : forall mu S l v,
  heap_ok mu S ->
  heap_lookup l mu = Some v ->
  exists T, nth_error S l = Some T /\ has_type [] S v T.
Proof.
  intros mu S l v Hok Hlook.
  revert l v Hlook.
  induction Hok; intros l' v' Hlook.
  simpl in Hlook. discriminate.
  simpl in Hlook.
  remember (l' =? l) as b eqn:Heq.
  destruct b.
  symmetry in Heq. apply Nat.eqb_eq in Heq. subst l'.
  simpl in Hlook. inversion Hlook; subst.
  exists T. split; auto.
  apply IHHok in Hlook as [T' [Hn Ht]].
  exists T'. split; auto.
Qed.

Lemma heap_update_ok : forall mu S l v T,
  heap_ok mu S ->
  nth_error S l = Some T ->
  has_type [] S v T ->
  heap_ok (heap_update l v mu) S.
Proof.
  intros mu S l v T Hok Hnth Hty.
  revert v l Hnth Hty.
  induction Hok; intros v_target l_target Hnth Hty.
  constructor.
  unfold heap_update. simpl.
  case_eq (l_target =? l); intros Heq.
  apply Nat.eqb_eq in Heq. subst l.
  simpl. econstructor; eauto.
  simpl. econstructor; eauto.
Qed.

Lemma firstn_nth_error : forall A (l : list A) d n,
  n < d -> nth_error (firstn d l) n = nth_error l n.
Proof.
  intros A l d n Hlt.
  revert d n Hlt.
  induction l; intros d n Hlt; simpl.
  - rewrite firstn_nil. rewrite nth_error_nil. reflexivity.
  - destruct d; [lia|].
    destruct n; simpl; auto.
    apply IHl. lia.
Qed.

Lemma nth_error_skipn : forall A (l : list A) d n,
  nth_error (skipn d l) n = nth_error l (d + n).
Proof.
  intros A l d n. revert l.
  induction d; intros l; simpl.
  - auto.
  - destruct l; simpl.
    + induction n; simpl; reflexivity.
    + simpl in *. apply IHd.
Qed.

Lemma nth_error_insert : forall A (l : list A) d a n x,
  nth_error l n = Some x ->
  nth_error (firstn d l ++ [a] ++ skipn d l) (if n <? d then n else Datatypes.S n) = Some x.
Proof.
  intros A l d a n x Hnth.
  destruct (n <? d) eqn:Hlt.
  - apply Nat.ltb_lt in Hlt.
    rewrite nth_error_app1.
    + apply firstn_nth_error with (A:=A). exact Hlt. exact Hnth.
    + rewrite length_firstn. apply Nat.min_glb_lt_iff.
      split; [exact Hlt | eapply nth_error_Some_len; eauto].
  - apply Nat.ltb_nlt in Hlt.
    assert (d <= length l) as Hdlen.
    { eapply nth_error_Some_len in Hnth. lia. }
    assert (length (firstn d l) = d) as Hlenfirstn.
    { apply firstn_length_le. exact Hdlen. }
    rewrite nth_error_app2 by (rewrite Hlenfirstn; lia).
    rewrite Hlenfirstn.
    replace (Datatypes.S n - d) with (Datatypes.S (n - d)) by lia.
    simpl. (* simpl reduces nth_error (a :: skipn d l) (S (n-d)) *)
    rewrite nth_error_skipn.
    replace (d + (n - d)) with n by lia.
    exact Hnth.
Qed.

Lemma weakening_G_at : forall d G A S t T,
  has_type G S t T ->
  has_type (firstn d G ++ [A] ++ skipn d G) S (shift_at d t) T.
Proof.
  intros d G A S t T Ht.
  generalize dependent G.
  generalize dependent d.
  generalize dependent A.
  intros A d G Ht.
  revert A d.
  induction Ht; intros A d; simpl.
  - rename H into Hnth.
    apply T_Var.
    apply nth_error_insert with (A:=ty) (d:=d) (a:=A) (x:=T); auto.
  - apply T_Num.
  - apply T_Bool.
  - apply T_Succ. apply IHHt; auto.
  - apply T_Pred. apply IHHt; auto.
  - apply T_IsZero. apply IHHt; auto.
  - eapply T_If; [apply IHHt1 | apply IHHt2 | apply IHHt3]; eauto.
  - apply T_Lam. apply IHHt with (d := S d); auto.
  - eapply T_App; [apply IHHt1 | apply IHHt2]; eauto.
  - apply T_Fix. apply IHHt with (d := S d); auto.
  - apply T_Ref. apply IHHt; auto.
  - apply T_Deref. apply IHHt; auto.
  - eapply T_Assign; [apply IHHt1 | apply IHHt2]; eauto.
  - eapply T_Loc. eapply extends_nth_error; eauto.
    exists []; auto.
Qed.

Lemma weakening_G_front : forall G A S t T,
  has_type G S t T ->
  has_type (A :: G) S (shift t) T.
Proof.
  intros. apply weakening_G_at with (d:=0); auto.
Qed.

Fixpoint nshift (n : nat) (s : tm) : tm :=
  match n with
  | 0 => s
  | S n' => shift (nshift n' s)
  end.

Lemma nshift_typing : forall pre S s U,
  has_type [] S s U ->
  has_type pre S (nshift (length pre) s) U.
Proof.
  induction pre; simpl; intros; auto.
  apply weakening_G_front.
  apply IHpre. auto.
Qed.

Lemma weakening_G_end : forall G A S t T,
  has_type G S t T ->
  has_type (G ++ [A]) S t T.
Proof.
  induction 1; simpl.
  - apply T_Var. apply nth_error_app1. eapply nth_error_Some_len; eauto.
  - apply T_Num.
  - apply T_Bool.
  - apply T_Succ. apply IHhas_type.
  - apply T_Pred. apply IHhas_type.
  - apply T_IsZero. apply IHhas_type.
  - eapply T_If; eauto.
  - apply T_Lam. apply IHhas_type.
  - eapply T_App; eauto.
  - apply T_Fix. apply IHhas_type.
  - apply T_Ref. apply IHhas_type.
  - apply T_Deref. apply IHhas_type.
  - eapply T_Assign; eauto.
  - eapply T_Loc. apply nth_error_app1. eapply nth_error_Some_len; eauto.
Qed.

Lemma subst_deep : forall (pre : list ty) U S t T s,
  has_type (pre ++ [U]) S t T ->
  has_type [] S s U ->
  has_type pre S (subst (length pre) (nshift (length pre) s) t) T.
Proof.
  intros pre U S t T s Ht Hs.
  revert pre U s Hs.
  induction Ht; intros pre U' s Hs; simpl.
  - rename H into Hnth.
    destruct (x =? length pre) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst x.
      (* nth_error (pre ++ [U']) (length pre) = Some T *)
      rewrite nth_error_app2 in Hnth; [|rewrite app_length; simpl; lia].
      simpl in Hnth. replace (length pre - length pre) with 0 in Hnth by lia.
      simpl in Hnth. inversion Hnth; subst T.
      clear Hnth.
      apply nshift_typing; auto.
    + apply T_Var.
      apply Nat.eqb_neq in Heq.
      apply nth_error_Some_len in Hnth.
      assert (x < length pre) as Hlt by (rewrite app_length in Hnth; simpl in Hnth; lia).
      apply nth_error_app1 in Hnth; auto.
  - apply T_Num.
  - apply T_Bool.
  - apply T_Succ. apply IHHt; auto.
  - apply T_Pred. apply IHHt; auto.
  - apply T_IsZero. apply IHHt; auto.
  - eapply T_If; [apply IHHt1 | apply IHHt2 | apply IHHt3]; auto.
  - apply T_Lam.
    apply IHHt with (pre := T1 :: pre).
    simpl. auto.
  - eapply T_App; [apply IHHt1 | apply IHHt2]; auto.
  - apply T_Fix.
    apply IHHt with (pre := T :: pre).
    simpl. auto.
  - apply T_Ref. apply IHHt; auto.
  - apply T_Deref. apply IHHt; auto.
  - eapply T_Assign; [apply IHHt1 | apply IHHt2]; auto.
  - eapply T_Loc. eapply extends_nth_error.
    + exists []. auto.
    + eauto.
Qed.

Lemma subst_empty : forall U S t T s,
  has_type [U] S t T ->
  has_type [] S s U ->
  has_type [] S (subst 0 s t) T.
Proof.
  intros. eapply subst_deep with (pre := []); eauto.
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
  generalize dependent T.
  generalize dependent S.
  induction Hstep; intros S T Ht Hok Hlen.
  - inversion Ht; subst.
    destruct (IHHstep S TyNat H2 Hok Hlen) as [S' [Hext [Hok' Ht']]].
    exists S'. split; auto. split; auto.
    apply T_Succ. exact Ht'.
  - inversion Ht; subst. inversion H2; subst.
    exists S. split; [exists []; auto | split; auto]. apply T_Num.
  - inversion Ht; subst. inversion H2; subst.
    exists S. split; [exists []; auto | split; auto]. apply T_Num.
  - inversion Ht; subst.
    destruct (IHHstep S TyNat H2 Hok Hlen) as [S' [Hext [Hok' Ht']]].
    exists S'. split; auto. split; auto.
    apply T_Pred. exact Ht'.
  - inversion Ht; subst. inversion H2; subst.
    exists S. split; [exists []; auto | split; auto]. apply T_Bool.
  - inversion Ht; subst. inversion H2; subst.
    exists S. split; [exists []; auto | split; auto]. apply T_Bool.
  - inversion Ht; subst.
    destruct (IHHstep S TyNat H2 Hok Hlen) as [S' [Hext [Hok' Ht']]].
    exists S'. split; auto. split; auto.
    apply T_IsZero. exact Ht'.
  - inversion Ht; subst. inversion H2; subst.
    exists S. split; [exists []; auto | split; auto].
  - inversion Ht; subst. inversion H2; subst.
    exists S. split; [exists []; auto | split; auto].
  - inversion Ht; subst.
    destruct (IHHstep S TyBool H2 Hok Hlen) as [S' [Hext [Hok' Ht']]].
    exists S'. split; auto. split; auto.
    eapply T_If; eauto.
    eapply weakening_has_type; eauto.
    eapply weakening_has_type; eauto.
  - inversion Ht; subst.
    destruct (IHHstep S (TyArrow T1 T2) H2 Hok Hlen) as [S' [Hext [Hok' Ht']]].
    exists S'. split; auto. split; auto.
    eapply T_App; eauto.
    eapply weakening_has_type; eauto.
  - inversion Ht; subst.
    destruct (IHHstep S T1 H5 Hok Hlen) as [S' [Hext [Hok' Ht']]].
    exists S'. split; auto. split; auto.
    eapply T_App; eauto.
    eapply weakening_has_type; eauto.
  - inversion Ht; subst. inversion H3; subst.
    exists S. split; [exists []; auto | split; auto].
    apply subst_empty with (U:=T1); auto.
  - inversion Ht; subst.
    assert (Hfix : has_type [] S (Fix t) T) by (apply T_Fix; exact H2).
    apply (subst_deep [] T S t T (Fix t) H2 Hfix).
    exists S. split; [exists []; auto | split; auto].
  - inversion Ht; subst.
    destruct (IHHstep S T0 H2 Hok Hlen) as [S' [Hext [Hok' Ht']]].
    exists S'. split; auto. split; auto.
    apply T_Ref. exact Ht'.
  - inversion Ht; subst.
    set (k := length mu - length S).
    set (S' := S ++ repeat TyNat k ++ [T]).
    assert (Hext : extends S' S) by (exists (repeat TyNat k ++ [T]); auto).
    assert (Hnth : nth_error S' (length mu) = Some T).
    { subst S' k.
      rewrite nth_error_app2.
      - rewrite app_length. rewrite repeat_length.
        replace (length mu - length S - (length mu - length S)) with 0 by lia.
        simpl. auto.
      - rewrite app_length. rewrite repeat_length. lia.
    }
    assert (Hmu' : heap_ok ((length mu, v) :: mu) S').
    { apply heap_cons with (T:=T); auto.
      - eapply weakening_heap_ok; eauto.
      - eapply weakening_has_type; eauto.
    }
    assert (Htloc : has_type [] S' (Loc (length mu)) (TyRef T)).
    { apply T_Loc. exact Hnth. }
    exists S'. split; auto. split; auto.
  - inversion Ht; subst.
    destruct (IHHstep S (TyRef T) H2 Hok Hlen) as [S' [Hext [Hok' Ht']]].
    exists S'. split; auto. split; auto.
    apply T_Deref. exact Ht'.
  - inversion Ht; subst.
    rename H3 into HnthS.
    apply heap_lookup_ok with (l:=l) (v:=v) in Hok as [T' [HnthS' Hvty]]; auto.
    rewrite HnthS in HnthS'. inversion HnthS'; subst T'.
    exists S. split; [exists []; auto | split; auto].
  - inversion Ht; subst.
    destruct (IHHstep S (TyRef T) H2 Hok Hlen) as [S' [Hext [Hok' Ht']]].
    exists S'. split; auto. split; auto.
    eapply T_Assign; eauto.
    eapply weakening_has_type; eauto.
  - inversion Ht; subst.
    destruct (IHHstep S T0 H6 Hok Hlen) as [S' [Hext [Hok' Ht']]].
    exists S'. split; auto. split; auto.
    eapply T_Assign; eauto.
    eapply weakening_has_type; eauto.
  - inversion Ht; subst. inversion H3; subst.
    rename H4 into Hloc, H5 into Hval.
    rename H7 into HnthS.
    assert (Hok' : heap_ok (heap_update l v mu) S).
    { apply heap_update_ok with (T:=T); auto. }
    assert (Ht' : has_type [] S (Num 0) TyNat) by apply T_Num.
    exists S. split; [exists []; auto | split; auto].
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
