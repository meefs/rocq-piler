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

(** * Helper lemmas *)

Lemma nth_error_app_l : forall {A : Type} (l1 l2 : list A) n x,
  nth_error l1 n = Some x -> nth_error (l1 ++ l2) n = Some x.
Proof.
  intros A l1 l2 n x H.
  rewrite nth_error_app1.
  - exact H.
  - apply nth_error_Some. intros H0. rewrite H0 in H. discriminate.
Qed.

Lemma nth_error_app_r : forall {A : Type} (l1 l2 : list A) n x,
  nth_error l2 n = Some x ->
  nth_error (l1 ++ l2) (length l1 + n) = Some x.
Proof.
  intros A l1 l2 n x H.
  rewrite nth_error_app2.
  - replace (length l1 + n - length l1) with n by lia.
    exact H.
  - lia.
Qed.

Lemma extends_refl : forall S, extends S S.
Proof.
  intros S. unfold extends. exists []. rewrite app_nil_r. auto.
Qed.

Lemma extends_app : forall S S2, extends (S ++ S2) S.
Proof.
  intros. unfold extends. exists S2. auto.
Qed.

Lemma has_type_extends : forall G S t T S',
  has_type G S t T ->
  extends S' S ->
  has_type G S' t T.
Proof.
  intros G S t T S' Htyp Hext.
  revert S' Hext.
  induction Htyp; intros S'' Hext.
  - apply T_Var. auto.
  - apply T_Num.
  - apply T_Bool.
  - apply T_Succ. apply IHHtyp. assumption.
  - apply T_Pred. apply IHHtyp. assumption.
  - apply T_IsZero. apply IHHtyp. assumption.
  - eapply T_If; [ apply IHHtyp1 | apply IHHtyp2 | apply IHHtyp3 ]; eassumption.
  - apply T_Lam. apply IHHtyp. assumption.
  - eapply T_App; [ apply IHHtyp1 | apply IHHtyp2 ]; eassumption.
  - apply T_Fix. apply IHHtyp. assumption.
  - apply T_Ref. apply IHHtyp. assumption.
  - apply T_Deref. apply IHHtyp. assumption.
  - eapply T_Assign; [ apply IHHtyp1 | apply IHHtyp2 ]; eassumption.
  - apply T_Loc. unfold extends in Hext. destruct Hext as [S2 HS'].
    rewrite HS'. apply nth_error_app_l. auto.
Qed.

Lemma nth_error_insert_var : forall {A : Type} (G : list A) (x d : nat) (T a : A),
  nth_error G x = Some T ->
  nth_error (firstn d G ++ a :: skipn d G) (if x <? d then x else S x) = Some T.
Proof.
  intros A G x d T a H.
  induction d in G, x, H |- *; simpl.
  - destruct x; simpl in *.
    + assumption.
    + rewrite H. auto.
  - destruct G as [|h G]; simpl.
    + destruct x; inversion H.
    + destruct x as [|x]; simpl in *.
      * inversion H; subst; auto.
      * replace (S x <? S d) with (x <? d) by reflexivity.
        destruct (x <? d) eqn:Heq; simpl.
        -- apply IHd in H. rewrite Heq in H. simpl in H. exact H.
        -- apply IHd in H. rewrite Heq in H. simpl in H. exact H.
Qed.

Lemma nth_error_insert_lt : forall {A : Type} (G : list A) (x d : nat) (T a : A),
  x < d -> nth_error G x = Some T ->
  nth_error (firstn d G ++ a :: skipn d G) x = Some T.
Proof.
  intros * Hlt Hnth.
  assert (x < length G) by (apply nth_error_Some; intros Hnone; rewrite Hnone in Hnth; discriminate).
  assert (Hlenf : x < length (firstn d G)).
  { rewrite firstn_length. lia. }
  rewrite nth_error_app1 by assumption.
  rewrite nth_error_firstn.
  assert (x <? d = true) by (apply Nat.ltb_lt; assumption).
  rewrite H0. assumption.
Qed.

Lemma nth_error_insert_ge : forall {A : Type} (G : list A) (x d : nat) (T a : A),
  x >= d -> nth_error G x = Some T ->
  nth_error (firstn d G ++ a :: skipn d G) (x + 1) = Some T.
Proof.
  intros * Hge Hnth.
  assert (x < length G) by (apply nth_error_Some; intros Hnone; rewrite Hnone in Hnth; discriminate).
  assert (Hmin : Init.Nat.min d (length G) = d) by lia.
  rewrite nth_error_app2.
  - rewrite firstn_length, Hmin.
    replace (x + 1 - d) with (S (x - d)) by lia.
    simpl. rewrite nth_error_skipn.
    replace (d + (x - d)) with x by lia.
    assumption.
  - rewrite firstn_length. lia.
Qed.

Lemma has_type_shift_at : forall d G St t T T',
  has_type G St t T ->
  has_type (firstn d G ++ T' :: skipn d G) St (shift_at d t) T.
Proof.
  intros d G St t T T' H.
  revert d.
  induction H; intros d; simpl.
  - simpl. destruct (x <? d) eqn:Hx.
    + apply T_Var. eapply nth_error_insert_lt; try eassumption.
      apply Nat.ltb_lt. assumption.
    + apply T_Var. eapply nth_error_insert_ge; try eassumption.
      apply Nat.ltb_nlt in Hx. lia.
  - apply T_Num.
  - apply T_Bool.
  - apply T_Succ. apply IHhas_type.
  - apply T_Pred. apply IHhas_type.
  - apply T_IsZero. apply IHhas_type.
  - eapply T_If; eapply IHhas_type1 || eapply IHhas_type2 || eapply IHhas_type3; eauto.
  - apply T_Lam. apply IHhas_type with (d := S d).
  - eapply T_App; eapply IHhas_type1 || eapply IHhas_type2; eauto.
  - apply T_Fix. apply IHhas_type with (d := S d).
  - apply T_Ref. apply IHhas_type.
  - apply T_Deref. apply IHhas_type.
  - eapply T_Assign; eapply IHhas_type1 || eapply IHhas_type2; eauto.
  - apply T_Loc. assumption.
Qed.

Lemma has_type_shift : forall G St t T T',
  has_type G St t T ->
  has_type (T' :: G) St (shift t) T.
Proof.
  intros G St t T T' H.
  apply has_type_shift_at with (d := 0); assumption.
Qed.

Lemma nth_error_snoc_Some : forall {A : Type} (G : list A) (U T : A) (x : nat),
  nth_error (G ++ [U]) x = Some T ->
  (x < length G /\ nth_error G x = Some T) \/ (x = length G /\ T = U).
Proof.
  intros A G U T x H.
  rewrite nth_error_app in H.
  destruct (x <? length G) eqn:Hlt.
  - left. split.
    + apply Nat.ltb_lt; assumption.
    + assumption.
  - right.
    apply Nat.ltb_nlt in Hlt.
    assert (Hx : x = length G).
    { simpl in H. destruct (x - length G) eqn:Heq; simpl in H.
      - apply Nat.sub_0_le in Heq. lia.
      - inversion H. }
    subst x. simpl in H. inversion H. subst. auto.
Qed.

Lemma has_type_subst_gen : forall j C St t T v U,
  nth_error C j = Some U ->
  has_type C St t T ->
  has_type (firstn j C ++ skipn (S j) C) St v U ->
  has_type (firstn j C ++ skipn (S j) C) St (subst j v t) T.
Proof.
  induction t as [n | n0 | b | t1 IH1 | t1 IH1 | t1 IH1 | t1 IH1 t2 IH2 t3 IH3 | T0 t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 | t1 IH1 | t1 IH1 t2 IH2 | n0];
    intros T v U Hnth Ht Hv; inversion Ht; subst; simpl.
  - (* Var *)
    simpl in H.
    destruct (n0 <? j) eqn:Hlt.
    + apply T_Var.
      rewrite nth_error_app1.
      * rewrite nth_error_firstn, Hlt. exact H.
      * rewrite firstn_length. apply Nat.ltb_lt in Hlt. lia.
    + apply Nat.ltb_nlt in Hlt.
      destruct (Nat.eq_dec n0 j).
      * subst n0. rewrite Hnth in H. inversion H. subst. assumption.
      * assert (n0 > j) by lia.
        apply T_Var.
        rewrite nth_error_app2.
        -- rewrite firstn_length.
           replace (length (firstn j C)) with j by (rewrite firstn_length; lia).
           replace (n0 - j - 1) with (n0 - S j) by lia.
           rewrite nth_error_skipn.
           replace (S j + (n0 - S j)) with n0 by lia.
           exact H.
        -- rewrite firstn_length. lia.
  - (* Num *) apply T_Num.
  - (* Bool *) apply T_Bool.
  - (* Succ *) apply T_Succ. apply IH1 with (v := v); assumption.
  - (* Pred *) apply T_Pred. apply IH1 with (v := v); assumption.
  - (* IsZero *) apply T_IsZero. apply IH1 with (v := v); assumption.
  - (* If *)
    eapply T_If; [apply IH1 with (v := v) | apply IH2 with (v := v) | apply IH3 with (v := v)]; assumption.
  - (* Lam *)
    apply T_Lam.
    apply IH1 with (j := S j) (C := T0 :: C) (v := shift v) (U := U).
    + simpl. assumption.
    + assumption.
    + simpl. apply has_type_shift. assumption.
  - (* App *)
    eapply T_App; [apply IH1 with (v := v) | apply IH2 with (v := v)]; assumption.
  - (* Fix *)
    apply T_Fix.
    apply IH1 with (j := S j) (C := T :: C) (v := shift v) (U := U).
    + simpl. assumption.
    + assumption.
    + simpl. apply has_type_shift. assumption.
  - (* Ref *) apply T_Ref. apply IH1 with (v := v); assumption.
  - (* Deref *) apply T_Deref. apply IH1 with (v := v); assumption.
  - (* Assign *)
    eapply T_Assign; [apply IH1 with (v := v) | apply IH2 with (v := v)]; assumption.
  - simpl in H. (* Loc *) apply T_Loc. assumption.
Qed.
  - (* T_Var *)
    simpl in H.
    destruct (x <? j') eqn:Hlt.
    + (* x < j', variable before the substitution point *)
      apply T_Var.
      rewrite nth_error_app1.
      * rewrite nth_error_firstn, Hlt. exact H.
      * rewrite firstn_length. apply Nat.ltb_lt in Hlt. lia.
    + (* x >= j' *)
      apply Nat.ltb_nlt in Hlt.
      destruct (Nat.eq_dec x j') as [Heq | Hneq].
      * (* x = j', the substituted variable *)
        subst x.
        assert (T = U') by (rewrite Hnth' in H; inversion H; auto).
        subst T. exact Hv'.
      * (* x > j', variable after the substitution point *)
        apply T_Var.
        assert (Hxgt : x > j') by lia.
        rewrite nth_error_app2.
        -- rewrite firstn_length.
           replace (length (firstn j' C)) with j' by (rewrite firstn_length; lia).
           replace (x - j' - 1) with (x - S j') by lia.
           rewrite nth_error_skipn.
           replace (S j' + (x - S j')) with x by lia.
           exact H.
        -- rewrite firstn_length. lia.
  - (* T_Num *) apply T_Num.
  - (* T_Bool *) apply T_Bool.
  - (* T_Succ *) apply T_Succ. eapply IHHt; eassumption.
  - (* T_Pred *) apply T_Pred. eapply IHHt; eassumption.
  - (* T_IsZero *) apply T_IsZero. eapply IHHt; eassumption.
  - (* T_If *)
    eapply T_If; [eapply IHHt1 | eapply IHHt2 | eapply IHHt3]; eassumption.
  - (* T_Lam *)
    apply T_Lam.
    eapply IHHt with (j' := S j') (v' := shift v').
    + simpl. apply Hnth'.
    + exact H0.
    + simpl. apply has_type_shift. exact Hv'.
  - (* T_App *)
    eapply T_App; [eapply IHHt1 | eapply IHHt2]; eassumption.
  - (* T_Fix *)
    apply T_Fix.
    eapply IHHt with (j' := S j') (v' := shift v').
    + simpl. apply Hnth'.
    + exact H0.
    + simpl. apply has_type_shift. exact Hv'.
  - (* T_Ref *) apply T_Ref. eapply IHHt; eassumption.
  - (* T_Deref *) apply T_Deref. eapply IHHt; eassumption.
  - (* T_Assign *)
    eapply T_Assign; [eapply IHHt1 | eapply IHHt2]; eassumption.
  - (* T_Loc *) apply T_Loc. assumption.
Qed.

Lemma has_type_subst_0 : forall S U body T v,
  has_type [U] S body T ->
  has_type [] S v U ->
  has_type [] S (subst 0 v body) T.
Proof.
  intros S U body T v Hbody Hv.
  eapply has_type_subst_gen with (j := 0) (C := [U]).
  - reflexivity.
  - exact Hbody.
  - simpl. exact Hv.
Qed.

Lemma heap_ok_extends : forall mu S S',
  heap_ok mu S ->
  extends S' S ->
  heap_ok mu S'.
Proof.
  intros mu S S' Hok Hext.
  induction Hok.
  - apply heap_empty.
  - apply heap_cons with (T := T); auto.
    + apply has_type_extends with (S := S); auto.
    + unfold extends in Hext. destruct Hext as [S2 HS'].
      rewrite HS'. apply nth_error_app_l. auto.
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
