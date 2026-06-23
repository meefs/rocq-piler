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

Lemma nth_error_Some_len : forall A l n (x : A),
  nth_error l n = Some x -> n < length l.
Proof.
  induction l; destruct n; simpl; intros; try discriminate; try lia.
  apply IHl in H. lia.
Qed.

Lemma extends_app_id : forall S, extends S S.
Proof.
  intro S. exists []. symmetry. apply app_nil_r.
Qed.

Lemma nth_error_app_l : forall A (l l' : list A) n,
  n < length l ->
  nth_error (l ++ l') n = nth_error l n.
Proof.
  induction l; simpl; intros; try lia.
  destruct n; simpl; auto.
  apply IHl; lia.
Qed.

Lemma nth_error_app_r : forall A (l l' : list A) n,
  nth_error (l ++ l') (length l + n) = nth_error l' n.
Proof.
  induction l; simpl; intros; auto.
Qed.

Lemma nth_error_app_singleton_r : forall A (l : list A) (x : A),
  nth_error (l ++ [x]) (length l) = Some x.
Proof.
  intros.
  replace (length l) with (length l + 0) by lia.
  rewrite nth_error_app_r. reflexivity.
Qed.

Lemma store_weakening : forall G S t T S',
  has_type G S t T ->
  extends S' S ->
  has_type G S' t T.
Proof.
  intros G S t T S' Ht [S2 HS']; subst.
  induction Ht.
  - apply T_Var; auto.
  - apply T_Num.
  - apply T_Bool.
  - apply T_Succ; apply IHHt.
  - apply T_Pred; apply IHHt.
  - apply T_IsZero; apply IHHt.
  - eapply T_If; eauto.
  - eapply T_Lam; eauto.
  - eapply T_App; eauto.
  - eapply T_Fix; eauto.
  - eapply T_Ref; eauto.
  - eapply T_Deref; eauto.
  - eapply T_Assign; eauto.
  - apply T_Loc.
    rewrite nth_error_app_l.
    + apply H.
    + eapply nth_error_Some_len. eauto.
Qed.

Lemma heap_ok_weakening : forall mu S S',
  heap_ok mu S ->
  extends S' S ->
  heap_ok mu S'.
Proof.
  intros mu S S' Hok [S2 HS']; subst.
  induction Hok.
  - apply heap_empty.
  - apply heap_cons with (T := T).
    + apply IHHok.
    + apply store_weakening with (S := S); auto. exists S2; auto.
    + rewrite nth_error_app_l.
      * apply H0.
      * eapply nth_error_Some_len. eauto.
Qed.

Lemma shift_at_typing : forall G1 G2 St t T U,
  has_type (G1 ++ G2) St t T ->
  has_type (G1 ++ U :: G2) St (shift_at (length G1) t) T.
Proof.
  intros G1 G2 St t T U Ht.
  remember (G1 ++ G2) as G eqn:HeqG.
  revert G1 G2 HeqG.
  induction Ht; intros Ga Gb HeqG; subst.
  - (* T_Var *)
    simpl.
    rename x into i.
    destruct (i <? length Ga) eqn:E.
    + apply Nat.ltb_lt in E.
      apply T_Var.
      rewrite (nth_error_app_l ty Ga (U :: Gb) i E).
      rewrite (nth_error_app_l ty Ga Gb i E) in H.
      exact H.
    + apply Nat.ltb_nlt in E.
      apply T_Var.
      assert (Hi : i = length Ga + (i - length Ga)) by lia.
      rewrite Hi in *.
      rewrite nth_error_app_r in H.
      replace (length Ga + (i - length Ga) + 1)
        with (length Ga + (i - length Ga + 1)) by lia.
      rewrite nth_error_app_r.
      rewrite Nat.add_comm.
      simpl.
      exact H.
  - (* T_Num *) simpl. apply T_Num.
  - (* T_Bool *) simpl. apply T_Bool.
  - (* T_Succ *) simpl. apply T_Succ; eauto.
  - (* T_Pred *) simpl. apply T_Pred; eauto.
  - (* T_IsZero *) simpl. apply T_IsZero; eauto.
  - (* T_If *) simpl. eapply T_If; eauto.
  - (* T_Lam *)
    simpl.
    eapply T_Lam.
    apply (IHHt (T1 :: Ga) Gb).
    reflexivity.
  - (* T_App *) simpl. eapply T_App; eauto.
  - (* T_Fix *)
    simpl.
    eapply T_Fix.
    apply (IHHt (T :: Ga) Gb).
    reflexivity.
  - (* T_Ref *) simpl. eapply T_Ref; eauto.
  - (* T_Deref *) simpl. eapply T_Deref; eauto.
  - (* T_Assign *) simpl. eapply T_Assign; eauto.
  - (* T_Loc *) simpl. apply T_Loc; auto.
Qed.

(** * Heap lemmas *)

Lemma heap_ok_lookup : forall mu S l v,
  heap_ok mu S ->
  heap_lookup l mu = Some v ->
  exists T, has_type [] S v T /\ nth_error S l = Some T.
Proof.
  induction mu as [|[l' v'] mu IH]; simpl; intros S l v Hok Hlook.
  - discriminate.
  - destruct (Nat.eqb_spec l l').
    + subst. inversion Hlook; subst.
      inversion Hok; subst.
      exists T; auto.
    + inversion Hok; subst.
      apply IH; auto.
Qed.

Lemma heap_ok_lookup_type : forall mu S l v T,
  heap_ok mu S ->
  heap_lookup l mu = Some v ->
  nth_error S l = Some T ->
  has_type [] S v T.
Proof.
  intros mu S l v T Hok Hlook Hnth.
  apply heap_ok_lookup with (l := l) (v := v) in Hok; auto.
  destruct Hok as [T' [Hty Hnth']].
  rewrite Hnth' in Hnth. inversion Hnth. subst. apply Hty.
Qed.

Lemma heap_ok_update : forall mu S l v T,
  heap_ok mu S ->
  has_type [] S v T ->
  nth_error S l = Some T ->
  heap_ok (heap_update l v mu) S.
Proof.
  induction mu as [|[l' v'] mu IH]; intros S l v T Hok Hty Hnth; simpl.
  - apply heap_empty.
  - destruct (Nat.eqb_spec l l').
    + subst l'.
      inversion Hok as [|? ? mu' ? T0 Hok' Hty' Hnth']; subst; clear Hok.
      apply (heap_cons l v mu S T); [exact Hok' | exact Hty | exact Hnth].
    + inversion Hok as [|l0 v0 mu0 ? T0 Hok' Hty' Hnth']; subst; clear Hok.
      apply (heap_cons l' v' (heap_update l v mu) S T0);
        [apply (IH S l v T); auto | exact Hty' | exact Hnth'].
Qed.

(** * Substitution lemma *)

Lemma shift_weakening : forall G St t T T',
  has_type G St t T ->
  has_type (T' :: G) St (shift t) T.
Proof.
  intros G St t T T' Ht.
  apply (shift_at_typing [] G St t T T').
  simpl. exact Ht.
Qed.

Lemma substitution : forall G St s t T U,
  has_type G St s T ->
  has_type (G ++ T :: []) St t U ->
  has_type G St (subst (length G) s t) U.
Proof.
  intros G St s t T U Hs Ht.
  remember (G ++ T :: []) as C eqn:HeqC.
  revert G T Hs HeqC Ht.
  induction t; intros G T Hs HeqC Hty; inversion Hty; subst; simpl.
  - (* Var *)
    destruct (Nat.eqb_spec n (length G)).
    + subst n.
      rewrite (nth_error_app_singleton_r ty G T) in H2.
      inversion H2; subst; clear H2.
      apply Hs.
    + assert (n < length G) as Hlt.
      { pose proof (nth_error_Some_len ty (G ++ [T]) n _ H2).
        simpl in H0. destruct (n <? length G) eqn:E.
        - apply Nat.ltb_lt in E; exact E.
        - apply Nat.ltb_nlt in E; lia. }
      rewrite (nth_error_app_l ty G [T] n Hlt) in H2.
      apply T_Var. exact H2.
  - (* Num *) apply T_Num.
  - (* BOOL *) apply T_Bool.
  - (* Succ *) apply T_Succ. eapply IHt; eauto.
  - (* Pred *) apply T_Pred. eapply IHt; eauto.
  - (* IsZero *) apply T_IsZero. eapply IHt; eauto.
  - (* If *) eapply T_If; eauto.
  - (* Lam *)
    apply T_Lam.
    eapply IHt with (G := T0 :: G) (T := T); eauto.
    + simpl. reflexivity.
    + apply shift_weakening; auto.
  - (* App *) eapply T_App; eauto.
  - (* Fix *)
    apply T_Fix.
    eapply IHt with (G := T1 :: G) (T := T); eauto.
    + simpl. reflexivity.
    + apply shift_weakening; auto.
  - (* Ref *) eapply T_Ref; eauto.
  - (* Deref *) eapply T_Deref; eauto.
  - (* Assign *) eapply T_Assign; eauto.
  - (* Loc *) apply T_Loc. auto.
Qed.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Theorem preservation :
  forall t mu t' mu' Ty S,
    has_type [] S t Ty ->
    step t mu t' mu' ->
    heap_ok mu S ->
    length mu >= length S ->
    exists S',
      extends S' S /\
      heap_ok mu' S' /\
      has_type [] S' t' Ty.
Proof.
  intros t mu t' mu' Ty S Ht Hstep Hok Hlen.
  revert Ty S Ht Hok Hlen.
  induction Hstep; intros Ty' S' Ht' Hok' Hlen'.
  - (* S_Succ *)
    inversion Ht'; subst; clear Ht'.
    match goal with H: has_type [] S' ?x TyNat |- _ =>
      destruct (IHHstep TyNat _ H Hok' Hlen')
        as [S'' [Hext [Hok'' Ht'']]]
    end.
    exists S''; split; [| split]; auto.
    apply T_Succ; auto.
  - (* S_PredZero *)
    inversion Ht'; subst; clear Ht'.
    match goal with H: has_type [] S' (Num 0) TyNat |- _ =>
      inversion H; subst; clear H
    end.
    exists S'; split; [| split]; [apply extends_app_id | auto | apply T_Num].
  - (* S_PredSucc *)
    inversion Ht'; subst; clear Ht'.
    match goal with H: has_type [] S' (Num (S n)) TyNat |- _ =>
      inversion H; subst; clear H
    end.
    exists S'; split; [| split]; [apply extends_app_id | auto | apply T_Num].
  - (* S_Pred *)
    inversion Ht'; subst; clear Ht'.
    match goal with H: has_type [] S' ?x TyNat |- _ =>
      destruct (IHHstep TyNat _ H Hok' Hlen')
        as [S'' [Hext [Hok'' Ht'']]]
    end.
    exists S''; split; [| split]; auto.
    apply T_Pred; auto.
  - (* S_IsZeroZero *)
    inversion Ht'; subst; clear Ht'.
    match goal with H: has_type [] S' (Num 0) TyNat |- _ =>
      inversion H; subst; clear H
    end.
    exists S'; split; [| split]; [apply extends_app_id | auto | apply T_Bool].
  - (* S_IsZeroSucc *)
    inversion Ht'; subst; clear Ht'.
    match goal with H: has_type [] S' (Num (S n)) TyNat |- _ =>
      inversion H; subst; clear H
    end.
    exists S'; split; [| split]; [apply extends_app_id | auto | apply T_Bool].
  - (* S_IsZero *)
    inversion Ht'; subst; clear Ht'.
    match goal with H: has_type [] S' ?x TyNat |- _ =>
      destruct (IHHstep TyNat _ H Hok' Hlen')
        as [S'' [Hext [Hok'' Ht'']]]
    end.
    exists S''; split; [| split]; auto.
    apply T_IsZero; auto.
  - (* S_IfTrue *)
    inversion Ht'; subst; clear Ht'.
    exists S'; split; [| split].
    + apply extends_app_id.
    + auto.
    + match goal with H: has_type [] S' ?x Ty' |- _ =>
        eapply store_weakening; [exact H | apply extends_app_id]
      end.
  - (* S_IfFalse *)
    inversion Ht'; subst; clear Ht'.
    exists S'; split; [| split].
    + apply extends_app_id.
    + auto.
    + match goal with H: has_type [] S' ?x Ty' |- _ =>
        eapply store_weakening; [exact H | apply extends_app_id]
      end.
  - (* S_If *)
    inversion Ht'; clear Ht'.
    match goal with
    | H1: has_type [] S' ?x TyBool, H2: has_type [] S' ?y ?Ty, H3: has_type [] S' ?z ?Ty |- _ =>
      subst;
      destruct (IHHstep TyBool _ H1 Hok' Hlen')
        as [S'' [Hext [Hok'' Ht'']]];
      exists S''; split; [| split]; auto;
      apply (T_If [] S'' t' y z Ty);
      [exact Ht'' | eapply store_weakening; [exact H2 | eauto] | eapply store_weakening; [exact H3 | eauto]]
    end.
  - (* S_App1 *)
    inversion Ht'; subst; clear Ht'.
    match goal with
    | H: has_type [] S' ?x (TyArrow ?T1 ?T2), H': has_type [] S' ?y ?T1 |- _ =>
      destruct (IHHstep (TyArrow T1 T2) _ H Hok' Hlen')
        as [S'' [Hext [Hok'' Ht'']]];
      exists S''; split; [| split]; auto;
      apply (T_App [] S'' t' y T1 T2);
      [exact Ht'' | eapply store_weakening; [exact H' | eauto]]
    end.
  - (* S_App2 *)
    inversion Ht'; subst; clear Ht'.
    match goal with
    | H: has_type [] S' ?x ?T1, H': has_type [] S' v1 (TyArrow ?T1 ?T2) |- _ =>
      destruct (IHHstep T1 _ H Hok' Hlen')
        as [S'' [Hext [Hok'' Ht'']]];
      exists S''; split; [| split]; auto;
      apply (T_App [] S'' v1 t' T1 T2);
      [eapply store_weakening; [exact H' | eauto] | exact Ht'']
    end.
  - (* S_AppAbs *)
    inversion Ht'; subst; clear Ht'.
    exists S'; split; [| split].
    + apply extends_app_id.
    + auto.
    + match goal with
      | Hlam: has_type [] S' (Lam ?T1 ?t1) (TyArrow ?T1 ?T2),
        Hv: has_type [] S' v2 ?T1 |- _ =>
        inversion Hlam; subst; clear Hlam;
        apply (substitution [] S' v2 t1 T1 T2); auto
      end.
  - (* S_Fix *)
    inversion Ht'; subst; clear Ht'.
    exists S'; split; [| split].
    + apply extends_app_id.
    + auto.
    + match goal with
      | Hfix: has_type [] S' (Fix ?t1) ?T |- _ =>
        inversion Hfix; subst; clear Hfix;
        apply (substitution [] S' (Fix t1) t1 T T); auto
      end.
  - (* S_Ref *)
    inversion Ht'; subst; clear Ht'.
    match goal with H: has_type [] S' ?x ?T |- _ =>
      destruct (IHHstep T _ H Hok' Hlen')
        as [S'' [Hext [Hok'' Ht'']]]
    end.
    exists S''; split; [| split]; auto.
    apply T_Ref; auto.
  - (* S_RefV *)
    inversion Ht'; subst; clear Ht'.
    exists (S' ++ [Ty']).
    split; [| split].
    + exists [Ty']. auto.
    + apply heap_cons with (T := Ty'); auto.
      * apply heap_ok_weakening with (S := S'); auto.
        exists [Ty']. auto.
      * apply store_weakening with (S := S'); auto.
        exists [Ty']. auto.
      * rewrite nth_error_app_r. simpl. reflexivity.
    + apply T_Loc.
      rewrite nth_error_app_r. simpl. reflexivity.
  - (* S_Deref *)
    inversion Ht'; subst; clear Ht'.
    match goal with H: has_type [] S' ?x (TyRef ?T) |- _ =>
      destruct (IHHstep (TyRef T) _ H Hok' Hlen')
        as [S'' [Hext [Hok'' Ht'']]]
    end.
    exists S''; split; [| split]; auto.
    apply T_Deref; auto.
  - (* S_DerefLoc *)
    inversion Ht'; subst; clear Ht'.
    exists S'; split; [| split].
    + apply extends_app_id.
    + auto.
    + apply heap_ok_lookup_type with (mu := mu) (S := S') (l := l) (v := v) (T := Ty'); auto.
      match goal with H: heap_lookup l mu = Some v |- _ => exact H end.
  - (* S_Assign1 *)
    inversion Ht'; subst; clear Ht'.
    match goal with
    | H: has_type [] S' ?x (TyRef ?T0), Hv: has_type [] S' ?y ?T0 |- _ =>
      destruct (IHHstep (TyRef T0) _ H Hok' Hlen')
        as [S'' [Hext [Hok'' Ht'']]];
      exists S''; split; [| split]; auto;
      apply (T_Assign [] S'' t' y T0);
      [exact Ht'' | eapply store_weakening; [exact Hv | eauto]]
    end.
  - (* S_Assign2 *)
    inversion Ht'; subst; clear Ht'.
    match goal with
    | H: has_type [] S' ?x ?T0, Hloc: has_type [] S' (Loc l) (TyRef ?T0) |- _ =>
      destruct (IHHstep T0 _ H Hok' Hlen')
        as [S'' [Hext [Hok'' Ht'']]];
      exists S''; split; [| split]; auto;
      apply (T_Assign [] S'' (Loc l) t' T0);
      [eapply store_weakening; [exact Hloc | eauto] | exact Ht'']
    end.
  - (* S_AssignV *)
    inversion Ht'; subst; clear Ht'.
    match goal with
    | Hloc: has_type [] S' (Loc l) (TyRef ?T0) |- _ =>
      inversion Hloc; subst; clear Hloc
    end.
    exists S'; split; [| split].
    + apply extends_app_id.
    + match goal with
      | Hv: has_type [] S' v ?T0, Hnth: nth_error S' l = Some ?T0 |- _ =>
        apply (heap_ok_update mu S' l v T0 Hok' Hv Hnth)
      end.
    + apply T_Num.
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
