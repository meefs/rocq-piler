From Stdlib Require Import Arith List Lia.
From Stdlib Require Import Program.Equality.
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

Lemma extends_refl : forall S, extends S S.
Proof.
  intros S. exists []. rewrite app_nil_r. reflexivity.
Qed.

Lemma has_type_store_weaken : forall G S t T S',
    has_type G S t T ->
    extends S' S ->
    has_type G S' t T.
Proof.
  intros G S t T S' Htyp Hext.
  induction Htyp.
  - eapply T_Var; eauto.
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
  - destruct Hext as [S2 ->].
    eapply T_Loc.
    rewrite nth_error_app1; [exact H | ].
    apply nth_error_Some; rewrite H; discriminate.
Qed.

Lemma heap_ok_extends : forall mu S S',
    heap_ok mu S ->
    extends S' S ->
    heap_ok mu S'.
Proof.
  intros mu S S' Hhok Hext.
  induction Hhok as [| l v mu S T Hhok IH Hv Hnth].
  - apply heap_empty.
  - apply heap_cons with (T := T).
    + apply IH; assumption.
    + eapply has_type_store_weaken; eassumption.
    + destruct Hext as [S2 ->].
      rewrite nth_error_app1; [exact Hnth | ].
      apply nth_error_Some; rewrite Hnth; discriminate.
Qed.

Lemma heap_lookup_sound : forall mu S l v,
    heap_ok mu S ->
    heap_lookup l mu = Some v ->
    exists T, nth_error S l = Some T /\ has_type [] S v T.
Proof.
  intros mu S l v Hhok.
  induction Hhok as [| l0 v0 mu S T Hhok IH Hv Hnth].
  - intros H. discriminate.
  - simpl. intros Hlookup.
    destruct (Nat.eqb l l0) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst l0.
      injection Hlookup as ->.
      exists T. split; assumption.
    + apply IH. assumption.
Qed.

Lemma weakening_shift : forall G1 G2 St t T T',
    has_type (G1 ++ G2) St t T ->
    has_type (G1 ++ T' :: G2) St (shift_at (length G1) t) T.
Proof.
  intros G1 G2 St t T T' Htyp.
  remember (G1 ++ G2) as G eqn:HeqG.
  revert G1 G2 HeqG.
  induction Htyp; intros G1' G2' HeqG'.
  - subst G.
    simpl. destruct (x <? length G1') eqn:Hlt.
    + apply Nat.ltb_lt in Hlt.
      apply T_Var.
      rewrite nth_error_app1 with (l' := T' :: G2') by assumption.
      rewrite nth_error_app1 with (l' := G2') in H by assumption.
      assumption.
    + apply Nat.ltb_ge in Hlt.
      apply T_Var.
      rewrite nth_error_app2 with (l' := T' :: G2') by lia.
      rewrite nth_error_app2 with (l' := G2') in H by lia.
      assert (x + 1 - length G1' = (x - length G1') + 1) by lia.
      rewrite H0, Nat.add_1_r.
      simpl. exact H.
  - apply T_Num.
  - apply T_Bool.
  - simpl. apply T_Succ. eapply IHHtyp; eauto.
  - simpl. apply T_Pred. eapply IHHtyp; eauto.
  - simpl. apply T_IsZero. eapply IHHtyp; eauto.
  - simpl. apply T_If.
    + eapply IHHtyp1; eauto.
    + eapply IHHtyp2; eauto.
    + eapply IHHtyp3; eauto.
  - simpl. apply T_Lam.
    apply IHHtyp with (G1 := T1 :: G1') (G2 := G2').
    subst G. rewrite <- app_comm_cons. reflexivity.
  - simpl. apply T_App with (T1 := T1).
    + eapply IHHtyp1; eauto.
    + eapply IHHtyp2; eauto.
  - simpl. apply T_Fix.
    apply IHHtyp with (G1 := T :: G1') (G2 := G2').
    subst G. rewrite <- app_comm_cons. reflexivity.
  - simpl. apply T_Ref. eapply IHHtyp; eauto.
  - simpl. apply T_Deref. eapply IHHtyp; eauto.
  - simpl. apply T_Assign with (T := T).
    + eapply IHHtyp1; eauto.
    + eapply IHHtyp2; eauto.
  - simpl. apply T_Loc.
    subst G. assumption.
Qed.

Lemma nth_error_app_left_length : forall A (l : list A) x,
    nth_error (l ++ [x]) (length l) = Some x.
Proof.
  induction l; simpl; [reflexivity | assumption].
Qed.

Lemma subst_typing : forall G St t T s T',
    has_type (G ++ [T']) St t T ->
    has_type G St s T' ->
    has_type G St (subst (length G) s t) T.
Proof.
  intros G St t T s T' Htyp Hs. revert Htyp Hs. revert G s T' T. induction t; intros G s T' T Htyp Hs; inversion Htyp; subst; simpl.
  { (* case_1:ff4da908 *)
    destruct (Nat.eqb n (length G)) eqn:Heq.
    - apply Nat.eqb_eq in Heq. subst n.
      rewrite (nth_error_app_left_length ty G T') in H2.
      assert (T' = T) by (inversion H2; reflexivity).
      subst T'. assumption.
    - apply T_Var.
      assert (n < length G \/ n >= length G) as [Hcase|Hcase] by lia.
      + rewrite nth_error_app1 in H2 by assumption. assumption.
      + rewrite nth_error_app2 in H2 by assumption.
        simpl in H2.
        destruct (n - length G) eqn:Hsub; simpl in H2.
        * assert (n = length G) by lia. subst n.
          exfalso. apply Nat.eqb_neq in Heq. apply Heq. reflexivity.
        * discriminate. }
  { (* case_2:af3958df *) apply T_Num.
  }
  { (* case_3:5e0d7c5b *) apply T_Bool.
  }
  { (* case_4:c0dd90ae *) econstructor; eauto.
  }
  { (* case_5:9ccf1c5a *) econstructor; eauto.
  }
  { (* case_6:8d5d938c *) econstructor; eauto.
  }
  { (* case_7:63b92dbb *) econstructor; eauto.
  }
  { (* case_8:d02e92ae *) apply T_Lam; eapply IHt; [rewrite <- app_comm_cons; eassumption|simpl; eapply weakening_shift with (G1:=[])(G2:=G)(T':=t); simpl; eauto].
  }
  { (* case_9:ee971362 *) econstructor; eauto.
  }
  { (* case_10:1c08ce67 *) apply T_Fix; eapply IHt; [rewrite <- app_comm_cons; eassumption|simpl; eapply weakening_shift with (G1:=[])(G2:=G)(T':=T); simpl; eauto].
  }
  { (* case_11:8d9e73d4 *) econstructor; eauto.
  }
  { (* case_12:9a1cde3b *) econstructor; eauto.
  }
  { (* case_13:8cc9de45 *) econstructor; eauto.
  }
  { (* case_14:2c5eb784 *) apply T_Loc; assumption.
  }
Admitted.

Lemma subst_closed : forall St t T s T',
    has_type [T'] St t T ->
    has_type [] St s T' ->
    has_type [] St (subst 0 s t) T.
Proof.
  intros. eapply subst_typing with (G := []); eassumption.
Qed.

Lemma heap_update_ok : forall mu S l v T,
    heap_ok mu S ->
    has_type [] S v T ->
    nth_error S l = Some T ->
    heap_ok (heap_update l v mu) S.
Proof.
  intros mu S l v T Hhok Hv Hnth.
  induction Hhok as [| l0 v0 mu S T0 Hhok IH Hv0 Hnth0].
  - simpl. apply heap_empty.
  - simpl. destruct (Nat.eqb l l0) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst l0.
      rewrite Hnth in Hnth0. inversion Hnth0. subst T0.
      apply heap_cons with (T := T); auto.
    + apply heap_cons with (T := T0); auto.
Qed.

Lemma store_extension_alloc : forall mu S T,
    heap_ok mu S ->
    length mu >= length S ->
    exists S', extends S' S /\ heap_ok mu S' /\ nth_error S' (length mu) = Some T.
Proof.
  intros mu S T Hhok Hlen.
  set (k := length mu - length S).
  exists (S ++ repeat TyNat k ++ [T]).
  split.
  - exists (repeat TyNat k ++ [T]). reflexivity.
  - split.
    + apply heap_ok_extends with (S := S); auto.
      exists (repeat TyNat k ++ [T]). reflexivity.
    + assert (Hlen_eq : length mu = length S + k) by lia.
      rewrite Hlen_eq.
      rewrite nth_error_app2 by lia.
      replace (length S + k - length S) with k by lia.
      rewrite nth_error_app2 by (rewrite repeat_length; lia).
      rewrite repeat_length.
      replace (k - k) with 0 by lia.
      reflexivity.
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
  intros t mu t' mu' T0 S0 Htyp Hstep Hhok Hlen. revert T0 S0 Htyp Hhok Hlen. induction Hstep; intros T0 S0 Htyp Hhok Hlen.
  { (* S_Succ:58387bbc *) inversion Htyp; subst; edestruct IHHstep as [S' [Hext [Hhok' Htyp']]]; eauto; exists S'; split; [assumption | split; [assumption | econstructor; eauto using has_type_store_weaken]].
  }
  { (* S_PredZero:3961c05a *) inversion Htyp; subst; exists S0; split; [apply extends_refl | split; [assumption | eauto 3]].
  }
  { (* S_PredSucc:dc5b51a6 *) inversion Htyp; subst; exists S0; split; [apply extends_refl | split; [assumption | eauto 3]].
    { (* 741ddd52 *) apply T_Num.
    }
  }
  { (* S_Pred:060efb54 *) inversion Htyp; subst; edestruct IHHstep as [S' [Hext [Hhok' Htyp']]]; eauto; exists S'; split; [assumption | split; [assumption | econstructor; eauto using has_type_store_weaken]].
  }
  { (* S_IsZeroZero:1253d94b *) inversion Htyp; subst; exists S0; split; [apply extends_refl | split; [assumption | eauto 3]].
    { (* 8b0a9630 *) apply T_Bool.
    }
  }
  { (* S_IsZeroSucc:db5ccf76 *) inversion Htyp; subst; exists S0; split; [apply extends_refl | split; [assumption | eauto 3]].
    { (* 8e5b732e *) apply T_Bool.
    }
  }
  { (* S_IsZero:a2050d3f *) inversion Htyp; subst; edestruct IHHstep as [S' [Hext [Hhok' Htyp']]]; eauto; exists S'; split; [assumption | split; [assumption | econstructor; eauto using has_type_store_weaken]].
  }
  { (* S_IfTrue:e2855274 *) inversion Htyp; subst; exists S0; split; [apply extends_refl | split; [assumption | eauto 3]].
  }
  { (* S_IfFalse:0b2c15cd *) inversion Htyp; subst; exists S0; split; [apply extends_refl | split; [assumption | eauto 3]].
  }
  { (* S_If:e4733374 *) inversion Htyp; subst; edestruct IHHstep as [S' [Hext [Hhok' Htyp']]]; eauto; exists S'; split; [assumption | split; [assumption | econstructor; eauto using has_type_store_weaken]].
  }
  { (* S_App1:850d5fd9 *) inversion Htyp; subst; edestruct IHHstep as [S' [Hext [Hhok' Htyp']]]; eauto; exists S'; split; [assumption | split; [assumption | econstructor; eauto using has_type_store_weaken]].
  }
  { (* S_App2:39a35521 *) inversion Htyp; subst; edestruct IHHstep as [S' [Hext [Hhok' Htyp']]]; eauto; exists S'; split; [assumption | split; [assumption | econstructor; eauto using has_type_store_weaken]].
  }
  { (* S_AppAbs:dc04e8a2 *) inversion Htyp; subst; exists S0; split; [apply extends_refl | split; [assumption | eapply subst_closed; eauto]].
    { (* fda320c7 *) inversion Htyp; eauto.
      { (* fda320c7 *) inversion H4; subst; eauto.
      }
    }
  }
  { (* S_Fix:68f6aff8 *) inversion Htyp; subst; exists S0; split; [apply extends_refl | split; [assumption | eapply subst_closed; eauto]].
  }
  { (* S_Ref:7841fed7 *) inversion Htyp; subst; edestruct IHHstep as [S' [Hext [Hhok' Htyp']]]; eauto; exists S'; split; [assumption | split; [assumption | econstructor; eauto using has_type_store_weaken]].
  }
  { (* S_RefV:8dedfc67 *) inversion Htyp; subst; edestruct store_extension_alloc as [S' [Hext [Hhok' Hnth]]]; [eassumption | eassumption |]; exists S'; split; [eassumption | split; [apply heap_cons with (T := T); [eassumption | eapply has_type_store_weaken; [eassumption | eassumption] | eassumption] | apply T_Loc; eassumption]].
  }
  { (* S_Deref:0d1ebd03 *) inversion Htyp; subst; edestruct IHHstep as [S' [Hext [Hhok' Htyp']]]; eauto; exists S'; split; [assumption | split; [assumption | econstructor; eauto using has_type_store_weaken]].
  }
  { (* S_DerefLoc:b0b97791 *) inversion Htyp. subst. inversion H3. subst. edestruct heap_lookup_sound as [U [Hnth Hv]]; [eassumption | eassumption |]. rewrite H1 in Hnth. inversion Hnth. subst. exists S0. split; [apply extends_refl | split; [assumption | assumption]]. }
  { (* S_Assign1:8574e98b *) inversion Htyp; subst; edestruct IHHstep as [S' [Hext [Hhok' Htyp']]]; eauto; exists S'; split; [assumption | split; [assumption | econstructor; eauto using has_type_store_weaken]].
  }
  { (* S_Assign2:d2034227 *) inversion Htyp; subst; edestruct IHHstep as [S' [Hext [Hhok' Htyp']]]; eauto; exists S'; split; [assumption | split; [assumption | econstructor; eauto using has_type_store_weaken]].
  }
  { (* S_AssignV:fc5cb456 *) inversion Htyp; subst; exists S0; split; [apply extends_refl | split; [eapply heap_update_ok; eauto | apply T_Num]].
    { (* 2792886d *) inversion Htyp; eauto.
      { (* 2792886d *) inversion Htyp; subst; inversion H4; subst; eauto.
      }
    }
  }
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
