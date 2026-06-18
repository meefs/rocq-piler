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


Lemma nth_error_extends : forall (S S' : store_ty) l T, extends S' S -> nth_error S l = Some T -> nth_error S' l = Some T.
Proof.
intros S S' l T [S2 Heq] Hlookup; subst; rewrite nth_error_app1; auto; apply nth_error_Some; eauto.
  { (* ca12d036 *) congruence.
  }
Qed.


Lemma extends_refl : forall S, extends S S.
Proof.
intro S; exists []; symmetry; apply app_nil_r.
Qed.


Lemma store_weakening : forall G S S' t T, has_type G S t T -> extends S' S -> has_type G S' t T.
Proof.
intros G S S' t T Hty; generalize dependent S'; induction Hty; intros S' Hext; econstructor; eauto using nth_error_extends.
Qed.


Lemma heap_ok_extends : forall mu S S', heap_ok mu S -> extends S' S -> heap_ok mu S'.
Proof.
intros mu S S' Hok Hext; induction Hok; [constructor | econstructor; eauto using store_weakening, nth_error_extends].
Qed.


Lemma shift_at_typing : forall G1 G2 S t T U, has_type (G1 ++ G2) S t T -> has_type (G1 ++ U :: G2) S (shift_at (length G1) t) T.
Proof.
intros G1 G2 S t T U Hty; remember (G1 ++ G2) as G eqn:HeqG; generalize dependent G2; generalize dependent G1; generalize dependent U; induction Hty; intros U0 G1 G2 HeqG; subst; simpl.
  { (* 97964809 *) destruct (Nat.ltb_spec x (length G1)); apply T_Var.
    { (* cc764f6d *) rewrite nth_error_app1; [rewrite nth_error_app1 in H; auto | lia].
    }
    { (* fbcc27d1 *) rewrite nth_error_app2 by lia; rewrite nth_error_app2 in H by lia; replace (x + 1 - length G1) with (Datatypes.S (x - length G1)) by lia; simpl; auto.
    }
  }
  { (* 6dac3fa2 *) econstructor; eauto.
  }
  { (* bb09a75c *) econstructor; eauto.
  }
  { (* 23ac5da5 *) econstructor; eauto.
  }
  { (* cb4575a2 *) econstructor; eauto.
  }
  { (* 8eb03db7 *) econstructor; eauto.
  }
  { (* 23b6c962 *) econstructor; eauto.
  }
  { (* 7e4fff94 *) apply T_Lam; apply (IHHty U0 (T1 :: G1) G2); reflexivity.
  }
  { (* 70913f8f *) econstructor; eauto.
  }
  { (* 9c9c24c5 *) apply T_Fix; apply (IHHty U0 (T :: G1) G2); reflexivity.
  }
  { (* f2531750 *) econstructor; eauto.
  }
  { (* 937af232 *) econstructor; eauto.
  }
  { (* c23cdd53 *) econstructor; eauto.
  }
  { (* 6f8e09ac *) econstructor; eauto.
  }
Qed.


Lemma shift_typing : forall G S t T U, has_type G S t T -> has_type (U :: G) S (shift t) T.
Proof.
intros; apply (shift_at_typing [] G); auto.
Qed.

Lemma subst_preserves_typing : forall G T1 S t T s, has_type (G ++ [T1]) S t T -> has_type G S s T1 -> has_type G S (subst (length G) s t) T.
Proof.
intros G T1 S t T s Hty; remember (G ++ [T1]) as G' eqn:HeqG; generalize dependent s; generalize dependent G; generalize dependent T1; induction Hty; intros T1' G0 HeqG s Hs; subst; simpl.
  { (* bdc4413d *) destruct (Nat.eqb_spec x (length G0)).
    { (* 0d643fbf *) subst; rewrite nth_error_app2 in H by lia; replace (length G0 - length G0) with 0 in H by lia; simpl in H; injection H; intro; subst; auto.
    }
    { (* 9e3ce39e *) apply T_Var; assert (Hlt : x < length G0); [destruct (Nat.lt_ge_cases x (length G0)); [auto | exfalso; enough (nth_error (G0 ++ [T1']) x = None) by congruence; apply nth_error_None; rewrite length_app; simpl; lia] | rewrite nth_error_app1 in H; auto].
    }
  }
  { (* d63d0736 *) econstructor; eauto.
  }
  { (* 8e91a835 *) econstructor; eauto.
  }
  { (* 51f3dab0 *) econstructor; eauto.
  }
  { (* 71b443bb *) econstructor; eauto.
  }
  { (* 85a47e20 *) econstructor; eauto.
  }
  { (* 958c92d6 *) econstructor; eauto.
  }
  { (* 1ec7a8db *) apply T_Lam; apply (IHHty T1' (T1 :: G0)); [reflexivity | apply shift_typing; auto].
  }
  { (* d385497f *) econstructor; eauto.
  }
  { (* 40148c39 *) apply T_Fix; apply (IHHty T1' (T :: G0)); [reflexivity | apply shift_typing; auto].
  }
  { (* 538fa65c *) econstructor; eauto.
  }
  { (* e81dc67f *) econstructor; eauto.
  }
  { (* ddea7fb9 *) econstructor; eauto.
  }
  { (* 62c48aea *) econstructor; eauto.
  }
Qed.


Lemma heap_lookup_has_type : forall mu S l v, heap_ok mu S -> heap_lookup l mu = Some v -> exists T, nth_error S l = Some T /\ has_type [] S v T.
Proof.
intros mu S l v Hok; induction Hok; simpl; intros Hlookup; [discriminate | destruct (Nat.eqb_spec l l0); [injection Hlookup; intros; subst; eauto | eauto]].
Qed.


Lemma heap_update_ok : forall mu S l v T, heap_ok mu S -> has_type [] S v T -> nth_error S l = Some T -> heap_ok (heap_update l v mu) S.
Proof.
intros mu S l v T Hok; generalize dependent v; generalize dependent l; generalize dependent T; induction Hok; intros T0 l0 v0 Hty Hnth; simpl; [constructor | destruct (Nat.eqb_spec l0 l); [subst; econstructor; eauto | econstructor; eauto]].
Qed.


Lemma nth_error_app_length : forall (A : Type) (l : list A) (x : A), nth_error (l ++ [x]) (length l) = Some x.
Proof.
intros A l x; rewrite nth_error_app2 by lia; replace (length l - length l) with 0 by lia; reflexivity.
Qed.


Lemma extend_store_alloc : forall S n T, n >= length S -> exists S', extends S' S /\ nth_error S' n = Some T.
Proof.
intros S n T Hge; exists (S ++ repeat TyNat (n - length S) ++ [T]); split; [unfold extends; exists (repeat TyNat (n - length S) ++ [T]); reflexivity | rewrite nth_error_app2 by lia; rewrite nth_error_app2 by (rewrite repeat_length; lia); rewrite repeat_length; replace (n - length S - (n - length S)) with 0 by lia; reflexivity].
Qed.


Lemma extends_trans : forall S1 S2 S3, extends S2 S1 -> extends S3 S2 -> extends S3 S1.
Proof.
intros S1 S2 S3 [X HX] [Y HY]; exists (X ++ Y); subst; symmetry; apply app_assoc.
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
  intros t mu t' mu' T S Hty Hstep; generalize dependent T; generalize dependent S; induction Hstep; intros S T0 Hty Hok Hlen.
  { (* S_Succ:0dbc4944 *) solve [ inversion Hty; subst; edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto; exists S'; repeat split; auto; econstructor; eauto using store_weakening ]. }
  { (* S_PredZero:9f3ff8f3 *) solve [ exists S; repeat split; auto using extends_refl; inversion Hty; subst; econstructor; eauto ]. }
  { (* S_PredSucc:d8d23e17 *) solve [ exists S; repeat split; auto using extends_refl; inversion Hty; subst; econstructor; eauto ]. }
  { (* S_Pred:244acbfe *) solve [ inversion Hty; subst; edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto; exists S'; repeat split; auto; econstructor; eauto using store_weakening ]. }
  { (* S_IsZeroZero:f8f364c9 *) solve [ exists S; repeat split; auto using extends_refl; inversion Hty; subst; econstructor; eauto ]. }
  { (* S_IsZeroSucc:8b013bb7 *) solve [ exists S; repeat split; auto using extends_refl; inversion Hty; subst; econstructor; eauto ]. }
  { (* S_IsZero:9917d663 *) solve [ inversion Hty; subst; edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto; exists S'; repeat split; auto; econstructor; eauto using store_weakening ]. }
  { (* S_IfTrue:8d30f06e *) solve [ inversion Hty; subst; exists S; repeat split; auto using extends_refl; eapply subst_preserves_typing with (G:=[]); simpl; eauto ]. }
  { (* S_IfFalse:9bb8bd3d *) solve [ inversion Hty; subst; exists S; repeat split; auto using extends_refl; eapply subst_preserves_typing with (G:=[]); simpl; eauto ]. }
  { (* S_If:3ba3f57f *) solve [ inversion Hty; subst; edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto; exists S'; repeat split; auto; econstructor; eauto using store_weakening ]. }
  { (* S_App1:419457a5 *) solve [ inversion Hty; subst; edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto; exists S'; repeat split; auto; econstructor; eauto using store_weakening ]. }
  { (* S_App2:864d4d3a *) solve [ inversion Hty; subst; edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto; exists S'; repeat split; auto; econstructor; eauto using store_weakening ]. }
  { (* S_AppAbs:11573dbe *) inversion Hty; subst; inversion H4; subst; exists S; repeat split; auto using extends_refl; eapply (subst_preserves_typing [] T1); simpl; eauto.
  }
  { (* S_Fix:cd76500e *) solve [ inversion Hty; subst; exists S; repeat split; auto using extends_refl; eapply subst_preserves_typing with (G:=[]); simpl; eauto ]. }
  { (* S_Ref:1c95fd34 *) solve [ inversion Hty; subst; edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto; exists S'; repeat split; auto; econstructor; eauto using store_weakening ]. }
  { (* S_RefV:d8e5f6dd *) solve [ inversion Hty; subst; edestruct (extend_store_alloc S (length mu) T) as [S' [Hext Hnth]]; auto; exists S'; repeat split; auto; [econstructor; eauto using store_weakening, heap_ok_extends | apply T_Loc; auto] ]. }
  { (* S_Deref:8439942b *) solve [ inversion Hty; subst; edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto; exists S'; repeat split; auto; econstructor; eauto using store_weakening ]. }
  { (* S_DerefLoc:549a6cb8 *) inversion Hty; subst; inversion H3; subst; edestruct (heap_lookup_has_type mu S l v) as [T' [Hnth' Hty']]; eauto; assert (T' = T0) by congruence; subst; exists S; repeat split; auto using extends_refl.
  }
  { (* S_Assign1:7a5350ba *) solve [ inversion Hty; subst; edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto; exists S'; repeat split; auto; econstructor; eauto using store_weakening ]. }
  { (* S_Assign2:c1f44dd6 *) solve [ inversion Hty; subst; edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto; exists S'; repeat split; auto; econstructor; eauto using store_weakening ]. }
  { (* S_AssignV:5d6e6ba5 *) inversion Hty; subst; inversion H4; subst; exists S; repeat split; auto using extends_refl; [eapply heap_update_ok; eauto | constructor].
  }
Qed.
