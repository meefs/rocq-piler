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


Lemma extends_refl : forall S, extends S S.
Proof.
intro S; exists []; rewrite app_nil_r; auto.
Qed.


Lemma extends_app : forall S S2, extends (S ++ S2) S.
Proof.
intros S S2; unfold extends; exists S2; auto.
Qed.


Lemma nth_error_extends : forall S S' l T, extends S' S -> nth_error S l = Some T -> nth_error S' l = Some T.
Proof.
intros S S' l T [S2 ->] H. rewrite nth_error_app1. exact H. apply nth_error_Some. congruence.
Qed.


Lemma has_type_store_extends : forall G S S' t T, has_type G S t T -> extends S' S -> has_type G S' t T.
Proof.
  intros G S S' t T Ht Hext; induction Ht.
  { (* case_1:a1cadb49 *) solve [ econstructor; eauto ]. }
  { (* case_2:871cb7c2 *) solve [ econstructor; eauto ]. }
  { (* case_3:921183ee *) solve [ econstructor; eauto ]. }
  { (* case_4:7f27afdd *) solve [ econstructor; eauto ]. }
  { (* case_5:1a40eb0b *) solve [ econstructor; eauto ]. }
  { (* case_6:78ab5f42 *) solve [ econstructor; eauto ]. }
  { (* case_7:f4b71eb2 *) solve [ econstructor; eauto ]. }
  { (* case_8:3f3c1d84 *) solve [ econstructor; eauto ]. }
  { (* case_9:d80368b3 *) solve [ econstructor; eauto ]. }
  { (* case_10:3ce7dd06 *) solve [ econstructor; eauto ]. }
  { (* case_11:b5eb6186 *) solve [ econstructor; eauto ]. }
  { (* case_12:771867f5 *) solve [ econstructor; eauto ]. }
  { (* case_13:71f786e4 *) solve [ econstructor; eauto ]. }
  { (* case_14:bb66202e *) solve [ constructor; eauto using nth_error_extends ]. }
Qed.


Lemma nth_error_insert : forall {A : Type} (G : list A) (d x : nat) (T U : A), nth_error G x = Some T -> nth_error (firstn d G ++ [U] ++ skipn d G) (if x <? d then x else x + 1) = Some T.
Proof.
intros A G. induction G as [|h t IH]; intros d x T U H. - destruct x; simpl in H; discriminate. - destruct d as [|d']. + simpl. destruct x as [|x']; simpl in *. rewrite H; reflexivity. exact H. + destruct x as [|x']; simpl in *. * rewrite H; reflexivity. * specialize (IH d' x' T U H). simpl in IH. assert (Heq : (S x' <? S d') = (x' <? d')) by (unfold Nat.ltb; simpl; reflexivity). rewrite Heq. destruct (x' <? d'); simpl; exact IH.
Qed.


Lemma shift_at_typing : forall G S t T d U, has_type G S t T -> has_type (firstn d G ++ [U] ++ skipn d G) S (shift_at d t) T.
Proof.
  intros G S t T d U Ht; revert d; induction Ht; intro d; simpl.
  { (* case_1:8189ea8a *) destruct (x <? d) eqn:Hlt; apply T_Var; pose proof (nth_error_insert G d x T U H) as Hni; rewrite Hlt in Hni; exact Hni.
  }
  { (* case_2:5af362bb *) solve [ econstructor; eauto ]. }
  { (* case_3:26d06287 *) solve [ econstructor; eauto ]. }
  { (* case_4:f2bf332b *) solve [ econstructor; eauto ]. }
  { (* case_5:c34fff31 *) solve [ econstructor; eauto ]. }
  { (* case_6:169198bd *) solve [ econstructor; eauto ]. }
  { (* case_7:45b03ee7 *) solve [ econstructor; eauto ]. }
  { (* case_8:f41fb15d *) specialize (IHHt (Datatypes.S d)). simpl in IHHt. apply T_Lam. exact IHHt.
  }
  { (* case_9:0e9538da *) solve [ econstructor; eauto ]. }
  { (* case_10:7a3d804b *) specialize (IHHt (Datatypes.S d)). simpl in IHHt. apply T_Fix. exact IHHt.
  }
  { (* case_11:c1086739 *) solve [ econstructor; eauto ]. }
  { (* case_12:a5e33412 *) solve [ econstructor; eauto ]. }
  { (* case_13:f3144987 *) solve [ econstructor; eauto ]. }
  { (* case_14:691a84d0 *) solve [ econstructor; eauto ]. }
Qed.


Lemma shift_typing : forall G S t T U, has_type G S t T -> has_type (U :: G) S (shift t) T.
Proof.
intros G Sc t T U Ht. unfold shift. apply (shift_at_typing G Sc t T 0 U Ht).
Qed.


Lemma subst_typing : forall G1 Sc t T1 T2 s, has_type (G1 ++ [T1]) Sc t T2 -> has_type G1 Sc s T1 -> has_type G1 Sc (subst (length G1) s t) T2.
Proof.
  intros G1 Sc t; revert G1 Sc; induction t; intros G1 Sc T1 T2 s Ht Hs; simpl; inversion Ht; subst.
  { (* case_1:890b998f *) destruct (Nat.compare n (length G1)) eqn:Hcmp; [apply Nat.compare_eq in Hcmp|apply Nat.compare_lt_iff in Hcmp|apply Nat.compare_gt_iff in Hcmp]. + subst n. rewrite Nat.eqb_refl. rewrite nth_error_app2 in H2 by auto. rewrite Nat.sub_diag in H2. simpl in H2. injection H2; intro; subst T2. exact Hs. + assert (n <> length G1) as Hne by lia. rewrite (proj2 (Nat.eqb_neq n (length G1)) Hne). apply T_Var. rewrite nth_error_app1 in H2 by auto. exact H2. + exfalso. rewrite nth_error_app2 in H2 by lia. destruct (n - length G1) as [|k] eqn:Hk. lia. simpl in H2. destruct k; simpl in H2; discriminate.
  }
  { (* case_2:e1713d7c *) solve [ econstructor; eauto ]. }
  { (* case_3:1c1d7246 *) solve [ econstructor; eauto ]. }
  { (* case_4:1fdafba7 *) solve [ econstructor; eauto ]. }
  { (* case_5:0ae6f580 *) solve [ econstructor; eauto ]. }
  { (* case_6:c15f75ec *) solve [ econstructor; eauto ]. }
  { (* case_7:9a3cfa7b *) solve [ econstructor; eauto ]. }
  { (* case_8:217a759e *) solve [ apply T_Lam; apply IHt with T1; [simpl; exact H4 | apply shift_typing; exact Hs] ]. }
  { (* case_9:5f0e2edb *) solve [ econstructor; eauto ]. }
  { (* case_10:fd9e4ec4 *) apply T_Fix. apply (IHt (T2 :: G1) Sc T1 T2 (shift s)). simpl. exact H2. apply shift_typing. exact Hs.
  }
  { (* case_11:2fa44f7b *) solve [ econstructor; eauto ]. }
  { (* case_12:f6452af1 *) solve [ econstructor; eauto ]. }
  { (* case_13:28b7edd7 *) solve [ econstructor; eauto ]. }
  { (* case_14:067966c3 *) solve [ econstructor; eauto ]. }
Qed.


Lemma heap_lookup_typed : forall mu S l v, heap_ok mu S -> heap_lookup l mu = Some v -> exists T, nth_error S l = Some T /\ has_type [] S v T.
Proof.
  intros mu S l v Hok Hlook; induction Hok; simpl in Hlook.
  { (* case_1:f92870ab *) discriminate Hlook.
  }
  { (* case_2:94096376 *) destruct (Nat.eqb l l0) eqn:Heq. injection Hlook; intro; subst v. apply Nat.eqb_eq in Heq. subst l0. exists T. split. exact H0. exact H. apply IHHok. exact Hlook.
  }
Qed.


Lemma heap_update_ok : forall mu S l v T, heap_ok mu S -> nth_error S l = Some T -> has_type [] S v T -> heap_ok (heap_update l v mu) S.
Proof.
  intros mu S l v T Hok Hn Hv; induction Hok; simpl.
  { (* case_1:d23b3754 *) solve [ econstructor; eauto ]. }
  { (* case_2:3c0b7a8e *) solve [ destruct (Nat.eqb l l0); econstructor; eauto ]. }
Qed.


Lemma nth_error_app_end : forall {A : Type} (l : list A) (x : A), nth_error (l ++ [x]) (length l) = Some x.
Proof.
intros A l x. rewrite nth_error_app2 by auto. rewrite Nat.sub_diag. reflexivity.
Qed.


Lemma heap_cons_ok : forall mu Sc Sc' v T, heap_ok mu Sc -> extends Sc' Sc -> has_type [] Sc' v T -> nth_error Sc' (length mu) = Some T -> heap_ok ((length mu, v) :: mu) Sc'.
Proof.
  intros mu Sc Sc' v T Hok Hext Hv Hn; apply heap_cons with T; [|exact Hv|exact Hn]; clear Hn Hv; induction Hok.
  { (* case_1:b916af3a *) solve [ apply heap_empty ]. }
  { (* case_2:7e6b5c79 *) solve [ apply heap_cons with T0; [eauto|eauto using has_type_store_extends|eauto using nth_error_extends] ]. }
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
  intros t mu t' mu' Ty Sc Ht Hstep Hok Hlen; revert Ty Sc Ht Hok Hlen; induction Hstep; intros Ty Sc Ht Hok Hlen; inversion Ht; subst.
  { (* case_1:bc6944e4 *) destruct (IHHstep TyNat Sc H2 Hok Hlen) as [S' [Hext [Hok' Ht']]]. exists S'. split. exact Hext. split. exact Hok'. apply T_Succ. exact Ht'.
  }
  { (* case_2:4e2abff0 *) solve [ exists Sc; split; [apply extends_refl | split; [exact Hok | econstructor; eauto]] ]. }
  { (* case_3:7c03e22e *) solve [ exists Sc; split; [apply extends_refl | split; [exact Hok | econstructor; eauto]] ]. }
  { (* case_4:8b8f0c8b *) destruct (IHHstep TyNat Sc H2 Hok Hlen) as [S' [Hext [Hok' Ht']]]. exists S'. split. exact Hext. split. exact Hok'. apply T_Pred. exact Ht'.
  }
  { (* case_5:f26294cb *) solve [ exists Sc; split; [apply extends_refl | split; [exact Hok | econstructor; eauto]] ]. }
  { (* case_6:53442ae9 *) solve [ exists Sc; split; [apply extends_refl | split; [exact Hok | econstructor; eauto]] ]. }
  { (* case_7:d1ee94c3 *) destruct (IHHstep TyNat Sc H2 Hok Hlen) as [S' [Hext [Hok' Ht']]]. exists S'. split. exact Hext. split. exact Hok'. apply T_IsZero. exact Ht'.
  }
  { (* case_8:04372467 *) solve [ eexists; split; [apply extends_refl | split; [exact Hok | eauto]] ]. }
  { (* case_9:d4d0856e *) solve [ eexists; split; [apply extends_refl | split; [exact Hok | eauto]] ]. }
  { (* case_10:5ac4adc4 *) destruct (IHHstep TyBool Sc H4 Hok Hlen) as [S' [Hext [Hok' Ht1']]]. exists S'. split. exact Hext. split. exact Hok'. apply T_If. exact Ht1'. exact (has_type_store_extends [] Sc S' t2 Ty H6 Hext). exact (has_type_store_extends [] Sc S' t3 Ty H7 Hext).
  }
  { (* case_11:5ade8952 *) destruct (IHHstep (TyArrow T1 Ty) Sc H3 Hok Hlen) as [S' [Hext [Hok' Ht1']]]. exists S'. split. exact Hext. split. exact Hok'. apply T_App with T1. exact Ht1'. exact (has_type_store_extends [] Sc S' t2 T1 H5 Hext).
  }
  { (* case_12:01815ed8 *) destruct (IHHstep T1 Sc H6 Hok Hlen) as [S' [Hext [Hok' Ht2']]]. exists S'. split. exact Hext. split. exact Hok'. apply T_App with T1. exact (has_type_store_extends [] Sc S' v1 (TyArrow T1 Ty) H4 Hext). exact Ht2'.
  }
  { (* case_13:927a7471 *) exists Sc. split. apply extends_refl. split. exact Hok. inversion H4; subst. apply (subst_typing [] Sc t1 T1 Ty v2); assumption.
  }
  { (* case_14:a1109f0f *) exists Sc. split. apply extends_refl. split. exact Hok. apply (subst_typing [] Sc t Ty Ty (Fix t) H2 Ht).
  }
  { (* case_15:8c768031 *) destruct (IHHstep T Sc H2 Hok Hlen) as [S' [Hext [Hok' Ht']]]. exists S'. split. exact Hext. split. exact Hok'. apply T_Ref. exact Ht'.
  }
  { (* case_16:a96a66a0 *) pose (k := length mu - length Sc). pose (S' := Sc ++ repeat TyNat k ++ [T]). assert (Hext' : extends S' Sc). { unfold S'; unfold extends; exists (repeat TyNat k ++ [T]); reflexivity. } assert (Hvt' : has_type [] S' v T). { apply has_type_store_extends with Sc. exact H3. exact Hext'. } assert (Hn' : nth_error S' (length mu) = Some T). { unfold S'; rewrite app_assoc; rewrite nth_error_app2; [rewrite app_length; rewrite repeat_length; replace (length mu - (length Sc + k)) with 0 by (unfold k; lia); reflexivity| rewrite app_length; rewrite repeat_length; unfold k; lia]. } exists S'; split; [exact Hext'|split; [exact (heap_cons_ok mu Sc S' v T Hok Hext' Hvt' Hn')|exact (T_Loc [] S' (length mu) T Hn')]].
  }
  { (* case_17:c3c27fbe *) destruct (IHHstep (TyRef Ty) Sc H2 Hok Hlen) as [S' [Hext [Hok' Ht']]]. exists S'. split. exact Hext. split. exact Hok'. apply T_Deref. exact Ht'.
  }
  { (* case_18:97c39c34 *) exists Sc. split. apply extends_refl. split. exact Hok. inversion H3; subst. destruct (heap_lookup_typed mu Sc l v Hok H) as [T' [Hn' Hv]]. rewrite Hn' in H5. injection H5; intro; subst T'. exact Hv.
  }
  { (* case_19:b50dd8f6 *) destruct (IHHstep (TyRef T) Sc H3 Hok Hlen) as [S' [Hext [Hok' Ht1']]]. exists S'. split. exact Hext. split. exact Hok'. apply T_Assign with T. exact Ht1'. exact (has_type_store_extends [] Sc S' t2 T H5 Hext).
  }
  { (* case_20:c50717ad *) destruct (IHHstep T Sc H5 Hok Hlen) as [S' [Hext [Hok' Ht2']]]. exists S'. split. exact Hext. split. exact Hok'. apply T_Assign with T. exact (has_type_store_extends [] Sc S' (Loc l) (TyRef T) H3 Hext). exact Ht2'.
  }
  { (* case_21:0362d92d *) exists Sc. split. apply extends_refl. split. inversion H4. subst. rename H5 into Hn. apply heap_update_ok with T. exact Hok. exact Hn. exact H6. apply T_Num.
  }
Qed.
