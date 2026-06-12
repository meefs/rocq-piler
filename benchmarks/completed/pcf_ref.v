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

Lemma extends_refl : forall ST : store_ty, extends ST ST.
Proof.
intro ST. unfold extends. exists []. apply app_nil_end_deprecated.
Qed.

Lemma extends_nth_error : forall (ST' ST : store_ty) l T, extends ST' ST -> nth_error ST l = Some T -> nth_error ST' l = Some T.
Proof.
intros ST' ST l T Hext Hnth. unfold extends in Hext. destruct Hext as [S2 ->]. rewrite nth_error_app. case_eq (l <? length ST); intros Hcmp; rewrite Hnth; auto.
assert (Hlt : l <? length ST = true). { apply Nat.ltb_lt. apply nth_error_Some. rewrite Hnth. discriminate. } rewrite Hlt. exact Hnth.
Qed.

Lemma has_type_extends : forall G ST t T, has_type G ST t T -> forall ST', extends ST' ST -> has_type G ST' t T.
Proof.
induction 1; intros ST' Hext; try solve [constructor; eauto].
all: econstructor; eauto; eapply extends_nth_error; eauto.
Qed.

Lemma heap_ok_extends : forall mu ST, heap_ok mu ST -> forall ST', extends ST' ST -> heap_ok mu ST'.
Proof.
induction 1; intros ST' Hext. { constructor. } { econstructor; eauto using has_type_extends, extends_nth_error. }.
Qed.


Lemma nth_error_shift_var : forall (G1 G2 : ctx) (U T : ty) (x : nat), nth_error (G1 ++ G2) x = Some T -> nth_error (G1 ++ U :: G2) (if x <? length G1 then x else x + 1) = Some T.
Proof.
intros G1 G2 U T x H. case_eq (x <? length G1); intros Hcmp. { apply Nat.ltb_lt in Hcmp. rewrite nth_error_app1; [|exact Hcmp]. rewrite nth_error_app1 in H; [|exact Hcmp]. exact H. } { apply Nat.ltb_nlt in Hcmp. assert (x1 : x + 1 - length G1 = x - length G1 + 1) by lia. rewrite nth_error_app2; [|lia]. rewrite nth_error_app2 in H; [|lia]. replace (x + 1 - length G1) with (S (x - length G1)) by lia. simpl. rewrite H. reflexivity. }.
Qed.

Lemma shift_at_preserves : forall G ST t T, has_type G ST t T -> forall G1 U G2, G = G1 ++ G2 -> has_type (G1 ++ U :: G2) ST (shift_at (length G1) t) T.
Proof.
induction 1; intros G1 U G2 Heq; subst; simpl; repeat (match goal with | H: nth_error (?g1 ++ ?g2) ?x = Some ?T |- has_type (?g1 ++ ?U :: ?g2) _ (if ?x <? length ?g1 then Var ?x else Var (?x + 1)) ?T => case_eq (x <? length g1); intros Hcmp; apply T_Var; [rewrite nth_error_app1; [|apply Nat.ltb_lt; auto] | rewrite nth_error_app2; [|apply Nat.ltb_nlt in Hcmp; lia]]; rewrite nth_error_app in H; rewrite Hcmp in H; assumption | |- has_type _ _ (Lam _ _) _ => constructor; eapply IHhas_type; reflexivity | |- has_type _ _ (Fix _) _ => constructor; eapply IHhas_type; reflexivity | _ => try (constructor; eauto) end).
repeat (match goal with | H: nth_error (?g1 ++ ?g2) ?x = Some ?T |- has_type (?g1 ++ ?U :: ?g2) _ (if ?x <? length ?g1 then Var ?x else Var (?x + 1)) ?T => case_eq (x <? length g1); intros Hcmp; apply T_Var; [rewrite nth_error_app1; [|apply Nat.ltb_lt; exact Hcmp] | rewrite nth_error_app2; [|apply Nat.ltb_nlt in Hcmp; lia]]; rewrite nth_error_app in H; rewrite Hcmp in H; assumption | HT: has_type (?T :: ?G1 ++ ?G2) ?S ?t ?T2 |- has_type (?T :: ?G1 ++ ?U :: ?G2) ?S (shift_at (Datatypes.S (length ?G1)) ?t) ?T2 => apply (IHhas_type (T :: G1) U G2); reflexivity | HT: has_type (?G1 ++ ?G2) ?S ?t1 (TyArrow ?T1 ?T2), HT2: has_type (?G1 ++ ?G2) ?S ?t2 ?T1 |- has_type (?G1 ++ ?U :: ?G2) ?S (App (shift_at (length ?G1) ?t1) (shift_at (length ?G1) ?t2)) ?T2 => econstructor; [apply (IHhas_type1 G1 U G2); reflexivity | apply (IHhas_type2 G1 U G2); reflexivity] | HT: has_type (?G1 ++ ?G2) ?S ?t1 (TyRef ?T), HT2: has_type (?G1 ++ ?G2) ?S ?t2 ?T |- has_type (?G1 ++ ?U :: ?G2) ?S (Assign (shift_at (length ?G1) ?t1) (shift_at (length ?G1) ?t2)) TyNat => econstructor; [apply (IHhas_type1 G1 U G2); reflexivity | apply (IHhas_type2 G1 U G2); reflexivity] end).
- destruct (x <? length G1) eqn:Hcmp.
  - apply T_Var. rewrite nth_error_app1. rewrite nth_error_app in H. rewrite Hcmp in H. exact H. apply Nat.ltb_lt. exact Hcmp.
  - apply Nat.ltb_nlt in Hcmp. apply T_Var. rewrite nth_error_app. assert (x <? length G1 = false) by (apply Nat.ltb_nlt; exact Hcmp). rewrite H0. rewrite nth_error_app2 in H; [|exact Hcmp]. replace (x+1 - length G1) with (S (x - length G1)) by lia. simpl. exact H.
  - apply (IHhas_type (T1 :: G1) U G2). reflexivity.
  - econstructor; [apply (IHhas_type1 G1 U G2 eq_refl) | apply (IHhas_type2 G1 U G2 eq_refl)].
  - apply (IHhas_type (T :: G1) U G2). reflexivity.
  econstructor; [apply (IHhas_type1 G1 U G2 eq_refl) | apply (IHhas_type2 G1 U G2 eq_refl)].
Qed.

Lemma shift_preserves : forall G ST t T U, has_type G ST t T -> has_type (U :: G) ST (shift t) T.
Proof.
intros. unfold shift. apply (shift_at_preserves G ST t T H [] U G). reflexivity.
Qed.
Lemma subst_preserves : forall G' ST t T, has_type G' ST t T -> forall G1 U v, G' = G1 ++ [U] -> has_type G1 ST v U -> has_type G1 ST (subst (length G1) v t) T.
Proof.
induction 1; intros G1 U v Heq Hv; subst; simpl; try solve [constructor; eauto].
* case_eq (x =? length G1); intros Heq. { apply Nat.eqb_eq in Heq. subst. rewrite nth_error_app2 in H; [|reflexivity]. simpl in H. injection H. intro. subst. exact Hv. } { apply Nat.eqb_neq in Heq. apply T_Var. rewrite nth_error_app1 in H; [exact H|]. assert (x < length G1) by (apply nth_error_Some; rewrite H; discriminate). lia. }
* econstructor; [eapply IHhas_type1 with (G0 := G1); [reflexivity|eauto] | eapply IHhas_type2 with (G0 := G1); [reflexivity|eauto]].
* constructor. apply IHhas_type with (G0 := T1 :: G1) (U0 := U) (v0 := shift v). reflexivity. apply shift_preserves. exact Hv.
* econstructor; [eapply IHhas_type1 with (G0 := G1); [reflexivity|eauto] | eapply IHhas_type2 with (G0 := G1); [reflexivity|eauto]].
* constructor. apply IHhas_type with (G0 := T :: G1) (U0 := U) (v0 := shift v). reflexivity. apply shift_preserves. exact Hv.
Qed.

Lemma heap_lookup_type : forall mu ST, heap_ok mu ST -> forall l v T, heap_lookup l mu = Some v -> nth_error ST l = Some T -> has_type [] ST v T.
Proof.
induction 1; simpl; intros l v T Hlook Hnth.
- discriminate.
- destruct (Nat.eqb l l0) eqn:Heq.
  + apply Nat.eqb_eq in Heq. subst. injection Hlook. intro. subst. injection Hnth. intro. subst. exact H0.
  + apply Nat.eqb_neq in Heq. eapply IHheap_ok; eauto.
Qed.

Lemma heap_update_ok : forall mu ST, heap_ok mu ST -> forall l v T, nth_error ST l = Some T -> has_type [] ST v T -> heap_ok (heap_update l v mu) ST.
Proof.
induction 1; simpl; intros l v T Hnth Htype.
- constructor.
- destruct (Nat.eqb l l0) eqn:Heq.
  + apply Nat.eqb_eq in Heq. subst. econstructor; eauto.
  + apply Nat.eqb_neq in Heq. econstructor; eauto.
Qed.

Lemma nth_error_extend : forall (S : store_ty) (T : ty) (k : nat), k >= length S -> nth_error (S ++ repeat TyNat (k - length S) ++ [T]) k = Some T.
Proof.
intros S T k Hk. rewrite nth_error_app2; [|repeat (rewrite app_length || rewrite repeat_length); lia]. replace (k - (length S + (k - length S))) with 0 by lia. simpl. reflexivity.
rewrite nth_error_app2; [|rewrite repeat_length; lia]. replace (k - length S - length (repeat TyNat (k - length S))) with 0 by (rewrite repeat_length; lia). simpl. reflexivity.
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
  intros t mu t' mu' T S Htype Hstep Hok Hlen.
  induction Hstep; intros T Htype Hok Hlen; match goal with
  | H: has_type [] ?S (Succ ?t') TyNat |- _ => inversion H as [| | | | | | | | | | | |? Q]; subst H; clear H; destruct (IHHstep Q Hok Hlen) as [S' [Hext [Hok' Hty']]]; exists S'; split; [exact Hext|split;[exact Hok'|constructor; exact Hty']]
  | H: has_type [] ?S (Pred (Num 0)) ?T |- _ => inversion H; subst; exists S; split;[apply extends_refl|split;[assumption|constructor]]
  | H: has_type [] ?S (Pred (Num (S ?n))) ?T |- _ => inversion H; subst; exists S; split;[apply extends_refl|split;[assumption|constructor]]
  | H: has_type [] ?S (Pred ?t') TyNat |- _ => inversion H as [| | | | | | | | | | | |? Q]; subst H; clear H; destruct (IHHstep Q Hok Hlen) as [S' [Hext [Hok' Hty']]]; exists S'; split; [exact Hext|split;[exact Hok'|constructor; exact Hty']]
  | H: has_type [] ?S (IsZero (Num 0)) ?T |- _ => inversion H; subst; exists S; split;[apply extends_refl|split;[assumption|constructor]]
  | H: has_type [] ?S (IsZero (Num (S ?n))) ?T |- _ => inversion H; subst; exists S; split;[apply extends_refl|split;[assumption|constructor]]
  | H: has_type [] ?S (IsZero ?t') TyBool |- _ => inversion H as [| | | | | | | | | | | |? Q]; subst H; clear H; destruct (IHHstep Q Hok Hlen) as [S' [Hext [Hok' Hty']]]; exists S'; split; [exact Hext|split;[exact Hok'|constructor; exact Hty']]
  | H: has_type [] ?S (If (BOOL true) ?t1 ?t2) ?T |- _ => inversion H; subst; exists S; split;[apply extends_refl|split;[assumption|assumption]]
  | H: has_type [] ?S (If (BOOL false) ?t1 ?t2) ?T |- _ => inversion H; subst; exists S; split;[apply extends_refl|split;[assumption|assumption]]
  | H: has_type [] ?S (If ?t1 ?t2 ?t3) ?T |- _ => inversion H as [| | | | | | |? ? ? ? ? Q1 Q2 Q3| | | | | |]; subst H; clear H; destruct (IHHstep Q1 Hok Hlen) as [S' [Hext [Hok' Hty']]]; exists S'; split; [exact Hext|split;[exact Hok'|econstructor; [exact Hty'|apply has_type_extends with (ST := S); [exact Q2|exact Hext]|apply has_type_extends with (ST := S); [exact Q3|exact Hext]]]]
  | H: has_type [] ?S (App ?t1 ?t2) ?T |- _ => inversion H as [| | | | | | | |? ? ? ? ? Q1 Q2| | | | | |]; subst H; clear H; destruct (IHHstep Q1 Hok Hlen) as [S' [Hext [Hok' Hty']]]; exists S'; split; [exact Hext|split;[exact Hok'|econstructor; [exact Hty'|apply has_type_extends with (ST := S); [exact Q2|exact Hext]]]]
  | H: has_type [] ?S (App (Lam ?T1 ?t1) ?v2) ?T |- _ => inversion H as [| | | | | | | |? ? T2 ? ? Q1 Q2| | | | | |]; subst H; clear H; inversion Q1; subst; exists S; split;[apply extends_refl|split;[assumption|apply subst_preserves with (v := v2) (G' := [T1]) (U := T1) (G1 := []); [exact H3|reflexivity|constructor; exact Q2]]]
  | H: has_type [] ?S (Fix ?t') ?T |- _ => inversion H as [| | | | | | | | |? ? Q| | | |]; subst H; clear H; inversion Q; subst; exists S; split;[apply extends_refl|split;[assumption|apply subst_preserves with (v := Fix t') (G' := [T0]) (U := T0) (G1 := []); [exact H2|reflexivity|constructor; exact H2]]]
  | H: has_type [] ?S (Ref ?t') ?T |- _ => inversion H as [| | | | | | | | | |? ? Q| | |]; subst H; clear H; destruct (IHHstep Q Hok Hlen) as [S' [Hext [Hok' Hty']]]; exists S'; split; [exact Hext|split;[exact Hok'|constructor; exact Hty']]
  | H: has_type [] ?S (Ref ?v) ?T |- _ => inversion H as [| | | | | | | | | |? ? Q| | |]; subst H; clear H; exists (S ++ repeat TyNat (length mu - length S) ++ [T0]); split; [exists (repeat TyNat (length mu - length S) ++ [T0]); reflexivity|split;[econstructor; [apply heap_ok_extends with (ST := S); [exact Hok|exists (repeat TyNat (length mu - length S) ++ [T0]); reflexivity]|apply has_type_extends with (ST := S); [exact Q|exists (repeat TyNat (length mu - length S) ++ [T0]); reflexivity]|apply nth_error_extend; exact Hlen]|constructor; apply nth_error_extend; exact Hlen]]
  | H: has_type [] ?S (Deref ?t') ?T |- _ => inversion H as [| | | | | | | | | | |? ? ? Q| | |]; subst H; clear H; destruct (IHHstep Q Hok Hlen) as [S' [Hext [Hok' Hty']]]; exists S'; split; [exact Hext|split;[exact Hok'|constructor; exact Hty']]
  | H: has_type [] ?S (Deref (Loc ?l)) ?T |- _ => inversion H as [| | | | | | | | | | |? ? ? Q| | |]; subst H; clear H; inversion Q; subst; exists S; split;[apply extends_refl|split;[assumption|eapply heap_lookup_type; eauto]]
  | H: has_type [] ?S (Assign ?t1 ?t2) ?T |- _ => inversion H as [| | | | | | | | | | | |? ? ? ? Q1 Q2| |]; subst H; clear H; destruct (IHHstep Q1 Hok Hlen) as [S' [Hext [Hok' Hty']]]; exists S'; split; [exact Hext|split;[exact Hok'|econstructor; [exact Hty'|apply has_type_extends with (ST := S); [exact Q2|exact Hext]]]]
  | H: has_type [] ?S (Assign (Loc ?l) ?v) ?T |- _ => inversion H as [| | | | | | | | | | | |? ? ? ? Q1 Q2| |]; subst H; clear H; inversion Q1; subst; exists S; split;[apply extends_refl|split;[apply heap_update_ok; eauto|constructor; constructor]]
  | _ => idtac
  end.
Qed.
