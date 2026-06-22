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


Lemma shift_ty_gen : forall t G1 G2 St T, has_type (G1 ++ G2) St t T -> forall U, has_type (G1 ++ U :: G2) St (shift_at (length G1) t) T.
Proof.
  induction t; intros G1 G2 St T Hty U; simpl; inversion Hty; subst.
  { (* case_1:0d503a21 *) destruct (Nat.ltb_spec n (length G1)) as [Hlt|Hge]; apply T_Var; match goal with H : nth_error (G1 ++ G2) _ = Some _ |- _ => first [ rewrite nth_error_app1 in H by lia; rewrite nth_error_app1 by lia; exact H | rewrite nth_error_app2 in H by lia; rewrite nth_error_app2 by lia; replace (n + 1 - length G1) with (S (n - length G1)) by lia; exact H ] end.
  }
  { (* case_2:0ab6d365 *) solve [ econstructor; eauto ]. }
  { (* case_3:8a0125f7 *) solve [ econstructor; eauto ]. }
  { (* case_4:7d9ce3c3 *) solve [ econstructor; eauto ]. }
  { (* case_5:9f223340 *) solve [ econstructor; eauto ]. }
  { (* case_6:a8f35958 *) solve [ econstructor; eauto ]. }
  { (* case_7:bc174322 *) solve [ econstructor; eauto ]. }
  { (* case_8:83ff7d8c *) apply T_Lam; apply (IHt (t :: G1) G2 St T2); assumption.
  }
  { (* case_9:90f10f75 *) solve [ econstructor; eauto ]. }
  { (* case_10:204002e9 *) apply T_Fix; apply (IHt (T :: G1) G2 St T); assumption.
  }
  { (* case_11:f75f84a8 *) solve [ econstructor; eauto ]. }
  { (* case_12:721410d2 *) solve [ econstructor; eauto ]. }
  { (* case_13:05f48fe3 *) solve [ econstructor; eauto ]. }
  { (* case_14:3a33972f *) solve [ econstructor; eauto ]. }
Qed.


Lemma shift_ty : forall t G St T U, has_type G St t T -> has_type (U :: G) St (shift t) T.
Proof.
intros t G St T U H; unfold shift; exact (shift_ty_gen t nil G St T H U).
Qed.


Lemma store_weakening : forall G St t T, has_type G St t T -> forall St', extends St' St -> has_type G St' t T.
Proof.
  intros G St t T H; induction H; intros St' Hext.
  { (* case_1:c1f12aa1 *) solve [ econstructor; eauto ]. }
  { (* case_2:6cb67c9b *) solve [ econstructor; eauto ]. }
  { (* case_3:27b8df69 *) solve [ econstructor; eauto ]. }
  { (* case_4:ff5e0df6 *) solve [ econstructor; eauto ]. }
  { (* case_5:7bed37a9 *) solve [ econstructor; eauto ]. }
  { (* case_6:c36eabae *) solve [ econstructor; eauto ]. }
  { (* case_7:b8fa3a7a *) solve [ econstructor; eauto ]. }
  { (* case_8:c8b37728 *) solve [ econstructor; eauto ]. }
  { (* case_9:f7f18e6a *) solve [ econstructor; eauto ]. }
  { (* case_10:76a932c9 *) solve [ econstructor; eauto ]. }
  { (* case_11:7b5010be *) solve [ econstructor; eauto ]. }
  { (* case_12:e7d3fbd7 *) solve [ econstructor; eauto ]. }
  { (* case_13:2f9cacba *) solve [ econstructor; eauto ]. }
  { (* case_14:b60e9dd9 *) destruct Hext as [S2 Heq]; subst St'; apply T_Loc; rewrite nth_error_app1 by (apply nth_error_Some; rewrite H; discriminate); exact H.
  }
Qed.


Lemma heap_ok_extends : forall mu St, heap_ok mu St -> forall St', extends St' St -> heap_ok mu St'.
Proof.
  intros mu St H; induction H; intros St' Hext.
  { (* case_1:4742ca27 *) solve [ econstructor; eauto using store_weakening ]. }
  { (* case_2:1985f654 *) eapply heap_cons; [ apply IHheap_ok; exact Hext | apply (store_weakening nil S v T H0 St' Hext) | destruct Hext as [S2 Heq]; subst St'; rewrite nth_error_app1 by (apply nth_error_Some; rewrite H1; discriminate); exact H1 ].
  }
Qed.


Lemma subst_ty : forall t G U T St s, has_type (G ++ [U]) St t T -> has_type G St s U -> has_type G St (subst (length G) s t) T.
Proof.
  induction t; intros G U T St s Hty Hs; simpl; inversion Hty; subst.
  { (* case_1:ff4da908 *) destruct (Nat.eqb_spec n (length G)) as [Heq|Hne]; [ assert (T = U) as ->; [ rewrite Heq in H2; rewrite nth_error_app2 in H2 by lia; replace (length G - length G) with 0 in H2 by lia; simpl in H2; congruence | exact Hs ] | apply T_Var; assert (Hb : n < length (G ++ [U])) by (apply nth_error_Some; rewrite H2; discriminate); rewrite length_app in Hb; simpl in Hb; rewrite nth_error_app1 in H2 by lia; exact H2 ].
  }
  { (* case_2:af3958df *) solve [ econstructor; eauto ]. }
  { (* case_3:5e0d7c5b *) solve [ econstructor; eauto ]. }
  { (* case_4:c0dd90ae *) solve [ econstructor; eauto ]. }
  { (* case_5:9ccf1c5a *) solve [ econstructor; eauto ]. }
  { (* case_6:8d5d938c *) solve [ econstructor; eauto ]. }
  { (* case_7:63b92dbb *) solve [ econstructor; eauto ]. }
  { (* case_8:d02e92ae *) apply T_Lam; apply (IHt (t :: G) U T2 St (shift s)); [ exact H4 | apply (shift_ty s G St U t Hs) ].
  }
  { (* case_9:ee971362 *) solve [ econstructor; eauto ]. }
  { (* case_10:1c08ce67 *) apply T_Fix; apply (IHt (T :: G) U T St (shift s)); [ exact H2 | apply (shift_ty s G St U T Hs) ].
  }
  { (* case_11:8d9e73d4 *) solve [ econstructor; eauto ]. }
  { (* case_12:9a1cde3b *) solve [ econstructor; eauto ]. }
  { (* case_13:8cc9de45 *) solve [ econstructor; eauto ]. }
  { (* case_14:2c5eb784 *) solve [ econstructor; eauto ]. }
Qed.


Lemma heap_lookup_typed : forall mu St, heap_ok mu St -> forall l v T, heap_lookup l mu = Some v -> nth_error St l = Some T -> has_type [] St v T.
Proof.
  intros mu St H; induction H; intros l0 v0 T0 Hlook Hnth; simpl in Hlook.
  { (* case_1:73f3a807 *) solve [ discriminate ]. }
  { (* case_2:73f3a807 *) destruct (Nat.eqb_spec l0 l) as [Heq|Hne]; [ subst l0; injection Hlook as ->; assert (T0 = T) by congruence; subst T0; exact H0 | apply (IHheap_ok l0 v0 T0 Hlook Hnth) ].
  }
Qed.


Lemma heap_update_ok : forall mu St, heap_ok mu St -> forall l v T, nth_error St l = Some T -> has_type [] St v T -> heap_ok (heap_update l v mu) St.
Proof.
  intros mu St H; induction H; intros l0 v0 T0 Hnth Hv; simpl.
  { (* case_1:d23b3754 *) solve [ apply heap_empty ]. }
  { (* case_2:d828bbeb *) destruct (Nat.eqb_spec l0 l) as [Heq|Hne]; [ exact (heap_cons l0 v0 mu S T0 H Hv Hnth) | exact (heap_cons l v (heap_update l0 v0 mu) S T (IHheap_ok l0 v0 T0 Hnth Hv) H0 H1) ].
  }
Qed.


#[local] Hint Constructors has_type : core.

Lemma extends_refl : forall S, extends S S.
Proof. intros S. exists (@nil ty). rewrite app_nil_r. reflexivity. Qed.

#[local] Hint Resolve extends_refl : core.

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
  intros t mu t' mu' T S Hty Hstep Hheap Hlen; generalize dependent S; generalize dependent T; induction Hstep; intros Tg Sg Hty Hheap Hlen.
  { (* S_Succ:cb4627e3 *) solve [ inversion Hty; subst; match goal with Hsub : has_type [] Sg ?u ?Tu |- _ => destruct (IHHstep Tu Sg Hsub Hheap Hlen) as [S2 [Hext [Hho Hty']]]; exists S2; split; [ exact Hext | split; [ exact Hho | econstructor; eauto using store_weakening ] ] end ]. }
  { (* S_PredZero:2f441286 *) solve [ inversion Hty; subst; exists Sg; split; [ apply extends_refl | split; [ exact Hheap | eauto ] ] ]. }
  { (* S_PredSucc:335b9d67 *) solve [ inversion Hty; subst; exists Sg; split; [ apply extends_refl | split; [ exact Hheap | eauto ] ] ]. }
  { (* S_Pred:b700a473 *) solve [ inversion Hty; subst; match goal with Hsub : has_type [] Sg ?u ?Tu |- _ => destruct (IHHstep Tu Sg Hsub Hheap Hlen) as [S2 [Hext [Hho Hty']]]; exists S2; split; [ exact Hext | split; [ exact Hho | econstructor; eauto using store_weakening ] ] end ]. }
  { (* S_IsZeroZero:c005235a *) solve [ inversion Hty; subst; exists Sg; split; [ apply extends_refl | split; [ exact Hheap | eauto ] ] ]. }
  { (* S_IsZeroSucc:ae222842 *) solve [ inversion Hty; subst; exists Sg; split; [ apply extends_refl | split; [ exact Hheap | eauto ] ] ]. }
  { (* S_IsZero:bedb3c33 *) solve [ inversion Hty; subst; match goal with Hsub : has_type [] Sg ?u ?Tu |- _ => destruct (IHHstep Tu Sg Hsub Hheap Hlen) as [S2 [Hext [Hho Hty']]]; exists S2; split; [ exact Hext | split; [ exact Hho | econstructor; eauto using store_weakening ] ] end ]. }
  { (* S_IfTrue:9c65f697 *) solve [ inversion Hty; subst; exists Sg; split; [ apply extends_refl | split; [ exact Hheap | eauto ] ] ]. }
  { (* S_IfFalse:363b7540 *) solve [ inversion Hty; subst; exists Sg; split; [ apply extends_refl | split; [ exact Hheap | eauto ] ] ]. }
  { (* S_If:3868fed9 *) solve [ inversion Hty; subst; match goal with Hsub : has_type [] Sg ?u ?Tu |- _ => destruct (IHHstep Tu Sg Hsub Hheap Hlen) as [S2 [Hext [Hho Hty']]]; exists S2; split; [ exact Hext | split; [ exact Hho | econstructor; eauto using store_weakening ] ] end ]. }
  { (* S_App1:e84e27b8 *) solve [ inversion Hty; subst; match goal with Hsub : has_type [] Sg ?u ?Tu |- _ => destruct (IHHstep Tu Sg Hsub Hheap Hlen) as [S2 [Hext [Hho Hty']]]; exists S2; split; [ exact Hext | split; [ exact Hho | econstructor; eauto using store_weakening ] ] end ]. }
  { (* S_App2:621384ba *) solve [ inversion Hty; subst; match goal with Hsub : has_type [] Sg ?u ?Tu |- _ => destruct (IHHstep Tu Sg Hsub Hheap Hlen) as [S2 [Hext [Hho Hty']]]; exists S2; split; [ exact Hext | split; [ exact Hho | econstructor; eauto using store_weakening ] ] end ]. }
  { (* S_AppAbs:d0de6cca *) inversion Hty; subst; match goal with H1 : has_type [] Sg (Lam _ _) _ |- _ => inversion H1; subst end; exists Sg; split; [ apply extends_refl | split; [ exact Hheap | match goal with Hb : has_type (?A :: []) Sg t1 Tg, Ha : has_type [] Sg v2 ?A |- _ => exact (subst_ty t1 nil A Tg Sg v2 Hb Ha) end ] ].
  }
  { (* S_Fix:466566ea *) inversion Hty; subst; exists Sg; split; [ apply extends_refl | split; [ exact Hheap | match goal with Hb : has_type (?A :: []) Sg t Tg |- _ => exact (subst_ty t nil A Tg Sg (Fix t) Hb Hty) end ] ].
  }
  { (* S_Ref:8bd945c2 *) solve [ inversion Hty; subst; match goal with Hsub : has_type [] Sg ?u ?Tu |- _ => destruct (IHHstep Tu Sg Hsub Hheap Hlen) as [S2 [Hext [Hho Hty']]]; exists S2; split; [ exact Hext | split; [ exact Hho | econstructor; eauto using store_weakening ] ] end ]. }
  { (* S_RefV:18328a29 *) inversion Hty; subst; match goal with Hv : has_type [] Sg v ?T0 |- _ => exists (Sg ++ repeat TyNat (length mu - length Sg) ++ [T0]); assert (Hext : extends (Sg ++ repeat TyNat (length mu - length Sg) ++ [T0]) Sg) by (eexists; reflexivity); assert (Hnth : nth_error (Sg ++ repeat TyNat (length mu - length Sg) ++ [T0]) (length mu) = Some T0) by (rewrite app_assoc; rewrite nth_error_app2 by (rewrite length_app, repeat_length; lia); rewrite length_app, repeat_length; replace (length mu - (length Sg + (length mu - length Sg))) with 0 by lia; reflexivity); split; [ exact Hext | split; [ eapply heap_cons; [ apply (heap_ok_extends mu Sg Hheap _ Hext) | apply (store_weakening nil Sg v T0 Hv _ Hext) | exact Hnth ] | apply T_Loc; exact Hnth ] ] end.
  }
  { (* S_Deref:33b89f27 *) solve [ inversion Hty; subst; match goal with Hsub : has_type [] Sg ?u ?Tu |- _ => destruct (IHHstep Tu Sg Hsub Hheap Hlen) as [S2 [Hext [Hho Hty']]]; exists S2; split; [ exact Hext | split; [ exact Hho | econstructor; eauto using store_weakening ] ] end ]. }
  { (* S_DerefLoc:45d4793f *) inversion Hty; subst; match goal with Hloc : has_type [] Sg (Loc l) (TyRef Tg) |- _ => inversion Hloc; subst end; exists Sg; split; [ apply extends_refl | split; [ exact Hheap | match goal with Hn : nth_error Sg l = Some Tg |- _ => exact (heap_lookup_typed mu Sg Hheap l v Tg H Hn) end ] ].
  }
  { (* S_Assign1:29a16d63 *) solve [ inversion Hty; subst; match goal with Hsub : has_type [] Sg ?u ?Tu |- _ => destruct (IHHstep Tu Sg Hsub Hheap Hlen) as [S2 [Hext [Hho Hty']]]; exists S2; split; [ exact Hext | split; [ exact Hho | econstructor; eauto using store_weakening ] ] end ]. }
  { (* S_Assign2:92235a77 *) solve [ inversion Hty; subst; match goal with Hsub : has_type [] Sg ?u ?Tu |- _ => destruct (IHHstep Tu Sg Hsub Hheap Hlen) as [S2 [Hext [Hho Hty']]]; exists S2; split; [ exact Hext | split; [ exact Hho | econstructor; eauto using store_weakening ] ] end ]. }
  { (* S_AssignV:e9df67fa *) inversion Hty; subst; match goal with Hloc : has_type [] Sg (Loc l) (TyRef _) |- _ => inversion Hloc; subst end; exists Sg; split; [ apply extends_refl | split; [ match goal with Hn : nth_error Sg l = Some ?T0, Hv : has_type [] Sg v ?T0 |- _ => exact (heap_update_ok mu Sg Hheap l v T0 Hn Hv) end | apply T_Num ] ].
  }
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
