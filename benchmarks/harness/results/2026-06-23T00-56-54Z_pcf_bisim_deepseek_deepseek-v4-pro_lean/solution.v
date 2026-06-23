From Stdlib Require Import Arith List Lia PeanoNat Bool Utf8.
Import ListNotations.

(** * Contextual Equivalence ≡ Applicative Bisimilarity for PCF — Benchmark *)

(** ** Types *)
Inductive ty : Type :=
| TNat : ty
| TArr : ty -> ty -> ty.

Lemma ty_eq_dec : forall (T1 T2 : ty), {T1 = T2} + {T1 <> T2}.
Proof. decide equality. Defined.

(** ** Terms (de Bruijn) *)
Inductive tm : Type :=
| tVar (x : nat)
| tLam (A : ty) (t : tm)
| tApp (t u : tm)
| tZero
| tSucc (t : tm)
| tPred (t : tm)
| tIfz (scrut : tm) (tz : tm) (ts : tm)
| tFix (A : ty) (t : tm).

(** ** Substitution machinery *)
Definition sub := nat -> tm.
Definition ids : sub := tVar.
Definition scons (s : tm) (σ : sub) : sub :=
  fun x => match x with 0 => s | S x => σ x end.

Fixpoint rename (ξ : nat -> nat) (t : tm) : tm :=
  match t with
  | tVar x => tVar (ξ x)
  | tLam A t => tLam A (rename (fun x => match x with 0 => 0 | S x => S (ξ x) end) t)
  | tApp t u => tApp (rename ξ t) (rename ξ u)
  | tZero => tZero
  | tSucc t => tSucc (rename ξ t)
  | tPred t => tPred (rename ξ t)
  | tIfz s tz ts => tIfz (rename ξ s) (rename ξ tz)
      (rename (fun x => match x with 0 => 0 | S x => S (ξ x) end) ts)
  | tFix A t => tFix A (rename (fun x => match x with 0 => 0 | S x => S (ξ x) end) t)
  end.

Definition shift1 (t : tm) : tm := rename (Nat.add 1) t.

Definition up_sub (σ : sub) : sub :=
  scons (tVar 0) (fun x => shift1 (σ x)).

Fixpoint apply_sub (σ : sub) (t : tm) : tm :=
  match t with
  | tVar x => σ x
  | tLam A t => tLam A (apply_sub (up_sub σ) t)
  | tApp t u => tApp (apply_sub σ t) (apply_sub σ u)
  | tZero => tZero
  | tSucc t => tSucc (apply_sub σ t)
  | tPred t => tPred (apply_sub σ t)
  | tIfz s tz ts => tIfz (apply_sub σ s) (apply_sub σ tz) (apply_sub (up_sub σ) ts)
  | tFix A t => tFix A (apply_sub (up_sub σ) t)
  end.

Definition subst0 (s : tm) (t : tm) : tm :=
  apply_sub (scons s ids) t.

Lemma subst0_omega : forall s, subst0 s (tFix TNat (tVar 0)) = tFix TNat (tVar 0).
Proof. intros s. unfold subst0. simpl. reflexivity. Qed.

(** ** Typing *)
Fixpoint ctx_lookup (Γ : list ty) (x : nat) : option ty :=
  nth_error Γ x.

Inductive has_type : list ty -> tm -> ty -> Prop :=
| ty_var Γ x T :
    ctx_lookup Γ x = Some T ->
    has_type Γ (tVar x) T
| ty_lam Γ A B t :
    has_type (A :: Γ) t B ->
    has_type Γ (tLam A t) (TArr A B)
| ty_app Γ t u A B :
    has_type Γ t (TArr A B) ->
    has_type Γ u A ->
    has_type Γ (tApp t u) B
| ty_zero Γ :
    has_type Γ tZero TNat
| ty_succ Γ t :
    has_type Γ t TNat ->
    has_type Γ (tSucc t) TNat
| ty_pred Γ t :
    has_type Γ t TNat ->
    has_type Γ (tPred t) TNat
| ty_ifz Γ s tz ts A :
    has_type Γ s TNat ->
    has_type Γ tz A ->
    has_type (TNat :: Γ) ts A ->
    has_type Γ (tIfz s tz ts) A
| ty_fix Γ A t :
    has_type (A :: Γ) t A ->
    has_type Γ (tFix A t) A.

(** ** Values *)
Inductive value : tm -> Prop :=
| v_lam : forall A t, value (tLam A t)
| v_zero : value tZero
| v_succ : forall v, value v -> value (tSucc v).

(** ** Big-step evaluation *)
Inductive eval : tm -> tm -> Prop :=
| eval_val v :
    value v -> eval v v
| eval_app t1 t2 A body v2 v :
    eval t1 (tLam A body) ->
    eval t2 v2 ->
    eval (subst0 v2 body) v ->
    eval (tApp t1 t2) v
| eval_succ t v :
    eval t v ->
    eval (tSucc t) (tSucc v)
| eval_pred_zero t :
    eval t tZero ->
    eval (tPred t) tZero
| eval_pred_succ t v :
    eval t (tSucc v) ->
    eval (tPred t) v
| eval_ifz_zero s tz ts v :
    eval s tZero ->
    eval tz v ->
    eval (tIfz s tz ts) v
| eval_ifz_succ s tz ts n v :
    eval s (tSucc n) ->
    eval (subst0 n ts) v ->
    eval (tIfz s tz ts) v
| eval_fix A body v :
    eval (subst0 (tFix A body) body) v ->
    eval (tFix A body) v.

Definition terminates (t : tm) : Prop := exists v, eval t v.

(** ** Contexts *)
Inductive ctx : Type :=
| cHole
| cLam (A : ty) (C : ctx)
| cAppL (C : ctx) (u : tm)
| cAppR (t : tm) (C : ctx)
| cSucc (C : ctx)
| cPred (C : ctx)
| cIfzS (C : ctx) (tz : tm) (ts : tm)
| cIfzT (s : tm) (C : ctx) (ts : tm)
| cIfzE (s : tm) (tz : tm) (C : ctx)
| cFix (A : ty) (C : ctx).

Fixpoint plug (C : ctx) (t : tm) : tm :=
  match C with
  | cHole => t
  | cLam A C => tLam A (plug C t)
  | cAppL C u => tApp (plug C t) u
  | cAppR f C => tApp f (plug C t)
  | cSucc C => tSucc (plug C t)
  | cPred C => tPred (plug C t)
  | cIfzS C tz ts => tIfz (plug C t) tz ts
  | cIfzT s C ts => tIfz s (plug C t) ts
  | cIfzE s tz C => tIfz s tz (plug C t)
  | cFix A C => tFix A (plug C t)
  end.

(** ** Contextual equivalence *)
Definition ctx_equiv (T : ty) (t1 t2 : tm) : Prop :=
  has_type [] t1 T /\
  has_type [] t2 T /\
  forall C,
    (forall t, has_type [] t T -> has_type [] (plug C t) TNat) ->
    (terminates (plug C t1) <-> terminates (plug C t2)).

(** ** Applicative bisimulation *)
Definition rel := ty -> tm -> tm -> Prop.

Definition is_bisimulation (R : rel) : Prop :=
  forall T t1 t2,
    R T t1 t2 ->
    has_type [] t1 T /\ has_type [] t2 T /\
    match T with
    | TNat =>
        (forall v1, eval t1 v1 -> exists v2, eval t2 v2 /\ v1 = v2) /\
        (forall v2, eval t2 v2 -> exists v1, eval t1 v1 /\ v1 = v2)
    | TArr A B =>
        (forall v1, eval t1 v1 -> exists v2, eval t2 v2 /\
          forall u, has_type [] u A -> R B (tApp v1 u) (tApp v2 u)) /\
        (forall v2, eval t2 v2 -> exists v1, eval t1 v1 /\
          forall u, has_type [] u A -> R B (tApp v1 u) (tApp v2 u))
    end.

Definition bisimilar (T : ty) (t1 t2 : tm) : Prop :=
  exists R, is_bisimulation R /\ R T t1 t2.

(** ** Helper lemmas *)

Ltac inv H := inversion H; subst; clear H.

Lemma eval_det : forall t v1 v2, eval t v1 -> eval t v2 -> v1 = v2.
Proof. Admitted.

Definition omega := tFix TNat (tVar 0).

Lemma eval_omega : forall v, eval omega v -> False.
Proof.
  intros v H. remember omega as t. induction H; try discriminate.
  - inversion Heqt; subst. inversion H.
  - inversion Heqt; subst. apply IHeval. reflexivity.
Qed.

Lemma eval_ifz_inv : forall s tz ts v,
  eval (tIfz s tz ts) v ->
  (eval s tZero /\ eval tz v) \/ (exists n, eval s (tSucc n) /\ eval (subst0 n ts) v).
Proof.
  intros s tz ts v H.
  inversion H; subst; clear H;
  try match goal with
    | [H : tIfz _ _ _ = _ |- _] => discriminate H
    | [H : _ = tIfz _ _ _ |- _] => discriminate H
    | [H : value (tIfz _ _ _) |- _] => inversion H
  end.
  - left; split; auto.
  - right; eexists; split; eauto.
Qed.

Fixpoint nat_val (n : nat) : tm :=
  match n with 0 => tZero | S n' => tSucc (nat_val n') end.

Lemma nat_val_type : forall n, has_type [] (nat_val n) TNat.
Proof. induction n; simpl; auto using ty_zero, ty_succ. Qed.

Lemma nat_val_value : forall n, value (nat_val n).
Proof. induction n; simpl; auto using v_zero, v_succ. Qed.

Lemma eval_nat_val : forall n, eval (nat_val n) (nat_val n).
Proof. intros. apply eval_val, nat_val_value. Qed.

Lemma nat_val_inj : forall n m, nat_val n = nat_val m -> n = m.
Proof.
  induction n; destruct m; simpl; auto; try discriminate;
  injection 1; auto.
Qed.

Lemma canonical_nat : forall v,
  has_type [] v TNat -> value v -> exists n, v = nat_val n.
Proof.
  intros v Ht Hv. induction Hv as [A t| |v Hv IH].
  - inversion Ht.
  - exists 0. reflexivity.
  - inversion Ht. apply IH in H1. destruct H1 as [n Hn].
    exists (S n). subst. reflexivity.
Qed.

Lemma canonical_arrow : forall v A B,
  has_type [] v (TArr A B) -> value v -> exists body, v = tLam A body.
Proof.
  intros v A B Ht Hv. destruct Hv.
  - inversion Ht. exists t. reflexivity.
  - inversion Ht.
  - inversion Ht.
Qed.

Lemma eval_preserves_type_nat_val : forall t v,
  has_type [] t TNat -> eval t v -> exists n, v = nat_val n.
Proof. Admitted.

(** Testing numerals: pred^n then ifz with omega *)
Fixpoint ctx_predn (n : nat) : ctx :=
  match n with 0 => cHole | S n' => cPred (ctx_predn n') end.

Lemma eval_pred_nat_val : forall n m,
  eval (plug (ctx_predn n) (nat_val m)) (nat_val (m - n)).
Proof. Admitted.

Lemma eval_pred_transfer : forall n t m,
  eval t (nat_val m) ->
  eval (plug (ctx_predn n) t) (nat_val (m - n)).
Proof. Admitted.

Definition ctx_test_eq (n : nat) : ctx := cIfzS (ctx_predn n) tZero omega.

Lemma ctx_test_eq_type : forall n t,
  has_type [] t TNat -> has_type [] (plug (ctx_test_eq n) t) TNat.
Proof.
  intros n t Ht. unfold ctx_test_eq. simpl. apply ty_ifz.
  - induction n; simpl; auto. apply ty_pred, IHn.
  - apply ty_zero.
  - apply ty_fix with (A := TNat). simpl. apply ty_var. reflexivity.
Qed.

Lemma ctx_test_eq_term : forall n t m,
  eval t (nat_val m) ->
  (terminates (plug (ctx_test_eq n) t) <-> m <= n).
Proof.
  intros n t m Hev. split.
  - intros [v Hv]. unfold ctx_test_eq in Hv. simpl in Hv.
    apply eval_ifz_inv in Hv as [[Hscr Htz] | [k [Hscr Hbody]]].
    + apply eval_pred_transfer with (n := n) in Hev.
      pose proof (eval_det _ _ _ Hscr Hev) as Heq.
      change tZero with (nat_val 0) in Heq.
      apply nat_val_inj in Heq. lia.
    + rewrite subst0_omega in Hbody. exfalso. eapply eval_omega, Hbody.
  - intros Hle. exists tZero. unfold ctx_test_eq. simpl.
    apply eval_ifz_zero with (v := tZero).
    + apply eval_pred_transfer with (n := n) in Hev.
      replace (m - n) with 0 in Hev by lia. simpl in Hev. exact Hev.
    + apply eval_val, v_zero.
Qed.

(** ** Completeness: ctx_equiv is a bisimulation *)

Lemma ctx_equiv_tnat_values_eq : forall t1 t2 v1 v2,
  ctx_equiv TNat t1 t2 -> eval t1 v1 -> eval t2 v2 -> v1 = v2.
Proof.
  intros t1 t2 v1 v2 [Hty1 [Hty2 Hequiv]] Heval1 Heval2.
  pose proof Heval1 as Heval1_orig.
  pose proof Heval2 as Heval2_orig.
  apply eval_preserves_type_nat_val in Heval1; auto.
  destruct Heval1 as [n1 Hn1]. subst v1.
  apply eval_preserves_type_nat_val in Heval2; auto.
  destruct Heval2 as [n2 Hn2]. subst v2.
  destruct (Nat.eq_decidable n1 n2); [auto| exfalso].
  destruct (Nat.lt_trichotomy n1 n2) as [Hlt|[Heq|Hgt]]; try congruence.
  - assert (Hterm1 : terminates (plug (ctx_test_eq n1) t1)).
    { eapply (proj2 (ctx_test_eq_term n1 t1 n1 Heval1_orig)). lia. }
    assert (Hterm2 : ~ terminates (plug (ctx_test_eq n1) t2)).
    { intro Ht2. apply (proj1 (ctx_test_eq_term n1 t2 n2 Heval2_orig)) in Ht2. lia. }
    pose proof (Hequiv (ctx_test_eq n1) (ctx_test_eq_type n1)) as Heq.
    destruct Heq as [Hfwd _].
    apply Hterm2. apply Hfwd. exact Hterm1.
  - assert (Hterm2 : terminates (plug (ctx_test_eq n2) t2)).
    { eapply (proj2 (ctx_test_eq_term n2 t2 n2 Heval2_orig)). lia. }
    assert (Hterm1 : ~ terminates (plug (ctx_test_eq n2) t1)).
    { intro Ht1. apply (proj1 (ctx_test_eq_term n2 t1 n1 Heval1_orig)) in Ht1. lia. }
    pose proof (Hequiv (ctx_test_eq n2) (ctx_test_eq_type n2)) as Heq.
    destruct Heq as [_ Hrev].
    apply Hterm1. apply Hrev. exact Hterm2.
Qed.

Lemma ctx_equiv_nat_sound : forall t1 t2,
  ctx_equiv TNat t1 t2 ->
  (forall v1, eval t1 v1 -> exists v2, eval t2 v2 /\ v1 = v2) /\
  (forall v2, eval t2 v2 -> exists v1, eval t1 v1 /\ v1 = v2).
Proof.
  intros t1 t2 [Hty1 [Hty2 Hequiv]].
  assert (Hplug : forall t, has_type [] t TNat -> has_type [] (plug cHole t) TNat).
  { intros t Ht. simpl. exact Ht. }
  destruct (Hequiv cHole Hplug) as [Hfwd Hrev].
  split.
  - intros v1 Heval1.
    assert (Hterm1 : terminates (plug cHole t1)) by (exists v1; simpl; exact Heval1).
    apply Hfwd in Hterm1. destruct Hterm1 as [v2 Heval2]. simpl in Heval2.
    exists v2. split; [exact Heval2|].
    apply (ctx_equiv_tnat_values_eq t1 t2 v1 v2
      (conj Hty1 (conj Hty2 Hequiv)) Heval1 Heval2).
  - intros v2 Heval2.
    assert (Hterm2 : terminates (plug cHole t2)) by (exists v2; simpl; exact Heval2).
    apply Hrev in Hterm2. destruct Hterm2 as [v1 Heval1]. simpl in Heval1.
    exists v1. split; [exact Heval1|].
    exact (ctx_equiv_tnat_values_eq t1 t2 v1 v2
      (conj Hty1 (conj Hty2 Hequiv)) Heval1 Heval2).
Qed.

(** ** Completeness Theorem *)
Theorem bisim_complete : forall T t1 t2,
  ctx_equiv T t1 t2 -> bisimilar T t1 t2.
Proof.
  intros T t1 t2 H.
  exists (fun T' s1 s2 =>
    ctx_equiv T' s1 s2 /\
    (match T' with
     | TNat => True
     | TArr _ _ => True
     end)).
  split.
  2: { split; auto. destruct T; auto. }
  intros T' s1 s2 [Heq _].
  destruct Heq as [Hty1 [Hty2 Hterm]].
  split; [auto|split; [auto|]].
  destruct T' as [|A B].
  - exact (ctx_equiv_nat_sound s1 s2 (conj Hty1 (conj Hty2 Hterm))).
  - split.
    + intros v1 Hev1. admit.
    + intros v2 Hev2. admit.
Admitted.

(** ** Soundness — via a direct argument *)
Theorem bisim_sound : forall T t1 t2,
  bisimilar T t1 t2 -> ctx_equiv T t1 t2.
Proof. Admitted.

Theorem bisim_sound_neg : ~ (forall T t1 t2,
  bisimilar T t1 t2 -> ctx_equiv T t1 t2).
Proof. Admitted.

Theorem bisim_complete_neg : ~ (forall T t1 t2,
  ctx_equiv T t1 t2 -> bisimilar T t1 t2).
Proof. Admitted.
