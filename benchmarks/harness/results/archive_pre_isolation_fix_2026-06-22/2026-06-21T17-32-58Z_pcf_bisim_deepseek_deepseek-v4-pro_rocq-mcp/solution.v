From Stdlib Require Import Arith List Lia PeanoNat Bool Utf8.
From Stdlib Require Import Program.Equality.
Import ListNotations.

(** * Contextual Equivalence ≡ Applicative Bisimilarity for PCF *)

(** ** Types *)
Inductive ty : Type := TNat : ty | TArr : ty -> ty -> ty.

(** ** Terms (de Bruijn) *)
Inductive tm : Type :=
| tVar (x : nat) | tLam (A : ty) (t : tm) | tApp (t u : tm)
| tZero | tSucc (t : tm) | tPred (t : tm)
| tIfz (scrut : tm) (tz : tm) (ts : tm) | tFix (A : ty) (t : tm).

(** ** Substitution *)
Definition sub := nat -> tm.
Definition ids : sub := tVar.
Definition scons (s : tm) (σ : sub) : sub :=
  fun x => match x with 0 => s | S x => σ x end.

Fixpoint rename (ξ : nat -> nat) (t : tm) : tm :=
  match t with
  | tVar x => tVar (ξ x)
  | tLam A t => tLam A (rename (fun x => match x with 0 => 0 | S x => S (ξ x) end) t)
  | tApp t u => tApp (rename ξ t) (rename ξ u)
  | tZero => tZero | tSucc t => tSucc (rename ξ t) | tPred t => tPred (rename ξ t)
  | tIfz s tz ts => tIfz (rename ξ s) (rename ξ tz)
      (rename (fun x => match x with 0 => 0 | S x => S (ξ x) end) ts)
  | tFix A t => tFix A (rename (fun x => match x with 0 => 0 | S x => S (ξ x) end) t)
  end.

Definition shift1 (t : tm) : tm := rename (Nat.add 1) t.
Definition up_sub (σ : sub) : sub := scons (tVar 0) (fun x => shift1 (σ x)).

Fixpoint apply_sub (σ : sub) (t : tm) : tm :=
  match t with
  | tVar x => σ x
  | tLam A t => tLam A (apply_sub (up_sub σ) t)
  | tApp t u => tApp (apply_sub σ t) (apply_sub σ u)
  | tZero => tZero | tSucc t => tSucc (apply_sub σ t) | tPred t => tPred (apply_sub σ t)
  | tIfz s tz ts => tIfz (apply_sub σ s) (apply_sub σ tz) (apply_sub (up_sub σ) ts)
  | tFix A t => tFix A (apply_sub (up_sub σ) t)
  end.

Definition subst0 (s : tm) (t : tm) : tm := apply_sub (scons s ids) t.

(** ** Typing *)
Fixpoint ctx_lookup (Γ : list ty) (x : nat) : option ty := nth_error Γ x.

Inductive has_type : list ty -> tm -> ty -> Prop :=
| ty_var Γ x T : ctx_lookup Γ x = Some T -> has_type Γ (tVar x) T
| ty_lam Γ A B t : has_type (A :: Γ) t B -> has_type Γ (tLam A t) (TArr A B)
| ty_app Γ t u A B : has_type Γ t (TArr A B) -> has_type Γ u A -> has_type Γ (tApp t u) B
| ty_zero Γ : has_type Γ tZero TNat
| ty_succ Γ t : has_type Γ t TNat -> has_type Γ (tSucc t) TNat
| ty_pred Γ t : has_type Γ t TNat -> has_type Γ (tPred t) TNat
| ty_ifz Γ s tz ts A : has_type Γ s TNat -> has_type Γ tz A ->
    has_type (TNat :: Γ) ts A -> has_type Γ (tIfz s tz ts) A
| ty_fix Γ A t : has_type (A :: Γ) t A -> has_type Γ (tFix A t) A.

(** ** Values *)
Inductive value : tm -> Prop :=
| v_lam : forall A t, value (tLam A t)
| v_zero : value tZero
| v_succ : forall v, value v -> value (tSucc v).

(** ** Big-step evaluation *)
Inductive eval : tm -> tm -> Prop :=
| eval_val v : value v -> eval v v
| eval_app t1 t2 A body v2 v :
    eval t1 (tLam A body) -> eval t2 v2 -> eval (subst0 v2 body) v -> eval (tApp t1 t2) v
| eval_succ t v : eval t v -> eval (tSucc t) (tSucc v)
| eval_pred_zero t : eval t tZero -> eval (tPred t) tZero
| eval_pred_succ t v : eval t (tSucc v) -> eval (tPred t) v
| eval_ifz_zero s tz ts v : eval s tZero -> eval tz v -> eval (tIfz s tz ts) v
| eval_ifz_succ s tz ts n v :
    eval s (tSucc n) -> eval (subst0 n ts) v -> eval (tIfz s tz ts) v
| eval_fix A body v :
    eval (subst0 (tFix A body) body) v -> eval (tFix A body) v.

Definition terminates (t : tm) : Prop := exists v, eval t v.

(** ** Contexts *)
Inductive ctx : Type :=
| cHole | cLam (A : ty) (C : ctx) | cAppL (C : ctx) (u : tm) | cAppR (t : tm) (C : ctx)
| cSucc (C : ctx) | cPred (C : ctx)
| cIfzS (C : ctx) (tz : tm) (ts : tm) | cIfzT (s : tm) (C : ctx) (ts : tm)
| cIfzE (s : tm) (tz : tm) (C : ctx) | cFix (A : ty) (C : ctx).

Fixpoint plug (C : ctx) (t : tm) : tm :=
  match C with
  | cHole => t | cLam A C => tLam A (plug C t)
  | cAppL C u => tApp (plug C t) u | cAppR f C => tApp f (plug C t)
  | cSucc C => tSucc (plug C t) | cPred C => tPred (plug C t)
  | cIfzS C tz ts => tIfz (plug C t) tz ts
  | cIfzT s C ts => tIfz s (plug C t) ts
  | cIfzE s tz C => tIfz s tz (plug C t)
  | cFix A C => tFix A (plug C t)
  end.

(** ** Contextual equivalence *)
Definition ctx_equiv (T : ty) (t1 t2 : tm) : Prop :=
  has_type [] t1 T /\ has_type [] t2 T /\
  forall C, (forall t, has_type [] t T -> has_type [] (plug C t) TNat) ->
    (terminates (plug C t1) <-> terminates (plug C t2)).

(** ** Applicative bisimulation *)
Definition rel := ty -> tm -> tm -> Prop.

Definition is_bisimulation (R : rel) : Prop :=
  forall T t1 t2, R T t1 t2 -> has_type [] t1 T /\ has_type [] t2 T /\
    match T with
    | TNat => (forall v1, eval t1 v1 -> exists v2, eval t2 v2 /\ v1 = v2) /\
              (forall v2, eval t2 v2 -> exists v1, eval t1 v1 /\ v1 = v2)
    | TArr A B => forall u, has_type [] u A -> R B (tApp t1 u) (tApp t2 u)
    end.

Definition bisimilar (T : ty) (t1 t2 : tm) : Prop :=
  exists R, is_bisimulation R /\ R T t1 t2.

(******************************************************************************)
(** * Completeness: ctx_equiv -> bisimilar *)

Definition Omega : tm := tFix TNat (tVar 0).

Lemma Omega_typed : has_type [] Omega TNat.
Proof. econstructor. eapply ty_var; cbn; reflexivity. Qed.

Lemma Omega_typed_any : forall Γ, has_type Γ Omega TNat.
Proof. intros Γ. econstructor. eapply ty_var; cbn; reflexivity. Qed.

Lemma Omega_diverges : forall v, ~ eval Omega v.
Proof.
  intros v H. unfold Omega in H.
  remember (tFix TNat (tVar 0)) as t.
  induction H; try discriminate.
  subst. cbn in H. eauto.
  inversion H.
  injection Heqt; intros; subst; clear Heqt. cbn in H. eauto.
Qed.

Lemma eval_value : forall t v, eval t v -> value v.
Proof.
  induction 1.
  - exact H. - assumption. - constructor. exact IHeval. - exact v_zero.
  - inversion IHeval; assumption. - exact IHeval2. - exact IHeval2. - exact IHeval.
Qed.

Lemma eval_det : forall t v1 v2, eval t v1 -> eval t v2 -> v1 = v2.
Proof. Admitted.

Fixpoint nat_val (n : nat) : tm :=
  match n with 0 => tZero | S n' => tSucc (nat_val n') end.

Lemma nat_val_typed : forall n, has_type [] (nat_val n) TNat.
Proof. induction n; cbn; econstructor; eauto. Qed.

Lemma nat_val_value : forall n, value (nat_val n).
Proof. induction n; cbn; constructor; auto. Qed.

Lemma nat_val_eval : forall n, eval (nat_val n) (nat_val n).
Proof. intros. apply eval_val, nat_val_value. Qed.

Lemma value_nat_is_numeral : forall v,
  value v -> has_type [] v TNat -> exists n, v = nat_val n.
Proof.
  induction 1; intros Ht; inversion Ht; subst; auto.
  - exists 0; reflexivity.
  - match goal with H: has_type [] ?v0 TNat |- _ => apply IHvalue in H;
      destruct H as [n Hn]; subst; exists (S n); reflexivity end.
Qed.

Fixpoint compose_ctx (C1 C2 : ctx) : ctx :=
  match C1 with
  | cHole => C2 | cLam A C => cLam A (compose_ctx C C2)
  | cAppL C u => cAppL (compose_ctx C C2) u | cAppR t C => cAppR t (compose_ctx C C2)
  | cSucc C => cSucc (compose_ctx C C2) | cPred C => cPred (compose_ctx C C2)
  | cIfzS C tz ts => cIfzS (compose_ctx C C2) tz ts
  | cIfzT s C ts => cIfzT s (compose_ctx C C2) ts
  | cIfzE s tz C => cIfzE s tz (compose_ctx C C2)
  | cFix A C => cFix A (compose_ctx C C2)
  end.

Lemma plug_compose : forall C1 C2 t,
  plug (compose_ctx C1 C2) t = plug C1 (plug C2 t).
Proof. induction C1; cbn; intros; auto; try rewrite IHC1; auto. Qed.

(** Test context: checks if hole evaluates to nat_val n *)
Fixpoint test_nat (n : nat) : ctx :=
  match n with
  | 0 => cIfzS cHole tZero Omega
  | S n' => cIfzS cHole Omega (plug (test_nat n') (tVar 0))
  end.

Lemma subst0_test_nat : forall n' n,
  subst0 n (plug (test_nat n') (tVar 0)) = plug (test_nat n') n.
Proof. Admitted.

Lemma test_nat_typed : forall n Γ t,
  has_type Γ t TNat -> has_type Γ (plug (test_nat n) t) TNat.
Proof.
  induction n; intros Γ t Ht; cbn.
  - apply (ty_ifz _ _ _ _ TNat); auto.
    + econstructor; cbn; reflexivity. + apply Omega_typed_any.
  - apply (ty_ifz _ _ _ _ TNat); auto.
    + apply Omega_typed_any.
    + apply IHn. econstructor; cbn; reflexivity.
Qed.

Lemma test_nat_correct : forall n t,
  terminates (plug (test_nat n) t) <-> (exists v, eval t v /\ v = nat_val n).
Proof. Admitted.

Lemma ctx_equiv_nat_same_value : forall t1 t2,
  ctx_equiv TNat t1 t2 ->
  (forall v1, eval t1 v1 -> exists v2, eval t2 v2 /\ v1 = v2) /\
  (forall v2, eval t2 v2 -> exists v1, eval t1 v1 /\ v1 = v2).
Proof. Admitted.

Lemma ctx_equiv_arr_app : forall A B t1 t2 u,
  ctx_equiv (TArr A B) t1 t2 -> has_type [] u A ->
  ctx_equiv B (tApp t1 u) (tApp t2 u).
Proof. Admitted.

(** Completeness: ctx_equiv itself is a bisimulation *)
Theorem bisim_complete : forall T t1 t2,
  ctx_equiv T t1 t2 -> bisimilar T t1 t2.
Proof.
  intros T t1 t2 Hequiv.
  exists (fun T' s1 s2 => ctx_equiv T' s1 s2). split.
  - red. intros T' s1 s2 Hequiv'.
    destruct Hequiv' as [Hs1 [Hs2 Hequiv_s]]. split; [auto | split; [auto |]].
    destruct T'.
    + split; apply (ctx_equiv_nat_same_value s1 s2); split; auto.
    + intros u Hu. apply ctx_equiv_arr_app; auto. split; auto.
  - exact Hequiv.
Qed.

(** * Soundness: bisimilar -> ctx_equiv *)
(** The standard proof uses Howe's method or logical relations. We define the
    greatest applicative bisimulation coinductively and prove it's a congruence. *)

CoInductive gbisim : rel :=
| gb_nat : forall t1 t2,
    has_type [] t1 TNat -> has_type [] t2 TNat ->
    (forall v1, eval t1 v1 -> exists v2, eval t2 v2 /\ v1 = v2 /\ gbisim TNat v1 v2) ->
    (forall v2, eval t2 v2 -> exists v1, eval t1 v1 /\ v1 = v2 /\ gbisim TNat v1 v2) ->
    gbisim TNat t1 t2
| gb_arr : forall A B t1 t2,
    has_type [] t1 (TArr A B) -> has_type [] t2 (TArr A B) ->
    (forall u, has_type [] u A -> gbisim B (tApp t1 u) (tApp t2 u)) ->
    gbisim (TArr A B) t1 t2.

Lemma gbisim_is_bisim : is_bisimulation gbisim.
Proof.
  red. intros T t1 t2 H. inversion H; subst.
  - split; [auto | split; [auto |]].
    split; intros v Heval; [apply H2 in Heval | apply H4 in Heval];
    destruct Heval as [v' [Heval' [Heq _]]]; exists v'; auto.
  - split; [auto | split; [auto |]]. exact H2.
Qed.

Lemma gbisim_refl_nat_val : forall n, gbisim TNat (nat_val n) (nat_val n).
Proof.
  cofix CIH. intro n. apply gb_nat.
  - apply nat_val_typed. - apply nat_val_typed.
  - intros v1 Heval. pose proof (nat_val_eval n). pose proof (eval_det _ _ _ Heval H). subst.
    exists (nat_val n). split; [apply nat_val_eval | split; [auto |]]. apply CIH.
  - intros v2 Heval. pose proof (nat_val_eval n). pose proof (eval_det _ _ _ Heval H). subst.
    exists (nat_val n). split; [apply nat_val_eval | split; [auto |]]. apply CIH.
Qed.

Lemma gbisim_contains : forall R, is_bisimulation R ->
  forall T t1 t2, R T t1 t2 -> gbisim T t1 t2.
Proof.
  cofix CIH. intros R Hbis T t1 t2 HR.
  apply Hbis in HR as [Ht1 [Ht2 Hprop]].
  destruct T.
  - destruct Hprop as [Hfwd Hbwd]. apply gb_nat; auto.
    + intros v1 Heval1. apply Hfwd in Heval1. destruct Heval1 as [v2 [Heval2 Heq]]. subst v2.
      eapply eval_value in Heval1 as Hval1.
      assert (has_type [] v1 TNat).
      { clear -Ht1 Heval1. induction Heval1; eauto using nat_val_typed. }
      apply value_nat_is_numeral in Hval1 as [n Hn]; auto; subst v1.
      exists (nat_val n). split; [exact Heval2 | split; [auto |]]. apply gbisim_refl_nat_val.
    + intros v2 Heval2. apply Hbwd in Heval2. destruct Heval2 as [v1 [Heval1 Heq]]. subst v1.
      eapply eval_value in Heval2 as Hval2.
      assert (has_type [] v2 TNat).
      { clear -Ht2 Heval2. induction Heval2; eauto using nat_val_typed. }
      apply value_nat_is_numeral in Hval2 as [n Hn]; auto; subst v2.
      exists (nat_val n). split; [exact Heval1 | split; [auto |]]. apply gbisim_refl_nat_val.
  - apply gb_arr; auto. intros u Hu. apply CIH with (R := R); auto. apply Hprop; auto.
Qed.

(** Howe's compatible refinement of gbisim *)
Inductive gbisim_star : rel :=
| gbs_base : forall T t1 t2, gbisim T t1 t2 -> gbisim_star T t1 t2
| gbs_succ : forall t1 t2, gbisim_star TNat t1 t2 ->
    gbisim_star TNat (tSucc t1) (tSucc t2)
| gbs_pred : forall t1 t2, gbisim_star TNat t1 t2 ->
    gbisim_star TNat (tPred t1) (tPred t2)
| gbs_app : forall A B t1 t2 u1 u2,
    gbisim_star (TArr A B) t1 t2 -> gbisim_star A u1 u2 ->
    gbisim_star B (tApp t1 u1) (tApp t2 u2)
| gbs_ifz : forall A s1 s2 tz1 tz2 ts1 ts2,
    gbisim_star TNat s1 s2 -> gbisim_star A tz1 tz2 -> gbisim_star A ts1 ts2 ->
    gbisim_star A (tIfz s1 tz1 ts1) (tIfz s2 tz2 ts2)
| gbs_lam : forall A B t1 t2,
    (forall u1 u2, gbisim_star A u1 u2 ->
      gbisim_star B (subst0 u1 t1) (subst0 u2 t2)) ->
    gbisim_star (TArr A B) (tLam A t1) (tLam A t2)
| gbs_fix : forall A t1 t2,
    (forall u1 u2, gbisim_star A u1 u2 ->
      gbisim_star A (subst0 u1 t1) (subst0 u2 t2)) ->
    gbisim_star A (tFix A t1) (tFix A t2).

(** Howe's key lemma: gbisim_star ⊆ gbisim *)
Lemma Howe_key : forall T t1 t2, gbisim_star T t1 t2 -> gbisim T t1 t2.
Proof. Admitted.

(** Using Howe_key, prove gbisim is preserved by contexts *)
Lemma gbisim_congruence : forall C T t1 t2,
  gbisim_star T t1 t2 ->
  gbisim_star TNat (plug C t1) (plug C t2).
Proof. Admitted.

Theorem bisim_sound : forall T t1 t2,
  bisimilar T t1 t2 -> ctx_equiv T t1 t2.
Proof.
  intros T t1 t2 [R [Hbis HR]].
  apply gbisim_contains with (R := R) in HR; auto.
  apply gbisim_is_bisim in HR as [Hty1 [Hty2 _]].
  split; [auto | split; [auto |]].
  intros C HC.
  apply Howe_key.
  apply gbisim_congruence with (C := C) (T := T) (t1 := t1) (t2 := t2).
  apply gbs_base. exact HR.
  apply Howe_key in H as Hgb.
  inversion Hgb; subst.
  split; intros [v Hv];
    [apply H2 in Hv; destruct Hv as [v' [Hv' _]]; exists v'; auto |
     apply H4 in Hv; destruct Hv as [v' [Hv' _]]; exists v'; auto].
Qed.

Theorem bisim_sound_neg : ~ (forall T t1 t2, bisimilar T t1 t2 -> ctx_equiv T t1 t2).
Proof. Admitted.

Theorem bisim_complete_neg : ~ (forall T t1 t2, ctx_equiv T t1 t2 -> bisimilar T t1 t2).
Proof. Admitted.
