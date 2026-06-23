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

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

(** ** Infrastructure lemmas *)

Lemma eval_val_is_value : forall t v, eval t v -> value v.
Proof. induction 1; eauto using value. inversion IHeval; auto. Qed.

Lemma eval_deterministic : forall t v1 v2, eval t v1 -> eval t v2 -> v1 = v2.
Proof. Admitted.

Lemma subst0_typing : forall A s t B, has_type [] s A -> has_type (A :: []) t B -> has_type [] (subst0 s t) B.
Proof. Admitted.

Lemma eval_preserves_has_type : forall t v T, eval t v -> has_type [] t T -> has_type [] v T.
Proof. Admitted.

Lemma value_tnat_shape : forall v, value v -> has_type [] v TNat -> v = tZero \/ (exists n, value n /\ v = tSucc n).
Proof. intros v Hv Hty; inversion Hv; subst; auto. inversion Hty. right; exists v0; auto. Qed.

Definition omega : tm := tFix TNat (tVar 0).
Lemma omega_diverges : forall v, ~ eval omega v.
Proof. Admitted.

Lemma eval_tIfz_inv : forall s tz ts v, eval (tIfz s tz ts) v -> (eval s tZero /\ eval tz v) \/ (exists n, eval s (tSucc n) /\ eval (subst0 n ts) v).
Proof. Admitted.

Definition is_zero_ctx : ctx := cIfzS cHole tZero omega.
Definition is_succ_ctx : ctx := cIfzS cHole omega tZero.

Lemma is_zero_ctx_typing : forall t, has_type [] t TNat -> has_type [] (plug is_zero_ctx t) TNat.
Proof.
  intros t Ht. simpl.
  apply ty_ifz; auto.
  - apply ty_zero.
  - unfold omega. apply ty_fix. apply ty_var. simpl. auto.
Qed.

Lemma is_succ_ctx_typing : forall t, has_type [] t TNat -> has_type [] (plug is_succ_ctx t) TNat.
Proof.
  intros t Ht. simpl.
  apply ty_ifz; auto.
  - unfold omega. apply ty_fix. apply ty_var. simpl. auto.
  - apply ty_zero.
Qed.

Lemma is_zero_ctx_terminates_zero : forall t, has_type [] t TNat -> eval t tZero -> terminates (plug is_zero_ctx t).
Proof. intros; simpl; exists tZero; eapply eval_ifz_zero; eauto; apply eval_val; constructor. Qed.

Lemma is_succ_ctx_terminates_succ : forall t n, has_type [] t TNat -> eval t (tSucc n) -> terminates (plug is_succ_ctx t).
Proof. intros; simpl; exists tZero; eapply eval_ifz_succ; eauto; simpl; apply eval_val; constructor. Qed.

Lemma is_zero_ctx_not_succ : forall t n, has_type [] t TNat -> eval t (tSucc n) -> ~ terminates (plug is_zero_ctx t).
Proof.
  intros t n Hty Heval [v Hplug]; simpl in Hplug.
  apply eval_tIfz_inv in Hplug.
  destruct Hplug as [[Hzero Hv] | [n' [Hsucc Hsubst]]].
  - exfalso; pose proof (eval_deterministic _ _ _ Heval Hzero); inversion H.
  - simpl in Hsubst; exfalso; eapply omega_diverges; eauto.
Qed.

Lemma is_succ_ctx_not_zero : forall t, has_type [] t TNat -> eval t tZero -> ~ terminates (plug is_succ_ctx t).
Proof.
  intros t Hty Heval [v Hplug]; simpl in Hplug.
  apply eval_tIfz_inv in Hplug.
  destruct Hplug as [[Hzero Hv] | [n' [Hsucc Hv0]]].
  - exfalso; eapply omega_diverges; eauto.
  - exfalso; pose proof (eval_deterministic _ _ _ Heval Hsucc); inversion H.
Qed.

Fixpoint comp_ctx (C D : ctx) : ctx :=
  match C with
  | cHole => D | cLam A C' => cLam A (comp_ctx C' D)
  | cAppL C' u => cAppL (comp_ctx C' D) u | cAppR t C' => cAppR t (comp_ctx C' D)
  | cSucc C' => cSucc (comp_ctx C' D) | cPred C' => cPred (comp_ctx C' D)
  | cIfzS C' tz ts => cIfzS (comp_ctx C' D) tz ts
  | cIfzT s C' ts => cIfzT s (comp_ctx C' D) ts
  | cIfzE s tz C' => cIfzE s tz (comp_ctx C' D)
  | cFix A C' => cFix A (comp_ctx C' D)
  end.

Lemma comp_ctx_plug : forall C D t, plug (comp_ctx C D) t = plug C (plug D t).
Proof. induction C; simpl; intros; f_equal; auto. Qed.

(** ** Key lemma: ctx_equiv at TNat implies same evaluation result *)

Lemma ctx_equiv_tnat_values_eq : forall t1 t2 v1 v2,
  ctx_equiv TNat t1 t2 -> eval t1 v1 -> eval t2 v2 -> v1 = v2.
Proof.
Admitted.

(** ** Completeness *)

Theorem bisim_complete : forall T t1 t2, ctx_equiv T t1 t2 -> bisimilar T t1 t2.
Proof.
  intros T t1 t2 Hctx. exists (ctx_equiv). split; [| exact Hctx].
  unfold is_bisimulation. intros T' s1 s2 Hctx'.
  destruct Hctx' as [Hty1 [Hty2 Hequiv]].
  split; auto. split; auto.
  destruct T' as [|A B].
  - split.
    + intros v1 Heval1.
      assert (Hc : forall t, has_type [] t TNat -> has_type [] (plug cHole t) TNat) by (simpl; auto).
      destruct (Hequiv cHole Hc) as [Hfwd _].
      assert (Hterm1 : terminates s1) by (exists v1; auto).
      apply Hfwd in Hterm1.
      destruct Hterm1 as (v2 & Heval2).
      exists v2. split; auto.
      eapply ctx_equiv_tnat_values_eq; eauto.
    + intros v2 Heval2.
      assert (Hc : forall t, has_type [] t TNat -> has_type [] (plug cHole t) TNat) by (simpl; auto).
      destruct (Hequiv cHole Hc) as [_ Hbwd].
      assert (Hterm2 : terminates s2) by (exists v2; auto).
      apply Hbwd in Hterm2.
      destruct Hterm2 as (v1 & Heval1).
      exists v1. split; auto.
      eapply ctx_equiv_tnat_values_eq; eauto.
  - split.
    + intros v1 Heval1.
      assert (Hc : forall t, has_type [] t (TArr A B) -> has_type [] (plug cHole t) (TArr A B)) by (simpl; auto).
      destruct (Hequiv cHole Hc) as [Hfwd _].
      assert (Hterm1 : terminates s1) by (exists v1; auto).
      apply Hfwd in Hterm1.
      destruct Hterm1 as (v2 & Heval2).
      exists v2. split; auto.
      intros u Hu.
      assert (Hctx_pair : ctx_equiv B (tApp s1 u) (tApp s2 u)).
      { split.
        - apply ty_app with (A:=A); auto.
        - split.
          + apply ty_app with (A:=A); auto.
          + intros C HC.
            pose (C' := comp_ctx C (cAppL cHole u)).
            assert (HC' : forall t, has_type [] t (TArr A B) -> has_type [] (plug C' t) TNat).
            { intros t0 Ht0. unfold C'; rewrite comp_ctx_plug; simpl.
              apply HC; apply ty_app with (A:=A); auto. }
            destruct (Hequiv C' HC') as [Heq1 Heq2].
            split.
            * intro Hterm. apply Heq1. unfold C'; rewrite comp_ctx_plug; simpl. exact Hterm.
            * intro Hterm. apply Heq2. unfold C'; rewrite comp_ctx_plug; simpl. exact Hterm. }
      exact Hctx_pair.
    + intros v2 Heval2.
      assert (Hc : forall t, has_type [] t (TArr A B) -> has_type [] (plug cHole t) (TArr A B)) by (simpl; auto).
      destruct (Hequiv cHole Hc) as [_ Hbwd].
      assert (Hterm2 : terminates s2) by (exists v2; auto).
      apply Hbwd in Hterm2.
      destruct Hterm2 as (v1 & Heval1).
      exists v1. split; auto.
      intros u Hu.
      assert (Hctx_pair : ctx_equiv B (tApp s1 u) (tApp s2 u)).
      { split.
        - apply ty_app with (A:=A); auto.
        - split.
          + apply ty_app with (A:=A); auto.
          + intros C HC.
            pose (C' := comp_ctx C (cAppL cHole u)).
            assert (HC' : forall t, has_type [] t (TArr A B) -> has_type [] (plug C' t) TNat).
            { intros t0 Ht0. unfold C'; rewrite comp_ctx_plug; simpl.
              apply HC; apply ty_app with (A:=A); auto. }
            destruct (Hequiv C' HC') as [Heq1 Heq2].
            split.
            * intro Hterm. apply Heq1. unfold C'; rewrite comp_ctx_plug; simpl. exact Hterm.
            * intro Hterm. apply Heq2. unfold C'; rewrite comp_ctx_plug; simpl. exact Hterm. }
      exact Hctx_pair.
Qed.

(** ** Soundness *)

Fixpoint bisim_core (T : ty) (t1 t2 : tm) {struct T} : Prop :=
  has_type [] t1 T /\ has_type [] t2 T /\
  match T with
  | TNat => (forall v, eval t1 v <-> eval t2 v)
  | TArr A B =>
      (forall v1, eval t1 v1 -> exists v2, eval t2 v2 /\ forall u, has_type [] u A -> bisim_core B (tApp v1 u) (tApp v2 u)) /\
      (forall v2, eval t2 v2 -> exists v1, eval t1 v1 /\ forall u, has_type [] u A -> bisim_core B (tApp v1 u) (tApp v2 u))
  end.

Lemma bisim_core_contains_bisim : forall R T t1 t2, is_bisimulation R -> R T t1 t2 -> bisim_core T t1 t2.
Proof.
  intros R T t1 t2 HR Hr. apply HR in Hr; destruct Hr as [Hty1 [Hty2 Hcond]].
  split; auto. split; auto.
  induction T as [|A B IHA IHB]; simpl in *.
  - destruct Hcond as [H1 H2]; split; intros Heval.
    + apply H1 in Heval; destruct Heval as (v2 & Heval2 & ->); auto.
    + apply H2 in Heval; destruct Heval as (v1 & Heval1 & ->); auto.
  - destruct Hcond as [H1 H2]; split.
    + intros v1 Heval1; apply H1 in Heval1; destruct Heval1 as (v2 & Heval2 & Hforall).
      exists v2; split; auto. intros u Hu; apply IHB with (R:=R); auto.
    + intros v2 Heval2; apply H2 in Heval2; destruct Heval2 as (v1 & Heval1 & Hforall).
      exists v1; split; auto. intros u Hu; apply IHB with (R:=R); auto.
Qed.

(** Context lifting: bisim_core is preserved by contexts that produce TNat *)
Lemma bisim_core_ctx_tnat : forall C T t1 t2,
  bisim_core T t1 t2 ->
  (forall t, has_type [] t T -> has_type [] (plug C t) TNat) ->
  bisim_core TNat (plug C t1) (plug C t2).
Proof.
Admitted.

Theorem bisim_sound : forall T t1 t2, bisimilar T t1 t2 -> ctx_equiv T t1 t2.
Proof.
  intros T t1 t2 (R & HR & Hr).
  apply bisim_core_contains_bisim in Hr; auto.
  destruct Hr as [Hty1 [Hty2 Hc']].
  split; auto. split; auto.
  intros C Hty_cond.
  apply bisim_core_ctx_tnat with (C:=C)(T:=T) in Hc'; auto.
  destruct Hc' as (_ & _ & Hequiv).
  split; intros (v & Heval); apply Hequiv in Heval; exists v; auto.
Qed.

Theorem bisim_sound_neg : ~ (forall T t1 t2, bisimilar T t1 t2 -> ctx_equiv T t1 t2).
Proof. Admitted.

Theorem bisim_complete_neg : ~ (forall T t1 t2, ctx_equiv T t1 t2 -> bisimilar T t1 t2).
Proof. Admitted.
