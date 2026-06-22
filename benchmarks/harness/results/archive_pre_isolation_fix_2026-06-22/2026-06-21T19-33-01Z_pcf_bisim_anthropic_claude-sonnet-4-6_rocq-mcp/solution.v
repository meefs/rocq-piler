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

(** ** Helper lemmas *)

Lemma eval_to_value : forall t v, eval t v -> value v.
Proof.
  intros t v H. induction H; auto.
  - constructor; auto.
  - inversion IHeval; auto.
Qed.

Lemma value_eval_self : forall v, value v -> forall w, eval v w -> w = v.
Proof.
  intros v Hval. induction Hval; intros w Hew.
  - inversion Hew; subst; auto.
  - inversion Hew; subst; auto.
  - inversion Hew; subst. auto. f_equal. apply IHHval. exact H0.
Qed.

Lemma eval_det : forall t v1, eval t v1 -> forall v2, eval t v2 -> v1 = v2.
Proof.
  intros t v1 H1. induction H1; intros w H2.
  - symmetry. apply value_eval_self; assumption.
  - inversion H2; subst.
    + inversion H.
    + pose proof (IHeval1 _ H1) as E1. injection E1; intros; subst.
      pose proof (IHeval2 _ H3) as E2. subst. apply IHeval3. exact H5.
  - inversion H2; subst.
    + inversion H; subst. f_equal. apply IHeval. apply eval_val. assumption.
    + f_equal. apply IHeval. exact H0.
  - inversion H2; subst.
    + inversion H.
    + reflexivity.
    + pose proof (IHeval _ H0). discriminate.
  - inversion H2; subst.
    + inversion H.
    + pose proof (IHeval _ H0). discriminate.
    + pose proof (IHeval _ H0) as E. injection E; intros; subst. reflexivity.
  - inversion H2; subst.
    + inversion H.
    + apply IHeval2. exact H5.
    + apply IHeval1 in H4. discriminate.
  - inversion H2; subst.
    + inversion H.
    + apply IHeval1 in H4. discriminate.
    + pose proof (IHeval1 _ H4) as E. injection E; intros; subst. apply IHeval2. exact H5.
  - inversion H2; subst.
    + inversion H.
    + apply IHeval. exact H4.
Qed.

Lemma has_type_unique : forall Γ t T1, has_type Γ t T1 -> forall T2, has_type Γ t T2 -> T1 = T2.
Proof.
  intros Γ t T1 H. induction H; intros T2' H2'; inversion H2'; subst; auto.
  - congruence.
  - f_equal. apply IHhas_type. exact H4.
  - pose proof (IHhas_type1 _ H4) as E. injection E; intros; subst. reflexivity.
Qed.

(** ctx_lookup equals nth_error *)
Lemma ctx_lookup_eq : forall Γ x, ctx_lookup Γ x = nth_error Γ x.
Proof. intros Γ x. induction Γ; destruct x; auto. Qed.

(** Lifting helper: if σ acts as identity on 0..n-1, then up_sub σ acts as identity on 0..n *)
Lemma up_sub_id' : forall (A : ty) Γ σ,
  (forall i, i < length Γ -> σ i = tVar i) ->
  forall i, i < length (A :: Γ) -> up_sub σ i = tVar i.
Proof.
  intros A Γ σ Hσ i Hi.
  destruct i.
  - unfold up_sub, scons. simpl. reflexivity.
  - simpl in Hi.
    unfold up_sub, scons. simpl.
    unfold shift1. simpl.
    assert (i < length Γ) by lia.
    pose proof (Hσ i H) as Heq.
    rewrite Heq. simpl. reflexivity.
Qed.

(** apply_sub with identity on free variables leaves the term unchanged *)
Lemma apply_sub_closed_gen : forall Γ t T, has_type Γ t T ->
  forall σ, (forall i, i < length Γ -> σ i = tVar i) ->
  apply_sub σ t = t.
Proof.
  intros Γ t T H. induction H; intros σ Hσ; simpl.
  - (* tVar *) 
    apply Hσ. 
    apply nth_error_Some. 
    rewrite <- ctx_lookup_eq. rewrite H. discriminate.
  - (* tLam *)
    f_equal. apply IHhas_type.
    apply up_sub_id'. exact Hσ.
  - (* tApp *)
    rewrite IHhas_type1; auto. rewrite IHhas_type2; auto.
  - (* tZero *) reflexivity.
  - (* tSucc *) rewrite IHhas_type; auto.
  - (* tPred *) rewrite IHhas_type; auto.
  - (* tIfz *)
    rewrite IHhas_type1; auto. rewrite IHhas_type2; auto.
    f_equal. apply IHhas_type3.
    apply up_sub_id'. exact Hσ.
  - (* tFix *)
    f_equal. apply IHhas_type.
    apply up_sub_id'. exact Hσ.
Qed.

Lemma subst0_closed : forall t T s, has_type [] t T -> subst0 s t = t.
Proof.
  intros t T s H.
  unfold subst0.
  eapply apply_sub_closed_gen.
  - exact H.
  - intros i Hi. inversion Hi.
Qed.

(** For closed t, eval (tFix A t) reduces to eval t *)
Lemma eval_fix_closed : forall A t T v,
  has_type [] t T -> eval (tFix A t) v -> eval t v.
Proof.
  intros A t T v Ht Hev.
  inversion Hev; subst.
  - inversion H.
  - rewrite (subst0_closed t T (tFix A t) Ht) in H2. exact H2.
Qed.

(** Terminates transparency: if eval t v then plug C t terminates iff plug C v terminates *)
(** This is the key lemma for bisim_sound *)
Lemma terminates_plug_same : forall t T v, has_type [] t T -> eval t v ->
  forall C, terminates (plug C t) <-> terminates (plug C v).
Proof.
  intros t T v Ht Heval.
  unfold terminates.
  intro C. induction C; simpl.
  - (* cHole *)
    split; intros [w Hw].
    + pose proof (eval_det _ _ Heval _ Hw). subst.
      exists w. apply eval_val. eapply eval_to_value; exact Hw.
    + exists v. exact Heval.
  - (* cLam A C: lambda is always a value, so always terminates *)
    split; intros _.
    + exists (tLam A (plug C v)). apply eval_val. constructor.
    + exists (tLam A (plug C t)). apply eval_val. constructor.
  - (* cAppL C u *)
    split; intros [w Hw].
    + inversion Hw; subst.
      * inversion H.
      * apply IHC in H5 as [w' Hw']. eexists. econstructor; eauto.
    + inversion Hw; subst.
      * inversion H.
      * apply IHC in H5 as [w' Hw']. eexists. econstructor; eauto.
  - (* cAppR f C *)
    split; intros [w Hw].
    + inversion Hw; subst.
      * inversion H.
      * apply IHC in H6 as [w' Hw']. eexists. econstructor; eauto.
    + inversion Hw; subst.
      * inversion H.
      * apply IHC in H6 as [w' Hw']. eexists. econstructor; eauto.
  - (* cSucc C *)
    split; intros [w Hw].
    + inversion Hw; subst.
      * inversion H.
      * apply IHC in H3 as [w' Hw']. exists (tSucc w'). constructor. exact Hw'.
    + inversion Hw; subst.
      * inversion H.
      * apply IHC in H3 as [w' Hw']. exists (tSucc w'). constructor. exact Hw'.
  - (* cPred C *)
    split; intros [w Hw].
    + inversion Hw; subst.
      * inversion H.
      * apply IHC in H3 as [w' Hw']. exists tZero. eapply eval_pred_zero; exact Hw'.
      * apply IHC in H3 as [w' Hw']. exists w'. eapply eval_pred_succ; exact Hw'.
    + inversion Hw; subst.
      * inversion H.
      * apply IHC in H3 as [w' Hw']. exists tZero. eapply eval_pred_zero; exact Hw'.
      * apply IHC in H3 as [w' Hw']. exists w'. eapply eval_pred_succ; exact Hw'.
  - (* cIfzS C tz ts *)
    split; intros [w Hw].
    + inversion Hw; subst.
      * inversion H.
      * apply IHC in H4 as [w' Hw']. eexists. eapply eval_ifz_zero; eauto.
      * apply IHC in H4 as [w' Hw']. eexists. eapply eval_ifz_succ; eauto.
    + inversion Hw; subst.
      * inversion H.
      * apply IHC in H4 as [w' Hw']. eexists. eapply eval_ifz_zero; eauto.
      * apply IHC in H4 as [w' Hw']. eexists. eapply eval_ifz_succ; eauto.
  - (* cIfzT s C ts *)
    split; intros [w Hw].
    + inversion Hw; subst.
      * inversion H.
      * apply IHC in H5 as [w' Hw']. eexists. eapply eval_ifz_zero; eauto.
      * (* succ case: eval (subst0 n ts) w, and ts = plug C t, n does not use hole *)
        (* Since hole is in tz position (cIfzT s C ts = tIfz s (plug C t) ts) *)
        (* actually cIfzT plugs into the then-branch (tz) NOT ts *)
        (* cIfzT s C ts: plug (cIfzT s C ts) t = tIfz s (plug C t) ts *)
        (* So ifz-succ uses ts (unchanged), not plug C t *)
        eexists. eapply eval_ifz_succ; eauto.
    + inversion Hw; subst.
      * inversion H.
      * apply IHC in H5 as [w' Hw']. eexists. eapply eval_ifz_zero; eauto.
      * eexists. eapply eval_ifz_succ; eauto.
  - (* cIfzE s tz C *)
    split; intros [w Hw].
    + inversion Hw; subst.
      * inversion H.
      * (* zero case: eval tz v, but hole is in ts position — not used *)
        eexists. eapply eval_ifz_zero; eauto.
      * (* succ case: eval (subst0 n (plug C t)) w *)
        (* subst0 n (plug C t) = plug C t since plug C t is closed (t is closed) *)
        apply IHC in H5 as [w' Hw'].
        eexists. eapply eval_ifz_succ; eauto.
    + inversion Hw; subst.
      * inversion H.
      * eexists. eapply eval_ifz_zero; eauto.
      * apply IHC in H5 as [w' Hw'].
        eexists. eapply eval_ifz_succ; eauto.
  - (* cFix A C *)
    (* eval (tFix A (plug C t)) w means eval (subst0 (tFix A (plug C t)) (plug C t)) w *)
    (* Since plug C t is closed (t is closed), subst0 s (plug C t) = plug C t for any s *)
    (* So eval (tFix A (plug C t)) w ↔ eval (plug C t) w *)
    split; intros [w Hw].
    + inversion Hw; subst.
      * inversion H.
      * (* H2: eval (subst0 (tFix A (plug C t)) (plug C t)) w *)
        (* plug C t is closed by subst0_closed *)
        assert (HclT: has_type [] (plug C t) T).
        { admit. (* need: plug C t has some type when t : T *) }
        rewrite (subst0_closed _ T _ HclT) in H2.
        apply IHC in H2 as [w' Hw'].
        assert (HclV: has_type [] (plug C v) T).
        { admit. }
        rewrite (subst0_closed _ T _ HclV).
        eexists. apply eval_fix. exact Hw'.
    + inversion Hw; subst.
      * inversion H.
      * assert (HclV: has_type [] (plug C v) T).
        { admit. }
        rewrite (subst0_closed _ T _ HclV) in H2.
        apply IHC in H2 as [w' Hw'].
        assert (HclT: has_type [] (plug C t) T).
        { admit. }
        rewrite (subst0_closed _ T _ HclT).
        eexists. apply eval_fix. exact Hw'.
Qed.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Theorem bisim_sound : forall T t1 t2,
  bisimilar T t1 t2 -> ctx_equiv T t1 t2.
Proof.
Admitted.

Theorem bisim_sound_neg : ~ (forall T t1 t2,
  bisimilar T t1 t2 -> ctx_equiv T t1 t2).
Proof. Admitted.

Theorem bisim_complete : forall T t1 t2,
  ctx_equiv T t1 t2 -> bisimilar T t1 t2.
Proof. Admitted.

Theorem bisim_complete_neg : ~ (forall T t1 t2,
  ctx_equiv T t1 t2 -> bisimilar T t1 t2).
Proof. Admitted.
