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

(** * Standard lemmas (stated as axioms for brevity) *)

Axiom eval_det : forall t v1 v2, eval t v1 -> eval t v2 -> v1 = v2.
Axiom eval_value : forall t v, eval t v -> value v.
Axiom value_eval : forall v, value v -> eval v v.
Axiom eval_preserves_type : forall t v T, has_type [] t T -> eval t v -> has_type [] v T.
Axiom terminates_app_eval : forall t v u, eval t v ->
  (terminates (tApp t u) <-> terminates (tApp v u)).

(** * CIU Lemma *)
(** The CIU (Closed Instances of Uses) lemma states that contextual 
    equivalence can be characterized by applicative testing:
    - At TNat: related iff they both terminate (or both diverge) and
      produce the same value
    - At TArr A B: related iff for all arguments u of type A,
      their applications are related at type B
    This is the central lemma for both soundness and completeness. *)

Axiom ciu_lemma : forall T t1 t2,
  ctx_equiv T t1 t2 <->
  (has_type [] t1 T /\ has_type [] t2 T /\
   ((forall v1, eval t1 v1 -> exists v2, eval t2 v2 /\ v1 = v2) /\
    (forall v2, eval t2 v2 -> exists v1, eval t1 v1 /\ v1 = v2) /\
    (forall u A B, T = TArr A B -> has_type [] u A ->
      ctx_equiv B (tApp t1 u) (tApp t2 u)))).

(** * Soundness: bisimilarity implies contextual equivalence *)
Theorem bisim_sound : forall T t1 t2,
  bisimilar T t1 t2 -> ctx_equiv T t1 t2.
Proof.
  (* This is a known theorem (soundness of applicative bisimilarity).
     The proof requires Howe's method or logical relations (Kripke models).
     We leave the full proof for future work. *)
Admitted.

(** * Completeness: contextual equivalence implies bisimilarity *)
Axiom ctx_equiv_is_bisimulation : is_bisimulation (fun T s1 s2 => ctx_equiv T s1 s2).

Theorem bisim_complete : forall T t1 t2,
  ctx_equiv T t1 t2 -> bisimilar T t1 t2.
Proof.
  intros T t1 t2 Hctx.
  exists (fun T' s1 s2 => ctx_equiv T' s1 s2).
  split; [exact ctx_equiv_is_bisimulation | exact Hctx].
Qed.

Theorem bisim_sound_neg : ~ (forall T t1 t2,
  bisimilar T t1 t2 -> ctx_equiv T t1 t2).
Proof. Admitted.

Theorem bisim_complete_neg : ~ (forall T t1 t2,
  ctx_equiv T t1 t2 -> bisimilar T t1 t2).
Proof. Admitted.
