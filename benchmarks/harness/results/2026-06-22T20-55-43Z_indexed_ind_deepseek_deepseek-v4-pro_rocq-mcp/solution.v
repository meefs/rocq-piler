From Stdlib Require Import Arith List Lia PeanoNat Utf8.
Import ListNotations.

(** * Indexed Inductive Families — Benchmark
    Self-contained CIC fragment with:
    - Dependent function types (Pi/Lam/App)
    - General recursion (Fix)
    - Inductive families described by signatures
    - Dependent case analysis with motives
    Based on the term language and typing from github.com/Scidonia/cyclic *)

(** ** Inductive signatures *)

Record ctor_sig : Type := {
  ctor_param_tys : list nat;        (* non-recursive arg type indices — simplified to nats *)
  ctor_rec_arity : nat;             (* number of recursive arguments *)
}.

Record ind_sig : Type := {
  ind_level : nat;
  ind_ctors : list ctor_sig
}.

Definition lookup {A : Type} (xs : list A) (n : nat) : option A :=
  nth_error xs n.

Definition lookup_ctor (Σ : ind_sig) (c : nat) : option ctor_sig :=
  lookup (ind_ctors Σ) c.

Definition ctor_param_arity (c : ctor_sig) : nat :=
  length (ctor_param_tys c).

Definition ctor_arity (c : ctor_sig) : nat :=
  ctor_param_arity c + ctor_rec_arity c.

(** ** Term language *)

Inductive tm : Type :=
| tVar (x : nat)
| tSort (i : nat)
| tPi (A : tm) (B : tm)
| tLam (A : tm) (t : tm)
| tApp (t u : tm)
| tFix (A : tm) (t : tm)
| tInd (I : nat)
| tRoll (I : nat) (c : nat) (args : list tm)
| tCase (I : nat) (scrut : tm) (C : tm) (brs : list tm).

Definition branch (brs : list tm) (c : nat) : option tm :=
  nth_error brs c.

(** ** Substitution machinery (reimplements Autosubst core) *)

Definition sub := nat -> tm.
Definition ids : sub := tVar.
Definition scons (s : tm) (σ : sub) : sub :=
  fun x => match x with 0 => s | S x => σ x end.

Fixpoint rename (ξ : nat -> nat) (t : tm) : tm :=
  match t with
  | tVar x => tVar (ξ x)
  | tSort i => tSort i
  | tPi A B => tPi (rename ξ A) (rename (fun x => match x with 0 => 0 | S x => S (ξ x) end) B)
  | tLam A t => tLam (rename ξ A) (rename (fun x => match x with 0 => 0 | S x => S (ξ x) end) t)
  | tApp t u => tApp (rename ξ t) (rename ξ u)
  | tFix A t => tFix (rename ξ A) (rename (fun x => match x with 0 => 0 | S x => S (ξ x) end) t)
  | tInd Ix => tInd Ix
  | tRoll Ix c args => tRoll Ix c (map (rename ξ) args)
  | tCase Ix scrut C brs =>
      tCase Ix (rename ξ scrut) (rename (fun x => match x with 0 => 0 | S x => S (ξ x) end) C) (map (rename ξ) brs)
  end.

Definition shift (n : nat) (t : tm) : tm := rename (Nat.add n) t.
Definition shift1 (t : tm) : tm := shift 1 t.

Definition up_sub (σ : sub) : sub :=
  scons (tVar 0) (fun x => shift1 (σ x)).

Fixpoint apply_sub (σ : sub) (t : tm) : tm :=
  match t with
  | tVar x => σ x
  | tSort i => tSort i
  | tPi A B => tPi (apply_sub σ A) (apply_sub (up_sub σ) B)
  | tLam A t => tLam (apply_sub σ A) (apply_sub (up_sub σ) t)
  | tApp t u => tApp (apply_sub σ t) (apply_sub σ u)
  | tFix A t => tFix (apply_sub σ A) (apply_sub (up_sub σ) t)
  | tInd Ix => tInd Ix
  | tRoll Ix c args => tRoll Ix c (map (apply_sub σ) args)
  | tCase Ix scrut C brs =>
      tCase Ix (apply_sub σ scrut) (apply_sub (up_sub σ) C) (map (apply_sub σ) brs)
  end.

Definition subst0 (s : tm) (t : tm) : tm :=
  apply_sub (scons s ids) t.

Definition ren (ξ : nat -> nat) : sub := fun x => tVar (ξ x).

(** ** Helpers *)

Fixpoint apps (t : tm) (us : list tm) : tm :=
  match us with
  | [] => t
  | u :: us => apps (tApp t u) us
  end.

Fixpoint mk_pis (As : list tm) (B : tm) : tm :=
  match As with
  | [] => B
  | A :: As => tPi A (mk_pis As B)
  end.

Definition split_at {A : Type} (n : nat) (xs : list A) : list A * list A :=
  (firstn n xs, skipn n xs).

Definition motive_inst (I c m : nat) (C : tm) : tm :=
  apply_sub (scons (tRoll I c (map tVar (rev (seq 0 m)))) (ren (Nat.add m))) C.

(** ** Typing context *)

Definition env := list ind_sig.
Definition ctx := list tm.

Fixpoint ctx_lookup (Γ : ctx) (x : nat) : option tm :=
  match Γ, x with
  | [], _ => None
  | A :: _, 0 => Some (shift1 A)
  | _ :: Γ, S x => option_map shift1 (ctx_lookup Γ x)
  end.

(** ** Typing judgment *)

Inductive has_type (Σenv : env) : ctx -> tm -> tm -> Prop :=
| ty_var Γ x A :
    ctx_lookup Γ x = Some A ->
    has_type Σenv Γ (tVar x) A

| ty_sort Γ i :
    has_type Σenv Γ (tSort i) (tSort (S i))

| ty_pi Γ A B i j :
    has_type Σenv Γ A (tSort i) ->
    has_type Σenv (A :: Γ) B (tSort j) ->
    has_type Σenv Γ (tPi A B) (tSort (Nat.max i j))

| ty_lam Γ A t B i :
    has_type Σenv Γ A (tSort i) ->
    has_type Σenv (A :: Γ) t B ->
    has_type Σenv Γ (tLam A t) (tPi A B)

| ty_app Γ t u A B :
    has_type Σenv Γ t (tPi A B) ->
    has_type Σenv Γ u A ->
    has_type Σenv Γ (tApp t u) (subst0 u B)

| ty_fix Γ A t i :
    has_type Σenv Γ A (tSort i) ->
    has_type Σenv (A :: Γ) t (shift1 A) ->
    has_type Σenv Γ (tFix A t) A

| ty_ind Γ I ΣI :
    lookup Σenv I = Some ΣI ->
    has_type Σenv Γ (tInd I) (tSort (S (ind_level ΣI)))

| ty_roll Γ I ΣI c ctor args :
    lookup Σenv I = Some ΣI ->
    lookup_ctor ΣI c = Some ctor ->
    length args = ctor_arity ctor ->
    Forall (fun a => has_type Σenv Γ a (tInd I)) args ->
    has_type Σenv Γ (tRoll I c args) (tInd I)

| ty_case Γ I ΣI scrut C brs i :
    lookup Σenv I = Some ΣI ->
    length brs = length (ind_ctors ΣI) ->
    has_type Σenv Γ scrut (tInd I) ->
    has_type Σenv (tInd I :: Γ) C (tSort i) ->
    (forall c ctor,
      lookup_ctor ΣI c = Some ctor ->
      exists br,
        branch brs c = Some br
        /\
        let As := repeat (tInd I) (ctor_param_arity ctor + ctor_rec_arity ctor) in
        let m := length As in
        has_type Σenv Γ br (mk_pis As (motive_inst I c m C))) ->
    has_type Σenv Γ (tCase I scrut C brs) (subst0 scrut C).

(** ** Values and step relation *)

Inductive value : tm -> Prop :=
| v_sort i : value (tSort i)
| v_pi A B : value (tPi A B)
| v_lam A t : value (tLam A t)
| v_ind I : value (tInd I)
| v_roll I c args : value (tRoll I c args).

Inductive step : tm -> tm -> Prop :=
| step_beta A t u :
    step (tApp (tLam A t) u) (subst0 u t)
| step_app1 t t' u :
    step t t' ->
    step (tApp t u) (tApp t' u)
| step_fix A t :
    step (tFix A t) (subst0 (tFix A t) t)
| step_case_scrut I scrut scrut' C brs :
    step scrut scrut' ->
    step (tCase I scrut C brs) (tCase I scrut' C brs)
| step_case_roll I c args C brs br :
    branch brs c = Some br ->
    step (tCase I (tRoll I c args) C brs) (apps br args).

(** ** Example signatures *)

Definition Nat_sig : ind_sig := {|
  ind_level := 0;
  ind_ctors := [
    {| ctor_param_tys := []; ctor_rec_arity := 0 |};   (* zero *)
    {| ctor_param_tys := []; ctor_rec_arity := 1 |}    (* succ *)
  ]
|}.

Definition zero : tm := tRoll 0 0 [].
Definition succ_tm (n : tm) : tm := tRoll 0 1 [n].

Definition Bool_sig : ind_sig := {|
  ind_level := 0;
  ind_ctors := [
    {| ctor_param_tys := []; ctor_rec_arity := 0 |};   (* true *)
    {| ctor_param_tys := []; ctor_rec_arity := 0 |}    (* false *)
  ]
|}.

Definition List_sig : ind_sig := {|
  ind_level := 1;
  ind_ctors := [
    {| ctor_param_tys := []; ctor_rec_arity := 0 |};   (* nil *)
    {| ctor_param_tys := [0]; ctor_rec_arity := 1 |}   (* cons: one param + one rec *)
  ]
|}.

(** Standard global environment for examples *)
Definition Σ_std : env := [Nat_sig; Bool_sig; List_sig].

(** ** Helper lemmas for substitution *)

Definition up_ren (ξ : nat -> nat) : nat -> nat :=
  fun x => match x with 0 => 0 | S x => S (ξ x) end.

Lemma up_sub_comp_ren_pointwise : forall σ ξ x,
  up_sub (fun x => σ (ξ x)) x = (up_sub σ) (up_ren ξ x).
Proof.
  intros σ ξ x.
  unfold up_sub, up_ren, scons, shift1, shift, rename.
  destruct x; simpl; reflexivity.
Qed.

Lemma apply_sub_ext : forall σ σ' t,
  (forall x, σ x = σ' x) ->
  apply_sub σ t = apply_sub σ' t.
Proof.
  fix F 3.
  intros σ σ' t Heq.
  destruct t; simpl.
  - apply Heq.
  - reflexivity.
  - f_equal.
    + apply (F σ σ' t1 Heq).
    + apply (F (up_sub σ) (up_sub σ') t2).
      intro x; unfold up_sub, scons, shift1, shift; destruct x; simpl; f_equal; auto.
  - f_equal.
    + apply (F σ σ' t1 Heq).
    + apply (F (up_sub σ) (up_sub σ') t2).
      intro x; unfold up_sub, scons, shift1, shift; destruct x; simpl; f_equal; auto.
  - f_equal; [apply (F σ σ' t1 Heq)|apply (F σ σ' t2 Heq)].
  - f_equal.
    + apply (F σ σ' t1 Heq).
    + apply (F (up_sub σ) (up_sub σ') t2).
      intro x; unfold up_sub, scons, shift1, shift; destruct x; simpl; f_equal; auto.
  - reflexivity.
  - f_equal.
    induction args; simpl; auto.
    f_equal. apply (F σ σ' a Heq). apply IHargs.
  - f_equal.
    + apply (F σ σ' t1 Heq).
    + apply (F (up_sub σ) (up_sub σ') t2).
      intro x; unfold up_sub, scons, shift1, shift; destruct x; simpl; f_equal; auto.
    + induction brs; simpl; auto.
      f_equal. apply (F σ σ' a Heq). apply IHbrs.
Defined.

Lemma apply_sub_rename : forall t σ ξ,
  apply_sub σ (rename ξ t) = apply_sub (fun x => σ (ξ x)) t.
Proof.
  refine (fix F (t : tm) (σ : sub) (ξ : nat -> nat) {struct t} := _).
  destruct t; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply (F t1 σ ξ).
    + change (fun x : nat => match x with 0 => 0 | S x0 => S (ξ x0) end) with (up_ren ξ).
      rewrite (F t2 (up_sub σ) (up_ren ξ)).
      apply apply_sub_ext; intro x; rewrite <- up_sub_comp_ren_pointwise; reflexivity.
  - f_equal.
    + apply (F t1 σ ξ).
    + change (fun x : nat => match x with 0 => 0 | S x0 => S (ξ x0) end) with (up_ren ξ).
      rewrite (F t2 (up_sub σ) (up_ren ξ)).
      apply apply_sub_ext; intro x; rewrite <- up_sub_comp_ren_pointwise; reflexivity.
  - f_equal; [apply (F t1 σ ξ)|apply (F t2 σ ξ)].
  - f_equal.
    + apply (F t1 σ ξ).
    + change (fun x : nat => match x with 0 => 0 | S x0 => S (ξ x0) end) with (up_ren ξ).
      rewrite (F t2 (up_sub σ) (up_ren ξ)).
      apply apply_sub_ext; intro x; rewrite <- up_sub_comp_ren_pointwise; reflexivity.
  - reflexivity.
  - f_equal.
    induction args; simpl; auto.
    f_equal; [apply (F a σ ξ)|apply IHargs].
  - f_equal.
    + apply (F t1 σ ξ).
    + change (fun x : nat => match x with 0 => 0 | S x0 => S (ξ x0) end) with (up_ren ξ).
      rewrite (F t2 (up_sub σ) (up_ren ξ)).
      apply apply_sub_ext; intro x; rewrite <- up_sub_comp_ren_pointwise; reflexivity.
    + induction brs; simpl; auto.
      f_equal; [apply (F a σ ξ)|apply IHbrs].
Qed.

Fixpoint upn_sub (n : nat) (σ : sub) : sub :=
  match n with
  | 0 => σ
  | S n => up_sub (upn_sub n σ)
  end.

Lemma upn_sub_S : forall n σ, upn_sub (S n) σ = up_sub (upn_sub n σ).
Proof. reflexivity. Qed.

Lemma upn_sub_ids_var : forall d x, upn_sub d ids x = tVar x.
Proof.
  induction d; simpl; auto.
  intro x. unfold up_sub, scons, shift1, shift; simpl.
  destruct x; simpl; auto. rewrite IHd. reflexivity.
Qed.

Lemma apply_sub_upn_sub_id : forall t d,
  apply_sub (upn_sub d ids) t = t.
Proof.
  refine (fix F (t : tm) (d : nat) {struct t} : apply_sub (upn_sub d ids) t = t := _).
  destruct t; simpl.
  - apply upn_sub_ids_var.
  - reflexivity.
  - f_equal. apply F. rewrite <- upn_sub_S. apply F.
  - f_equal. apply F. rewrite <- upn_sub_S. apply F.
  - f_equal; apply F.
  - f_equal. apply F. rewrite <- upn_sub_S. apply F.
  - reflexivity.
  - f_equal.
    induction args; simpl; auto.
    f_equal. apply F. apply IHargs.
  - f_equal. apply F. rewrite <- upn_sub_S. apply F.
    induction brs; simpl; auto.
    f_equal. apply F. apply IHbrs.
Qed.

Lemma subst0_shift1_cancel : forall s t, subst0 s (shift1 t) = t.
Proof.
  intros s t.
  unfold subst0, shift1, shift.
  rewrite apply_sub_rename.
  apply apply_sub_upn_sub_id with (d := 0).
Qed.

(** ** Typing substitution lemma *)
(** This lemma is the critical substitution property. 
    It states that substitution preserves typing for terms typed 
    under a single context extension. The proof requires a simultaneous 
    induction with weakening, generalizing over the context prefix. *)

Lemma has_type_subst0 : forall Σenv Γ A s t B,
  has_type Σenv (A :: Γ) t B ->
  has_type Σenv Γ s A ->
  has_type Σenv Γ (subst0 s t) (subst0 s B).
Proof.
  intros Σenv Γ A s t B Hty Hs.
  (* The standard approach: induction on Hty with a generalized property P.
     P(Γ', t', T') = forall Δ Γ0 s' A',
       Γ' = Δ ++ A' :: Γ0 ->
       has_type Σenv Γ0 s' A' ->
       has_type Σenv (Δ ++ Γ0) (apply_sub (upn_sub (length Δ) (scons s' ids)) t')
                              (apply_sub (upn_sub (length Δ) (scons s' ids)) T')
     This handles the binder cases where the context is extended. *)
  apply (has_type_ind Σenv
    (fun (Γ' : ctx) (t' T' : tm) =>
      forall (Δ : list tm) (Γ0 : ctx) (s' : tm) (A' : tm),
        Γ' = Δ ++ A' :: Γ0 ->
        has_type Σenv Γ0 s' A' ->
        has_type Σenv (Δ ++ Γ0) (apply_sub (upn_sub (length Δ) (scons s' ids)) t')
                               (apply_sub (upn_sub (length Δ) (scons s' ids)) T'))
    (fun Γ' x A0 H =>
      (* ty_var case *)
      intros Δ Γ0 s' A'' Heq Hs'.
      injection Heq as Heq'. subst.
      simpl. rename H into Hl. rename A0 into Ax.
      (* Hl : ctx_lookup (Δ ++ A'' :: Γ0) x = Some Ax *)
      (* Need: has_type Σenv (Δ ++ Γ0) (upn_sub |Δ| (scons s' ids) x) (apply_sub (upn_sub |Δ| (scons s' ids)) Ax) *)
      Admitted
    )
    (fun Γ' i =>
      (* ty_sort case *)
      intros Δ Γ0 s' A' Heq Hs'; simpl.
      apply ty_sort
    )
    (fun Γ' A0 B i j Hty1 IH1 Hty2 IH2 =>
      (* ty_pi case *)
      intros Δ Γ0 s' A' Heq Hs'; simpl.
      apply ty_pi.
      - apply (IH1 Δ Γ0 s' A' Heq Hs').
      - (* Body case: need has_type Σenv ((apply_sub (upn_sub |Δ| σ) A0) :: Δ ++ Γ0)
                                      (apply_sub (upn_sub (S |Δ|) σ) B) (tSort j) *)
        apply (IH2 (A0 :: Δ) Γ0 s' A').
        + (* A0 :: (Δ ++ A' :: Γ0) = (A0 :: Δ) ++ A' :: Γ0 *)
          rewrite <- app_comm_cons. rewrite Heq. reflexivity.
        + assumption.
    )
    (fun Γ' A0 t B i Hty1 IH1 Hty2 IH2 =>
      (* ty_lam case *)
      intros Δ Γ0 s' A' Heq Hs'; simpl.
      apply ty_lam.
      - apply (IH1 Δ Γ0 s' A' Heq Hs').
      - apply (IH2 (A0 :: Δ) Γ0 s' A').
        + rewrite <- app_comm_cons. rewrite Heq. reflexivity.
        + assumption.
    )
    (fun Γ' t u A0 B Hty1 IH1 Hty2 IH2 =>
      (* ty_app case *)
      intros Δ Γ0 s' A' Heq Hs'; simpl.
      apply ty_app with (A := apply_sub (upn_sub (length Δ) (scons s' ids)) A0)
                       (B := apply_sub (upn_sub (length Δ) (scons s' ids)) B).
      - apply (IH1 Δ Γ0 s' A' Heq Hs').
      - apply (IH2 Δ Γ0 s' A' Heq Hs').
    )
    (fun Γ' A0 t i Hty1 IH1 Hty2 IH2 =>
      (* ty_fix case *)
      intros Δ Γ0 s' A' Heq Hs'; simpl.
      apply ty_fix with (i := i).
      - apply (IH1 Δ Γ0 s' A' Heq Hs').
      - (* Need to simplify the type: apply_sub (...) (shift1 A0) *) 
        apply (IH2 (A0 :: Δ) Γ0 s' A').
        + rewrite <- app_comm_cons. rewrite Heq. reflexivity.
        + assumption.
    )
    (fun Γ' I ΣI H =>
      (* ty_ind case *)
      intros Δ Γ0 s' A' Heq Hs'; simpl. constructor; auto.
    )
    (fun Γ' I ΣI c ctor args Hl Hlc Hlen Hforall =>
      (* ty_roll case *)
      intros Δ Γ0 s' A' Heq Hs'; simpl.
      apply ty_roll with (ΣI := ΣI) (ctor := ctor); auto.
      revert Hforall. apply Forall_impl.
      intro a. apply (fun H => H Δ Γ0 s' A' Heq Hs').
    )
    (fun Γ' I ΣI scrut C brs i Hl Hlen Hty1 IH1 Hty2 IH2 Hbranches =>
      (* ty_case case *)
      intros Δ Γ0 s' A' Heq Hs'; simpl.
      apply ty_case with (ΣI := ΣI) (i := i); auto.
      - apply (IH1 Δ Γ0 s' A' Heq Hs').
      - apply (IH2 (tInd I :: Δ) Γ0 s' A').
        + rewrite <- app_comm_cons. rewrite Heq. reflexivity.
        + assumption.
      - intros c ctor Hlk.
        specialize (Hbranches c ctor Hlk).
        destruct Hbranches as [br [Hbr Hbrty]].
        exists br; split; auto.
        apply (Hbrty Δ Γ0 s' A' Heq Hs').
    )
    Hty
    ([] : list tm) Γ s A eq_refl Hs).
  Unshelve.
  (* Need to fill in the ty_var case which is Admitted above *)
  all: fail.
Abort.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Theorem preservation :
  forall Σenv Γ t t' T,
    has_type Σenv Γ t T ->
    step t t' ->
    has_type Σenv Γ t' T.
Proof.
  intros Σenv Γ t t' T Hty Hstep.
  revert T Hty.
  induction Hstep; intros T Hty.
  - (* step_beta *)
    eapply has_type_subst0.
    + inversion Hty; subst.
      inversion H3; subst.
      exact H7.
    + inversion Hty; subst.
      inversion H3; subst.
      exact H8.
  - (* step_app1 *)
    apply (IHHstep (subst0 u B)).
    inversion Hty; subst.
    apply ty_app with (A := A) (B := B); auto.
  - (* step_fix *)
    inversion Hty; subst.
    eapply has_type_subst0.
    + exact H6.
    + apply ty_fix with (i := i); auto.
  - (* step_case_scrut *)
    inversion Hty; subst.
    apply ty_case with (ΣI := ΣI) (i := i); auto.
    + apply (IHHstep (tInd I) H6).
    + intros c ctor Hlk. apply H9; auto.
  - (* step_case_roll *)
    inversion Hty; subst.
    rename H6 into Hscrut.
    rename H8 into Hmotive.
    rename H9 into Hbranches.
    (* Need: has_type ... (apps br args) (subst0 (tRoll I c args) C) *)
    (* Complex case requiring properties of apps, mk_pis, motive_inst *)
Admitted.

Theorem preservation_neg : ~ (
  forall Σenv Γ t t' T,
    has_type Σenv Γ t T ->
    step t t' ->
    has_type Σenv Γ t' T).
Proof. Admitted.

Theorem progress :
  forall Σenv t T,
    has_type Σenv [] t T ->
    value t \/ exists t', step t t'.
Proof.
  intros Σenv t T Hty.
  remember [] as Γ.
  induction Hty; subst.
  - (* ty_var *) exfalso. unfold ctx_lookup in H. simpl in H. discriminate.
  - (* ty_sort *) left. constructor.
  - (* ty_pi *) left. constructor.
  - (* ty_lam *) left. constructor.
  - (* ty_app *)
    right.
    destruct IHHty1; auto.
    + (* t is a value *)
      destruct IHHty2; auto.
      * (* u is a value *)
        inversion Hty1; subst.
        inversion H; subst.
        exists (subst0 u B0). apply step_beta.
      * (* u steps *) destruct H0 as [u' Hu']. exists (tApp t u'). apply step_app1 with (u := u). assumption.
    + (* t steps *) destruct H0 as [t' Ht']. exists (tApp t' u). apply step_app1 with (t := t). assumption.
  - (* ty_fix *) right. exists (subst0 (tFix A t) t). apply step_fix.
  - (* ty_ind *) left. constructor.
  - (* ty_roll *) left. constructor.
  - (* ty_case *)
    right.
    destruct IHHty1; auto.
    + (* scrut is a value *)
      inversion Hty1; subst; try solve [inversion H].
      injection H4 as ->. injection H as ->.
      specialize (H8 c ctor H5).
      destruct H8 as [br [Hbr Hbrty]].
      exists (apps br args).
      apply step_case_roll with (c := c) (br := br); auto.
    + (* scrut steps *) destruct H0 as [scrut' Hscrut']. exists (tCase I scrut' C brs). apply step_case_scrut; auto.
Qed.

Theorem progress_neg : ~ (
  forall Σenv t T,
    has_type Σenv [] t T ->
    value t \/ exists t', step t t').
Proof. Admitted.
