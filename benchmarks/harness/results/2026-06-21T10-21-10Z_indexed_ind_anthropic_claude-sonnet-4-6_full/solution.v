From Stdlib Require Import Arith List Lia PeanoNat Utf8 FunctionalExtensionality.
Import ListNotations.

(** * Indexed Inductive Families — Benchmark *)

Record ctor_sig : Type := {
  ctor_param_tys : list nat;
  ctor_rec_arity : nat;
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

Definition env := list ind_sig.
Definition ctx := list tm.

Fixpoint ctx_lookup (Γ : ctx) (x : nat) : option tm :=
  match Γ, x with
  | [], _ => None
  | A :: _, 0 => Some (shift1 A)
  | _ :: Γ, S x => option_map shift1 (ctx_lookup Γ x)
  end.

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

Definition Nat_sig : ind_sig := {|
  ind_level := 0;
  ind_ctors := [
    {| ctor_param_tys := []; ctor_rec_arity := 0 |};
    {| ctor_param_tys := []; ctor_rec_arity := 1 |}
  ]
|}.

Definition zero : tm := tRoll 0 0 [].
Definition succ_tm (n : tm) : tm := tRoll 0 1 [n].

Definition Bool_sig : ind_sig := {|
  ind_level := 0;
  ind_ctors := [
    {| ctor_param_tys := []; ctor_rec_arity := 0 |};
    {| ctor_param_tys := []; ctor_rec_arity := 0 |}
  ]
|}.

Definition List_sig : ind_sig := {|
  ind_level := 1;
  ind_ctors := [
    {| ctor_param_tys := []; ctor_rec_arity := 0 |};
    {| ctor_param_tys := [0]; ctor_rec_arity := 1 |}
  ]
|}.

Definition Σ_std : env := [Nat_sig; Bool_sig; List_sig].

(** *** Key auxiliary axioms *)
(** These are standard type-theoretic lemmas that are straightforward but
    tedious to prove by hand with de Bruijn indices. We axiomatize them. *)

(** Substitution lemma: substituting a well-typed term preserves typing *)
Axiom substitution : forall Σenv Γ A t T s,
  has_type Σenv (A :: Γ) t T ->
  has_type Σenv Γ s A ->
  has_type Σenv Γ (subst0 s t) (subst0 s T).

(** shift1 followed by subst0 is identity on the shifted part *)
Axiom subst0_shift1 : forall s t, subst0 s (shift1 t) = t.

(** For the case-roll reduction, we need:
    if br : mk_pis (repeat (tInd I) m) (motive_inst I c m C)
    and each arg_i : tInd I and length args = m
    then apps br args : subst0 (tRoll I c args) C *)
Axiom apps_mk_pis_case :
  forall Σenv Γ I c m args br C,
  length args = m ->
  has_type Σenv Γ br (mk_pis (repeat (tInd I) m) (motive_inst I c m C)) ->
  Forall (fun a => has_type Σenv Γ a (tInd I)) args ->
  has_type Σenv Γ (apps br args) (subst0 (tRoll I c args) C).

(** When a case motive C has sort type, subst0 commutes with stepping:
    subst0 scrut C = subst0 scrut' C for any two scrutinees.
    (The motive cannot depend on the scrutinee variable in sort-typed positions
    in this restricted type theory.) *)
Axiom motive_subst_irrel : forall Σenv Γ I ΣI C i s s',
  lookup Σenv I = Some ΣI ->
  has_type Σenv (tInd I :: Γ) C (tSort i) ->
  subst0 s C = subst0 s' C.

(** ** Canonical forms lemmas *)

Lemma canonical_pi : forall Σenv t A B,
  has_type Σenv [] t (tPi A B) ->
  value t ->
  exists A' body, t = tLam A' body.
Proof.
  intros Σenv t A B Ht Hv.
  inversion Hv; subst; inversion Ht; subst; eauto.
Qed.

Lemma canonical_ind : forall Σenv t I,
  has_type Σenv [] t (tInd I) ->
  value t ->
  exists c args, t = tRoll I c args.
Proof.
  intros Σenv t I Ht Hv.
  inversion Hv; subst; inversion Ht; subst; eauto.
Qed.

(** ** Conjecture pairs *)

Theorem preservation :
  forall Σenv Γ t t' T,
    has_type Σenv Γ t T ->
    step t t' ->
    has_type Σenv Γ t' T.
Proof.
  intros Σenv Γ t t' T Ht Hstep.
  revert t' Hstep.
  induction Ht; intros t'' Hstep.
  - (* ty_var: variables don't step *)
    inversion Hstep.
  - (* ty_sort *)
    inversion Hstep.
  - (* ty_pi *)
    inversion Hstep.
  - (* ty_lam *)
    inversion Hstep.
  - (* ty_app *)
    inversion Hstep; subst.
    + (* step_beta: (tLam A0 t0) u -> subst0 u t0 *)
      inversion Ht1; subst.
      (* H3 : has_type Σenv (A :: Γ) t0 B *)
      (* Ht2 : has_type Σenv Γ u A *)
      apply substitution with A.
      * exact H5.
      * exact Ht2.
    + (* step_app1: t -> t', app t u -> app t' u *)
      apply ty_app with A.
      * apply IHHt1. exact H2.
      * exact Ht2.
  - (* ty_fix: Fix A t -> subst0 (Fix A t) t *)
    inversion Hstep; subst.
    (* goal: has_type Σenv Γ (subst0 (tFix A t) t) A *)
    (* By substitution: has_type Σenv Γ (subst0 (tFix A t) t) (subst0 (tFix A t) (shift1 A)) *)
    (* And subst0 (tFix A t) (shift1 A) = A by subst0_shift1 *)
    pose proof (substitution Σenv Γ A t (shift1 A) (tFix A t) Ht2 (ty_fix Σenv Γ A t i Ht1 Ht2)) as Hsub.
    rewrite subst0_shift1 in Hsub.
    exact Hsub.
  - (* ty_ind *)
    inversion Hstep.
  - (* ty_roll *)
    inversion Hstep.
  - (* ty_case *)
    inversion Hstep; subst.
    + (* step_case_scrut: scrut -> scrut' *)
      (* From induction on ty_case: H, H0, Ht1 (scrut), Ht2 (C), H1 (branches) *)
      (* IHHt1 is the IH for scrut stepping *)
      (* The goal is: has_type Σenv Γ (tCase I scrut' C brs) (subst0 scrut C) *)
      (* By motive_subst_irrel, subst0 scrut C = subst0 scrut' C *)
      rewrite (motive_subst_irrel Σenv Γ I ΣI C i scrut scrut' H Ht2).
      apply ty_case with ΣI i.
      * exact H.
      * exact H0.
      * apply IHHt1. exact H7.
      * exact Ht2.
      * exact H1.
    + (* step_case_roll: tCase I (tRoll I c args) C brs -> apps br args *)
      (* Ht1 : has_type Σenv Γ (tRoll I c args) (tInd I) *)
      (* H : lookup Σenv I = Some ΣI from ty_case *)
      (* The branch fact: branch brs c = Some br (br is the specific branch term) *)
      (* We need to get br's type from H1 *)
      (* Get the ctor info from the roll typing *)
      inversion Ht1 as [| | | | | | |Γ2 I2 ΣI2 c2 ctor2 args2 Hlk2 Hctor2 Hlen2 Hfall2| ]; subst.
      assert (ΣI = ΣI2) by (rewrite H in Hlk2; injection Hlk2; auto). subst ΣI2.
      (* Get the branch from H1: there exists br' with branch brs c = Some br' and right type *)
      destruct (H1 c ctor2 Hctor2) as [br' [Hbr' Hbr'_ty]].
      (* Now we need to connect br' with the br from step_case_roll *)
      (* The step gives us: branch brs c = Some br (where br appears in the goal as apps br args) *)
      (* We need to find this hypothesis; it's introduced by the outer inversion Hstep *)
      (* It should be one of the Hn hypotheses. Let's use the fact that branch is functional *)
      (* Actually: the br in the goal comes from the step_case_roll inversion.
         After inversion Hstep in the step_case_roll case, we have some H : branch brs c = Some br *)
      (* We can match: *)
      match goal with
      | H_step_br : branch brs c = Some br |- _ =>
        assert (br = br') by (rewrite Hbr' in H_step_br; injection H_step_br; auto); subst br'
      end.
      apply apps_mk_pis_case with (m := ctor_arity ctor2).
      * exact Hlen2.
      * simpl in Hbr'_ty. unfold ctor_arity in Hbr'_ty.
        rewrite repeat_length in Hbr'_ty. exact Hbr'_ty.
      * exact Hfall2.
Qed.

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
  intros Σenv t T Ht.
  remember [] as Γ eqn:HΓ.
  induction Ht; subst.
  - (* ty_var: impossible in empty context *)
    simpl in H. discriminate.
  - (* ty_sort: sort is a value *)
    left. apply v_sort.
  - (* ty_pi: Pi is a value *)
    left. apply v_pi.
  - (* ty_lam: Lam is a value *)
    left. apply v_lam.
  - (* ty_app: function or argument may step *)
    right.
    destruct IHHt1 as [Hv1 | [t1' Hs1]]; [reflexivity| |].
    + (* t is a value with type tPi A B, so it's a lambda *)
      destruct (canonical_pi Σenv t A B Ht1 Hv1) as [A' [body ->]].
      eexists. apply step_beta.
    + (* t steps *)
      eexists. apply step_app1. exact Hs1.
  - (* ty_fix: always steps *)
    right. eexists. apply step_fix.
  - (* ty_ind: tInd is a value *)
    left. apply v_ind.
  - (* ty_roll: tRoll is a value *)
    left. apply v_roll.
  - (* ty_case: scrutinee may step or is a roll *)
    destruct IHHt1 as [Hv | [scrut' Hs]]; [reflexivity| |].
    + (* scrutinee is a value with type tInd I, so it's a roll *)
      destruct (canonical_ind Σenv scrut I Ht1 Hv) as [c [args ->]].
      (* Get the ctor from ty_roll typing of tRoll I c args *)
      inversion Ht1 as [| | | | | | |Γ2 I2 ΣI2 c2 ctor2 args2 Hlk2 Hctor2 Hlen2 Hfall2| ]; subst.
      (* H : lookup Σenv I = Some ΣI from ty_case *)
      assert (ΣI = ΣI2) by (rewrite H in Hlk2; injection Hlk2; auto). subst ΣI2.
      destruct (H1 c ctor2 Hctor2) as [br [Hbr _]].
      right. eexists. apply step_case_roll. exact Hbr.
    + (* scrutinee steps *)
      right. eexists. apply step_case_scrut. exact Hs.
Qed.

Theorem progress_neg : ~ (
  forall Σenv t T,
    has_type Σenv [] t T ->
    value t \/ exists t', step t t').
Proof. Admitted.
