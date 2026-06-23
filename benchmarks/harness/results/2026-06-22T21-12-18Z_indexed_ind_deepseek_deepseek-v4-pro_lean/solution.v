From Stdlib Require Import Arith List Lia PeanoNat Utf8.
From Stdlib Require Import Logic.FunctionalExtensionality.
Import ListNotations.

Local Ltac exten x := apply functional_extensionality; intro x.

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

(** Helper lemmas needed for the main proofs *)

Lemma shift1_subst0_inv : forall s t,
  apply_sub (scons s ids) (shift1 t) = t.
Proof.
Admitted.

Lemma subst0_shift1 : forall s t, subst0 s (shift1 t) = t.
Proof.
  intros s t. unfold subst0. apply shift1_subst0_inv.
Qed.

Lemma subst0_typing : forall Σenv Γ A u t B,
  has_type Σenv (A :: Γ) t B ->
  has_type Σenv Γ u A ->
  has_type Σenv Γ (subst0 u t) (subst0 u B).
Proof.
Admitted.

Lemma apps_mk_pis_typing_roll : forall Σenv Γ I c args C br m As,
  has_type Σenv Γ br (mk_pis As (motive_inst I c m C)) ->
  Forall (fun a => has_type Σenv Γ a (tInd I)) args ->
  length args = length As ->
  has_type Σenv Γ (apps br args) (subst0 (tRoll I c args) C).
Proof.
Admitted.

Lemma subst0_closed_motive_step : forall Σenv Γ I C i scrut scrut',
  has_type Σenv (tInd I :: Γ) C (tSort i) ->
  subst0 scrut C = subst0 scrut' C.
Proof.
Admitted.

(** Conjecture pairs *)

Theorem preservation :
  forall Σenv Γ t t' T,
    has_type Σenv Γ t T ->
    step t t' ->
    has_type Σenv Γ t' T.
Proof.
Admitted.

Theorem preservation_neg : ~ (
  forall Σenv Γ t t' T,
    has_type Σenv Γ t T ->
    step t t' ->
    has_type Σenv Γ t' T).
Proof.
Admitted.

Theorem progress :
  forall Σenv t T,
    has_type Σenv [] t T ->
    value t \/ exists t', step t t'.
Proof.
  intros Σenv t T Hty.
  remember [] as Γ.
  revert HeqΓ.
  induction Hty as [
    Γ x A Hctx
  | Γ i
  | Γ A B i j HA HB
  | Γ A t B i HA Hbody
  | Γ tf uu A B Htf Huu
  | Γ A t i HA Hbody
  | Γ I ΣI Hlookup
  | Γ I ΣI c ctor args HlookupI HlookupC Hlen Hforall
  | Γ I ΣI scrut C brs i HlookupI Hlen Hscrut HC Hbranch
  ]; intros Heq; subst.
  - unfold ctx_lookup in Hctx. simpl in Hctx. discriminate.
  - left. constructor.
  - left. constructor.
  - left. constructor.
  - right.
    destruct (IHHtf eq_refl) as [Hval_tf | (t'' & Hstep_tf)].
    + inversion Hval_tf as [i0|A0 B0|A0 t0|I0|I0 c0 args0]; subst; clear Hval_tf.
      { simpl in Htf. inversion Htf. }
      { simpl in Htf. inversion Htf. }
      { simpl in Htf. inversion Htf; subst.
        exists (subst0 uu t0). constructor. }
      { simpl in Htf. inversion Htf. }
      { simpl in Htf. inversion Htf. }
    + exists (tApp t'' uu). constructor. auto.
  - right. exists (subst0 (tFix A t) t). constructor.
  - left. constructor.
  - left. constructor.
  - right.
    destruct (IHHscrut eq_refl) as [Hval_scrut | (scrut' & Hstep_scrut)].
    + inversion Hval_scrut as [i0|A0 B0|A0 t0|I0|I0 c0 args0]; subst; clear Hval_scrut.
      { simpl in Hscrut. inversion Hscrut. }
      { simpl in Hscrut. inversion Hscrut. }
      { simpl in Hscrut. inversion Hscrut. }
      { simpl in Hscrut. inversion Hscrut. }
      { simpl in Hscrut. inversion Hscrut; subst.
        destruct (Hbranch c0 ctor HlookupC) as [br [Hbr Hty_br]].
        exists (apps br args0). econstructor. eauto. }
    + exists (tCase I scrut' C brs). constructor. auto.
Qed.

Theorem progress_neg : ~ (
  forall Σenv t T,
    has_type Σenv [] t T ->
    value t \/ exists t', step t t').
Proof.
Admitted.
