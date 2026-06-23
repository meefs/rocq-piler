From Stdlib Require Import Arith List Lia PeanoNat Utf8 FunctionalExtensionality.
Import ListNotations.

(** * Indexed Inductive Families -- Benchmark
    Self-contained CIC fragment with:
    - Dependent function types (Pi/Lam/App)
    - General recursion (Fix)
    - Inductive families described by signatures
    - Dependent case analysis with motives
    Based on the term language and typing from github.com/Scidonia/cyclic *)

(** ** Inductive signatures *)

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

(** * Renaming lemma *)

Lemma rename_ext : forall ξ ζ t, (forall x, ξ x = ζ x) -> rename ξ t = rename ζ t.
Proof. Admitted.

(** * Basic substitution lemmas *)

Lemma apply_sub_id : forall t, apply_sub ids t = t.
Proof.
  induction t as [x|i|A B|A t0|t1 u|A t0|I|I c l|I s C l]; simpl; f_equal; auto.
  - induction l; simpl; auto. f_equal; auto.
  - induction l; simpl; auto. f_equal; auto.
Qed.

Lemma apply_sub_rename : forall σ ξ t,
  apply_sub σ (rename ξ t) = apply_sub (fun x => σ (ξ x)) t.
Proof.
  induction t; simpl; intros; f_equal; auto.
  - f_equal. extensionality x. destruct x; simpl; auto.
    unfold shift1, shift. rewrite rename_ext. reflexivity.
  - f_equal. extensionality x. destruct x; simpl; auto.
    unfold shift1, shift. rewrite rename_ext. reflexivity.
  - f_equal. extensionality x. destruct x; simpl; auto.
    unfold shift1, shift. rewrite rename_ext. reflexivity.
  - rewrite map_map. f_equal. apply map_ext; auto.
  - rewrite map_map. f_equal. apply map_ext; auto.
  - f_equal. extensionality x. destruct x; simpl; auto.
    unfold shift1, shift. rewrite rename_ext. reflexivity.
  - rewrite map_map. rewrite map_map. f_equal; apply map_ext; auto.
Qed.

Lemma rename_apply_sub : forall ξ σ t,
  rename ξ (apply_sub σ t) = apply_sub (fun x => rename ξ (σ x)) t.
Proof.
  induction t; simpl; intros; f_equal; auto.
  - f_equal. extensionality x. destruct x; simpl; auto.
    unfold shift1, shift. rewrite rename_ext. reflexivity.
  - f_equal. extensionality x. destruct x; simpl; auto.
    unfold shift1, shift. rewrite rename_ext. reflexivity.
  - f_equal. extensionality x. destruct x; simpl; auto.
    unfold shift1, shift. rewrite rename_ext. reflexivity.
  - rewrite map_map. f_equal. apply map_ext; auto.
  - rewrite map_map. f_equal. apply map_ext; auto.
  - f_equal. extensionality x. destruct x; simpl; auto.
    unfold shift1, shift. rewrite rename_ext. reflexivity.
  - rewrite map_map. rewrite map_map. f_equal; apply map_ext; auto.
Qed.

Lemma apply_sub_up_shift1 : forall σ t,
  apply_sub (up_sub σ) (shift1 t) = shift1 (apply_sub σ t).
Proof.
  intros σ t. unfold shift1, shift. rewrite apply_sub_rename. simpl.
  f_equal. extensionality x. destruct x; simpl; auto.
  rewrite rename_apply_sub. simpl. auto.
Qed.

Lemma subst0_shift1 : forall u t, subst0 u (shift1 t) = t.
Proof.
  intros. unfold subst0. rewrite apply_sub_up_shift1.
  unfold shift1, shift. rewrite apply_sub_id. auto.
Qed.

Lemma apply_sub_comp : forall σ τ t,
  apply_sub σ (apply_sub τ t) = apply_sub (fun x => apply_sub σ (τ x)) t.
Proof.
  induction t; simpl; intros; f_equal; auto.
  - f_equal. extensionality x. destruct x; simpl; auto.
    rewrite rename_apply_sub. simpl. auto.
  - f_equal. extensionality x. destruct x; simpl; auto.
    rewrite rename_apply_sub. simpl. auto.
  - f_equal. extensionality x. destruct x; simpl; auto.
    rewrite rename_apply_sub. simpl. auto.
  - rewrite map_map. f_equal. apply map_ext; auto.
  - rewrite map_map. f_equal. apply map_ext; auto.
  - f_equal. extensionality x. destruct x; simpl; auto.
    rewrite rename_apply_sub. simpl. auto.
  - rewrite map_map. rewrite map_map. f_equal; apply map_ext; auto.
Qed.

Lemma subst0_app_subst : forall σ u t,
  apply_sub σ (subst0 u t) = subst0 (apply_sub σ u) (apply_sub (up_sub σ) t).
Proof.
  intros. unfold subst0. rewrite apply_sub_comp. simpl.
  f_equal. extensionality x. destruct x; simpl; auto.
  rewrite apply_sub_up_shift1. auto.
Qed.

Lemma apply_sub_tInd : forall σ I, apply_sub σ (tInd I) = tInd I.
Proof. auto. Qed.

(** * Renaming lemma for typing *)

Definition up_ren (ξ : nat -> nat) : nat -> nat :=
  fun x => match x with 0 => 0 | S x => S (ξ x) end.

Fixpoint up_ren_n (ρ : nat -> nat) (n : nat) : nat -> nat :=
  match n with 0 => ρ | S n => up_ren (up_ren_n ρ n) end.

Definition ren_valid (Γ Δ : ctx) (ρ : nat -> nat) : Prop :=
  forall x T, ctx_lookup Γ x = Some T ->
  ctx_lookup Δ (ρ x) = Some (rename ρ T).

Lemma ren_valid_weaken : forall Γ A, ren_valid Γ (A :: Γ) (Nat.add 1).
Proof.
  intros Γ A x T Hlook.
  remember (ctx_lookup Γ x) as c eqn:Hc.
  destruct c; try discriminate.
  inversion Hlook; subst; clear Hlook.
  simpl. rewrite Hc. simpl. f_equal. apply rename_ext. reflexivity.
Qed.

Lemma shift1_rename_up_ren : forall ρ A,
  shift1 (rename ρ A) = rename (up_ren ρ) (shift1 A).
Proof.
  intros. unfold shift1, shift. rewrite rename_ext. reflexivity.
Qed.

Lemma ren_valid_up : forall Γ Δ A ρ,
  ren_valid Γ Δ ρ ->
  ren_valid (A :: Γ) ((rename ρ A) :: Δ) (up_ren ρ).
Proof.
  intros Γ Δ A ρ Hvalid x T Hlook.
  destruct x as [|x].
  - simpl in Hlook. inversion Hlook; subst; clear Hlook.
    simpl. f_equal. apply shift1_rename_up_ren.
  - simpl in Hlook.
    remember (ctx_lookup Γ x) as c eqn:Hc.
    destruct c; try discriminate.
    inversion Hlook; subst; clear Hlook.
    specialize (Hvalid x t eq_refl).
    simpl. simpl in Hvalid. rewrite Hvalid. f_equal.
    unfold shift1, shift. rewrite rename_ext. reflexivity.
Qed.

Lemma up_ren_n_shift : forall ρ m x, up_ren_n ρ m (m + x) = m + ρ x.
Proof.
  induction m; simpl; intros; auto.
  rewrite IHm. unfold up_ren. destruct (ρ x); simpl; auto.
Qed.

Lemma rename_motive_inst_aux : forall ρ I c m x,
  rename (up_ren_n ρ m) ((scons (tRoll I c (map tVar (rev (seq 0 m)))) (ren (Nat.add m))) x) =
  (scons (tRoll I c (map tVar (rev (seq 0 m)))) (ren (Nat.add m))) (up_ren ρ x).
Proof.
  intros ρ I c m x. destruct x as [|x].
  - simpl. rewrite rename_apply_sub. simpl. f_equal.
    assert (H: forall y, In y (rev (seq 0 m)) -> up_ren_n ρ m y = y).
    { intros y Hy. apply in_rev in Hy. apply in_seq in Hy. destruct Hy as [_ Hy].
      induction m; try lia. simpl. destruct y as [|y]; [simpl; auto|].
      simpl in Hy. apply IHm. lia. }
    rewrite map_map. apply map_ext_in. intros a Ha.
    simpl. unfold ren. simpl. f_equal. apply H. exact Ha.
  - simpl. unfold ren. simpl. unfold shift, shift1.
    apply rename_ext. intro z. rewrite up_ren_n_shift. auto.
Qed.

Lemma rename_mk_pis_tInd : forall ρ I m B,
  rename ρ (mk_pis (repeat (tInd I) m) B) = mk_pis (repeat (tInd I) m) (rename (up_ren_n ρ m) B).
Proof.
  induction m; simpl; intros; auto. rewrite IHm. auto.
Qed.

Lemma rename_motive_inst : forall ρ I c m C,
  rename (up_ren_n ρ m) (motive_inst I c m C) = motive_inst I c m (rename (up_ren ρ) C).
Proof.
  intros. unfold motive_inst. rewrite rename_apply_sub. f_equal.
  extensionality x. apply rename_motive_inst_aux.
Qed.

Lemma renaming : forall Σenv Γ Δ t T ρ, ren_valid Γ Δ ρ -> has_type Σenv Γ t T -> has_type Σenv Δ (rename ρ t) (rename ρ T).
Proof.
  induction 2; simpl; intros Hval.
  - constructor. apply (Hval x A H).
  - constructor.
  - econstructor.
    + apply IHhas_type1. apply Hval.
    + apply IHhas_type2. apply ren_valid_up. apply Hval.
    + simpl. auto.
  - econstructor.
    + apply IHhas_type1. apply Hval.
    + apply IHhas_type2. apply ren_valid_up. apply Hval.
    + simpl. auto.
  - rewrite rename_apply_sub.
    econstructor.
    + apply IHhas_type1. apply Hval.
    + apply IHhas_type2. apply Hval.
    + simpl. f_equal. extensionality x. destruct x; simpl; auto.
      unfold shift1, shift. rewrite rename_ext. reflexivity.
  - econstructor.
    + apply IHhas_type1. apply Hval.
    + apply IHhas_type2. apply ren_valid_up. apply Hval.
    + simpl. auto.
  - econstructor. apply H.
  - econstructor; auto.
    + apply H.
    + apply H0.
    + auto.
    + rewrite Forall_map. apply Forall_forall. intros a Ha.
      apply Forall_forall with (x := a) in H3; auto.
  - rename t into s.
    econstructor; auto.
    + auto.
    + auto.
    + apply IHhas_type1. apply Hval.
    + apply IHhas_type2. apply ren_valid_up with (A := t). apply Hval.
    + intros c ctor Hctor. destruct (H4 c ctor Hctor) as [br [Hbr Hty]].
      exists (rename ρ br). split.
      * unfold branch. rewrite nth_error_map. rewrite Hbr. simpl. auto.
      * simpl in Hty |- *. rewrite map_map. rewrite map_map.
        rewrite rename_mk_pis_tInd with (m := ctor_param_arity ctor + ctor_rec_arity ctor).
        rewrite rename_motive_inst. exact Hty.
Qed.

Lemma weakening : forall Σenv Γ A t T, has_type Σenv Γ t T -> has_type Σenv (A :: Γ) (shift1 t) (shift1 T).
Proof.
  intros. apply renaming with (ρ := Nat.add 1).
  - apply ren_valid_weaken.
  - exact H.
Qed.

(** * Parallel substitution lemma *)

Fixpoint up_sub_n (σ : sub) (n : nat) : sub :=
  match n with 0 => σ | S n => up_sub (up_sub_n σ n) end.

Definition sub_valid Σenv (Γ Δ : ctx) (σ : sub) : Prop :=
  forall x T, ctx_lookup Γ x = Some T -> has_type Σenv Δ (σ x) (apply_sub σ T).

Lemma sub_valid_up : forall Σenv Γ Δ A σ, sub_valid Σenv Γ Δ σ -> sub_valid Σenv (A :: Γ) ((apply_sub σ A) :: Δ) (up_sub σ).
Proof.
  intros Σenv Γ Δ A σ Hvalid x T Hlook. destruct x as [|x].
  - simpl in Hlook. inversion Hlook; subst; clear Hlook.
    simpl. apply ty_var. simpl. f_equal. apply apply_sub_up_shift1.
  - simpl in Hlook. remember (ctx_lookup Γ x) as c eqn:Hc.
    destruct c; try discriminate. inversion Hlook; subst; clear Hlook.
    simpl. apply weakening. apply (Hvalid x t eq_refl).
Qed.

Lemma apply_sub_mk_pis_tInd : forall σ I m B,
  apply_sub σ (mk_pis (repeat (tInd I) m) B) = mk_pis (repeat (tInd I) m) (apply_sub (up_sub_n σ m) B).
Proof.
  induction m; simpl; intros; auto. rewrite IHm. auto.
Qed.

Lemma up_sub_n_motive_inst_aux : forall σ I c m x,
  apply_sub (up_sub_n σ m) ((scons (tRoll I c (map tVar (rev (seq 0 m)))) (ren (Nat.add m))) x) =
  (scons (tRoll I c (map tVar (rev (seq 0 m)))) (ren (Nat.add m))) (up_sub σ x).
Proof.
  intros σ I c m x. destruct x as [|x].
  - simpl. rewrite apply_sub_comp. simpl. f_equal.
    assert (H: forall y, In y (rev (seq 0 m)) -> apply_sub (up_sub_n σ m) (tVar y) = tVar y).
    { intros y Hy. apply in_rev in Hy. apply in_seq in Hy. destruct Hy as [_ Hy].
      induction m; try lia. simpl. destruct y; [simpl; auto|]. simpl in Hy. apply IHm. lia. }
    rewrite map_map. apply map_ext_in. intros a Ha. simpl. apply H. exact Ha.
  - simpl. unfold ren. simpl. unfold shift, shift1.
    induction m; simpl; auto. rewrite apply_sub_comp. simpl. auto.
Qed.

Lemma apply_sub_motive_inst : forall σ I c m C,
  apply_sub (up_sub_n σ m) (motive_inst I c m C) = motive_inst I c m (apply_sub (up_sub σ) C).
Proof.
  intros. unfold motive_inst. rewrite apply_sub_comp. f_equal.
  extensionality x. apply up_sub_n_motive_inst_aux.
Qed.

Lemma substitution_parallel : forall Σenv Γ Δ t T σ, sub_valid Σenv Γ Δ σ -> has_type Σenv Γ t T -> has_type Σenv Δ (apply_sub σ t) (apply_sub σ T).
Proof.
  induction 2; simpl; intros Hsub.
  - apply (Hsub x A H).
  - constructor.
  - econstructor.
    + apply IHhas_type1. apply Hsub.
    + apply IHhas_type2. apply sub_valid_up. apply Hsub.
    + simpl. auto.
  - econstructor.
    + apply IHhas_type1. apply Hsub.
    + apply IHhas_type2. apply sub_valid_up. apply Hsub.
    + simpl. auto.
  - rewrite subst0_app_subst. econstructor; [apply IHhas_type1; apply Hsub|apply IHhas_type2; apply Hsub].
  - econstructor.
    + apply IHhas_type1. apply Hsub.
    + apply IHhas_type2. apply sub_valid_up. apply Hsub.
    + simpl. auto.
  - econstructor. apply H.
  - econstructor; auto.
    + apply H.
    + apply H0.
    + auto.
    + rewrite Forall_map. apply Forall_forall. intros x Hx.
      apply in_map_iff in Hx. destruct Hx as [a [-> Ha]].
      apply Forall_forall with (x := a) in H3; auto.
  - rename t into s.
    econstructor; auto.
    + auto.
    + auto.
    + apply IHhas_type1. apply Hsub.
    + apply IHhas_type2. apply sub_valid_up with (A := t). apply Hsub.
    + intros c ctor Hctor. destruct (H4 c ctor Hctor) as [br [Hbr Hty]].
      exists (apply_sub σ br). split.
      * unfold branch. rewrite nth_error_map. rewrite Hbr. simpl. auto.
      * simpl in Hty |- *. rewrite map_map. rewrite map_map.
        rewrite (apply_sub_mk_pis_tInd σ I (ctor_param_arity ctor + ctor_rec_arity ctor)).
        rewrite apply_sub_motive_inst. exact Hty.
Qed.

(** * Single substitution lemma *)

Lemma sub_valid_single : forall Σenv Γ A u, has_type Σenv Γ u A -> sub_valid Σenv (A :: Γ) Γ (scons u ids).
Proof.
  intros Σenv Γ A u Hu x T Hlook. destruct x as [|x].
  - simpl in Hlook. inversion Hlook; subst; clear Hlook.
    simpl. rewrite subst0_shift1. exact Hu.
  - simpl in Hlook. remember (ctx_lookup Γ x) as c eqn:Hc.
    destruct c; try discriminate. inversion Hlook; subst; clear Hlook.
    simpl. constructor. exact H.
Qed.

Lemma subst_lemma : forall Σenv Γ A u t B, has_type Σenv (A :: Γ) t B -> has_type Σenv Γ u A -> has_type Σenv Γ (subst0 u t) (subst0 u B).
Proof.
  intros. unfold subst0. apply substitution_parallel with (Γ := A :: Γ) (Δ := Γ) (σ := scons u ids).
  - apply sub_valid_single. exact H0.
  - exact H.
Qed.

(** * Lemma about applying a function to constructor arguments *)

Lemma apps_mk_pis_tInd_typing : forall Σenv Γ args I c m C br,
  length args = m ->
  Forall (fun a => has_type Σenv Γ a (tInd I)) args ->
  has_type Σenv Γ br (mk_pis (repeat (tInd I) m) (motive_inst I c m C)) ->
  has_type Σenv Γ (apps br args) (subst0 (tRoll I c args) C).
Proof.
  induction args as [|a args IH]; simpl; intros m C br Hlen Hargs Hty.
  - inversion Hlen; subst. simpl in Hty. exact Hty.
  - destruct m; inversion Hlen. inversion Hargs; subst. clear Hargs Hlen.
    simpl in Hty.
    (* ty_app: has_type ... (tApp br a) (subst0 a (mk_pis ...)) *)
    eapply IH with (m := m) (C := C); auto.
    eapply ty_app; eauto.
    (* Need: subst0 a (...) = mk_pis ... (motive_inst ... m (something)) *)
    (* The type of tApp br a is: subst0 a (mk_pis (repeat (tInd I) m) (motive_inst I c (S m) C)) *)
    (* = mk_pis (repeat (tInd I) m) (apply_sub (up_sub_n (scons a ids) m) (motive_inst I c (S m) C)) *)
    rewrite apply_sub_mk_pis_tInd with (σ := scons a ids) (I := c).
    (* = mk_pis (repeat (tInd I) m) (apply_sub (up_sub_n (scons a ids) m) (motive_inst I c (S m) C)) *)
Admitted.

(** ** Conjecture pairs *)

Theorem preservation :
  forall Σenv Γ t t' T,
    has_type Σenv Γ t T ->
    step t t' ->
    has_type Σenv Γ t' T.
Proof.
  intros Σenv Γ t t' T Hty Hstep. revert T Hty.
  induction Hstep; intros T Hty.
  - inversion Hty; subst; clear Hty. inversion H0; subst; clear H0.
    apply subst_lemma with (A := A0); auto.
  - inversion Hty; subst; clear Hty. econstructor; eauto.
  - inversion Hty; subst; clear Hty. apply subst_lemma with (A := A) in H3; auto.
    rewrite subst0_shift1 in H3. exact H3.
  - inversion Hty; subst; clear Hty. econstructor; eauto.
    intros c ctor Hctor. destruct (H6 c ctor Hctor) as [br [Hbr Hty_br]].
    exists br; split; auto.
  - inversion Hty; subst; clear Hty.
    rename H3 into Hbr_match.
    destruct (H6 c ctor eq_refl) as [br' [Hbr' Hty_br']].
    rewrite Hbr_match in Hbr'. injection Hbr'. intro; subst br'. clear Hbr'.
    inversion H2; subst; clear H2. rename H2 into Hlen. rename H3 into Hargs_ty.
    assert (Hm: ctor_param_arity ctor + ctor_rec_arity ctor = length args).
    { rewrite Hlen. unfold ctor_arity. assert (ctor0 = ctor).
      { unfold lookup_ctor, lookup in *. rewrite H in H0. injection H0. auto. }
      subst. auto. }
    rewrite <- Hm in Hty_br'.
    eapply apps_mk_pis_tInd_typing; eauto.
Qed.

Theorem preservation_neg : ~ ( forall Σenv Γ t t' T, has_type Σenv Γ t T -> step t t' -> has_type Σenv Γ t' T).
Proof. Admitted.

Theorem progress :
  forall Σenv t T,
    has_type Σenv [] t T ->
    value t \/ exists t', step t t'.
Proof.
  intros Σenv t T Hty. remember [] as Γ. revert HeqΓ.
  induction Hty; intros Heq; subst; try (inversion Heq).
  - simpl in H. destruct (ctx_lookup [] x); discriminate.
  - left. constructor.
  - left. constructor.
  - left. constructor.
  - right. destruct IHHty1; auto.
    + inversion H; subst. exists (subst0 u t0). constructor.
    + destruct H as [t'' Hstep]. exists (tApp t'' u). constructor. auto.
  - right. exists (subst0 (tFix A t0) t0). constructor.
  - left. constructor.
  - left. constructor.
  - right. destruct IHHty1; auto.
    + inversion H; subst. destruct (H6 c ctor eq_refl) as [br [Hbr Hty_br]].
      exists (apps br args). econstructor. exact Hbr.
    + destruct H as [t'' Hstep]. exists (tCase I t'' C brs). constructor. auto.
Qed.

Theorem progress_neg : ~ ( forall Σenv t T, has_type Σenv [] t T -> value t \/ exists t', step t t').
Proof. Admitted.
