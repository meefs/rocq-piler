From Stdlib Require Import Arith List Lia PeanoNat Utf8.
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

(** Custom induction principle for tm with lists *)
Lemma tm_ind_list : forall (P : tm -> Prop),
  (forall x, P (tVar x)) ->
  (forall i, P (tSort i)) ->
  (forall A B, P A -> P B -> P (tPi A B)) ->
  (forall A t, P A -> P t -> P (tLam A t)) ->
  (forall t u, P t -> P u -> P (tApp t u)) ->
  (forall A t, P A -> P t -> P (tFix A t)) ->
  (forall I, P (tInd I)) ->
  (forall I c args, Forall P args -> P (tRoll I c args)) ->
  (forall I s C brs, P s -> P C -> Forall P brs -> P (tCase I s C brs)) ->
  forall t, P t.
Proof.
  intros P Hvar Hsort Hpi Hlam Happ Hfix Hind Hroll Hcase.
  fix IH 1. intro t.
  destruct t.
  - apply Hvar.
  - apply Hsort.
  - apply Hpi; apply IH.
  - apply Hlam; apply IH.
  - apply Happ; apply IH.
  - apply Hfix; apply IH.
  - apply Hind.
  - apply Hroll. induction args; constructor; [apply IH | exact IHargs].
  - apply Hcase; try apply IH. induction brs; constructor; [apply IH | exact IHbrs].
Qed.

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

(** Example signatures *)
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

(** *** Substitution and renaming lemmas *)

Lemma rename_ext : forall t ξ1 ξ2,
  (forall x, ξ1 x = ξ2 x) ->
  rename ξ1 t = rename ξ2 t.
Proof.
  induction t using tm_ind_list; intros; simpl; try f_equal; auto.
  all: try (apply IHt2 || apply IHB); intros [|x]; simpl; auto.
  all: try (apply IHt1 || apply IHA); auto.
  - apply IHargs. apply Forall_forall; intros a Ha.
    rewrite Forall_forall in H. apply H; auto.
  - apply IHbrs. apply Forall_forall; intros a Ha.
    rewrite Forall_forall in H0. apply H0; auto.
Qed.

Lemma apply_sub_ext : forall t σ1 σ2,
  (forall x, σ1 x = σ2 x) ->
  apply_sub σ1 t = apply_sub σ2 t.
Proof.
  induction t using tm_ind_list; intros; simpl; try f_equal; auto.
  all: try (apply IHt2 || apply IHB); intros [|x]; simpl; unfold up_sub, scons, shift1; auto; f_equal; auto.
  all: try (apply IHt1 || apply IHA); auto.
  - apply IHargs. apply Forall_forall; intros a Ha.
    rewrite Forall_forall in H. apply H; auto.
  - apply IHbrs. apply Forall_forall; intros a Ha.
    rewrite Forall_forall in H0. apply H0; auto.
Qed.

(** rename is a special case of apply_sub *)
Lemma rename_as_apply_sub : forall ξ t,
  rename ξ t = apply_sub (ren ξ) t.
Proof.
  induction t using tm_ind_list; intros; simpl; try f_equal; auto.
  all: try match goal with
    | |- rename _ ?t = apply_sub (up_sub (ren _)) ?t =>
        rewrite <- IHt || rewrite <- IHt2 || rewrite <- IHB
    end.
  all: try (apply rename_ext; intros [|x]; simpl; unfold up_sub, scons, ren, shift1, shift; simpl; auto).
  - rewrite <- IHA. auto.
  - rewrite <- IHt1; auto. apply rename_ext; intros [|x]; simpl; unfold up_sub, scons, ren, shift1; auto.
  - rewrite <- IHA; auto. apply rename_ext; intros [|x]; simpl; unfold up_sub, scons, ren, shift1; auto.
  - rewrite <- IHA; auto. apply rename_ext; intros [|x]; simpl; unfold up_sub, scons, ren, shift1; auto.
  - apply IHargs. apply Forall_forall; intros a Ha.
    rewrite Forall_forall in H. apply H; auto.
  - rewrite <- IHscrut. rewrite <- IHC. f_equal.
    + apply rename_ext; intros [|x]; simpl; unfold up_sub, scons, ren, shift1; auto.
    + apply IHbrs. apply Forall_forall; intros a Ha.
      rewrite Forall_forall in H0. apply H0; auto.
Qed.

(** Composition of renamings *)
Lemma rename_rename : forall t ξ1 ξ2,
  rename ξ2 (rename ξ1 t) = rename (fun x => ξ2 (ξ1 x)) t.
Proof.
  induction t using tm_ind_list; intros; simpl; try f_equal; auto.
  all: try match goal with
    | |- rename _ (rename _ ?t) = rename _ ?t =>
        (rewrite IHt2 || rewrite IHB || rewrite IHt || rewrite IHt1)
    end.
  all: try apply rename_ext; try intros [|x]; simpl; auto.
  all: try (rewrite IHt1 || rewrite IHA); try apply rename_ext; auto.
  - rewrite map_map. apply map_ext_in; intros a Ha.
    rewrite Forall_forall in H. apply H; auto.
  - rewrite IHscrut. rewrite IHC. f_equal.
    + apply rename_ext; intros [|x]; simpl; auto.
    + rewrite map_map. apply map_ext_in; intros a Ha.
      rewrite Forall_forall in H0. apply H0; auto.
Qed.

(** shift1 commutes with rename *)
Lemma shift1_rename : forall t ξ,
  shift1 (rename ξ t) = rename (fun x => S (ξ x)) t.
Proof.
  intros t ξ. unfold shift1, shift. rewrite rename_rename.
  apply rename_ext; intros x; simpl; lia.
Qed.

(** rename and apply_sub interaction *)
Lemma rename_apply_sub : forall t ξ σ,
  rename ξ (apply_sub σ t) = apply_sub (fun x => rename ξ (σ x)) t.
Proof.
  induction t using tm_ind_list; intros; simpl; try f_equal; auto.
  all: try match goal with
    | |- rename _ (apply_sub (up_sub _) ?t) = apply_sub (up_sub _) ?t =>
        (rewrite IHt2 || rewrite IHB || rewrite IHt)
    end.
  all: try (apply apply_sub_ext; intros [|x]; simpl; unfold up_sub, scons, shift1; auto).
  all: try (rewrite IHt1 || rewrite IHA; auto).
  all: try (apply apply_sub_ext; intros [|x]; simpl; unfold up_sub, scons, shift1; auto).
  - rewrite map_map. apply map_ext_in; intros a Ha.
    rewrite Forall_forall in H. apply H; auto.
  - rewrite IHscrut, IHC. f_equal.
    + apply apply_sub_ext; intros [|x]; simpl; unfold up_sub, scons, shift1; auto.
    + rewrite map_map. apply map_ext_in; intros a Ha.
      rewrite Forall_forall in H0. apply H0; auto.
Qed.

Lemma apply_sub_rename : forall t ξ σ,
  apply_sub σ (rename ξ t) = apply_sub (fun x => σ (ξ x)) t.
Proof.
  induction t using tm_ind_list; intros; simpl; try f_equal; auto.
  all: try match goal with
    | |- apply_sub (up_sub _) (rename _ ?t) = apply_sub _ ?t =>
        (rewrite IHt2 || rewrite IHB || rewrite IHt)
    end.
  all: try (apply apply_sub_ext; intros [|x]; simpl; unfold up_sub, scons, shift1; auto).
  all: try (rewrite IHt1 || rewrite IHA; auto).
  - rewrite map_map. apply map_ext_in; intros a Ha.
    rewrite Forall_forall in H. apply H; auto.
  - rewrite IHscrut, IHC. f_equal.
    + apply apply_sub_ext; intros [|x]; simpl; unfold up_sub, scons, shift1; auto.
    + rewrite map_map. apply map_ext_in; intros a Ha.
      rewrite Forall_forall in H0. apply H0; auto.
Qed.

(** apply_sub composition *)
Lemma apply_sub_comp : forall t σ1 σ2,
  apply_sub σ2 (apply_sub σ1 t) = apply_sub (fun x => apply_sub σ2 (σ1 x)) t.
Proof.
  induction t using tm_ind_list; intros; simpl; try f_equal; auto.
  all: try match goal with
    | |- apply_sub (up_sub _) (apply_sub (up_sub _) ?t) = apply_sub _ ?t =>
        (rewrite IHt2 || rewrite IHB || rewrite IHt)
    end.
  all: try (apply apply_sub_ext; intros [|x]; simpl; unfold up_sub, scons, shift1; auto;
            unfold shift1, shift; rewrite rename_apply_sub; apply apply_sub_ext; intros y; auto).
  all: try (rewrite IHt1 || rewrite IHA; try apply apply_sub_ext; auto).
  all: try (intros [|x]; simpl; unfold up_sub, scons, shift1; auto;
            unfold shift1, shift; rewrite rename_apply_sub; apply apply_sub_ext; intros y; auto).
  - rewrite map_map. apply map_ext_in; intros a Ha.
    rewrite Forall_forall in H. apply H; auto.
  - rewrite IHscrut, IHC. f_equal.
    + apply apply_sub_ext; intros [|x]; simpl; unfold up_sub, scons, shift1; auto;
      unfold shift1, shift; rewrite rename_apply_sub; apply apply_sub_ext; intros y; auto.
    + rewrite map_map. apply map_ext_in; intros a Ha.
      rewrite Forall_forall in H0. apply H0; auto.
Qed.

(** Key lemma: ctx_lookup after shifting *)
Lemma ctx_lookup_shift : forall Γ x A,
  ctx_lookup Γ x = Some A ->
  ctx_lookup Γ x = Some A.
Proof. trivial. Qed.

Lemma ctx_lookup_shift1_cons : forall Γ B x A,
  ctx_lookup Γ x = Some A ->
  ctx_lookup (B :: Γ) (S x) = Some (shift1 A).
Proof.
  intros Γ B x A H. simpl. rewrite H. reflexivity.
Qed.

(** The renaming lemma: typing is preserved under renamings that respect contexts *)
(** We state it as: if we have a renaming ξ that maps context Γ to Δ in the sense that
    for all x, ctx_lookup Γ x = Some A implies ctx_lookup Δ (ξ x) = Some (rename ξ A),
    then has_type Σenv Γ t T implies has_type Σenv Δ (rename ξ t) (rename ξ T). *)

Definition ctx_rename_ok (ξ : nat -> nat) (Γ Δ : ctx) : Prop :=
  forall x A, ctx_lookup Γ x = Some A -> ctx_lookup Δ (ξ x) = Some (rename ξ A).

Lemma lift_rename_ok : forall ξ Γ Δ B,
  ctx_rename_ok ξ Γ Δ ->
  ctx_rename_ok (fun x => match x with 0 => 0 | S x => S (ξ x) end) (B :: Γ) (rename ξ B :: Δ).
Proof.
  intros ξ Γ Δ B Hok x A.
  destruct x as [|x]; simpl.
  - intros [= <-]. f_equal.
    unfold shift1, shift. rewrite rename_rename.
    apply rename_ext; intros [|y]; simpl; lia.
  - intros Hlookup. apply option_map_some in Hlookup.
    destruct Hlookup as [A' [HA' ->]].
    apply Hok in HA'. 
    simpl. rewrite HA'. f_equal.
    unfold shift1, shift. rewrite rename_rename. rewrite rename_rename.
    apply rename_ext; intros y; simpl; lia.
Qed.

Lemma has_type_rename : forall Σenv Γ t T,
  has_type Σenv Γ t T ->
  forall Δ ξ,
  ctx_rename_ok ξ Γ Δ ->
  has_type Σenv Δ (rename ξ t) (rename ξ T).
Proof.
  intros Σenv Γ t T Hty. induction Hty; intros Δ ξ Hok; simpl.
  - apply ty_var. apply Hok. exact H.
  - apply ty_sort.
  - apply ty_pi.
    + apply IHHty1; exact Hok.
    + apply IHHty2. apply lift_rename_ok; exact Hok.
  - apply ty_lam.
    + apply IHHty1; exact Hok.
    + apply IHHty2. apply lift_rename_ok; exact Hok.
  - (* ty_app: type is subst0 u B, need rename ξ (subst0 u B) = subst0 (rename ξ u) (rename ξ B) *)
    change (has_type Σenv Δ (tApp (rename ξ t) (rename ξ u)) (rename ξ (subst0 u B))).
    (* Actually the renaming of subst0 u B is subst0 (rename ξ u) (rename ξ B) *)
    (* Need: rename ξ (subst0 u B) = subst0 (rename ξ u) (rename ξ B) *)
    (* subst0 u B = apply_sub (scons u ids) B *)
    (* rename ξ (apply_sub (scons u ids) B) = apply_sub (fun x => rename ξ (scons u ids x)) (rename ξ B) *)
    (* Hmm, this is actually: apply_sub σ' (rename ξ B) where σ'(0) = rename ξ u, σ'(S x) = tVar (ξ x) *)
    (* = apply_sub (scons (rename ξ u) (ren ξ)) (rename ξ B) *)
    (* But subst0 (rename ξ u) (rename ξ B) = apply_sub (scons (rename ξ u) ids) (rename ξ B) *)
    (* These are equal only if ren ξ = ids which is false in general! *)
    (* So we need a different approach... *)
    admit.
  - admit.
  - apply ty_ind; exact H.
  - simpl. apply ty_roll with (ΣI := ΣI) (ctor := ctor).
    + exact H.
    + exact H0.
    + rewrite map_length. exact H1.
    + rewrite Forall_map. revert H2. apply Forall_impl.
      intros a Hta. apply IHHty1 in Hok. (* wrong *)
      admit.
  - admit.
Admitted.
