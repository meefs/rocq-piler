From Stdlib Require Import Arith List Lia PeanoNat Utf8.
From Coq Require Import Logic.FunctionalExtensionality.
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

(** ** Substitution machinery *)

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

(** Standard global environment for examples *)
Definition Σ_std : env := [Nat_sig; Bool_sig; List_sig].

(** ** Key substitution lemmas *)

Lemma up_sub_ids : up_sub ids = ids.
Proof.
  apply functional_extensionality. intro n.
  unfold up_sub, ids, scons, shift1, shift, rename.
  destruct n; simpl; f_equal; lia.
Qed.

Lemma apply_sub_ids : forall t, apply_sub ids t = t.
Proof.
  fix IH 1.
  destruct t as [x|i|A B|A t|t u|A t|I|I c args|I scrut C brs]; simpl; auto.
  - f_equal; auto. rewrite up_sub_ids. apply IH.
  - f_equal; auto. rewrite up_sub_ids. apply IH.
  - f_equal; auto.
  - f_equal; auto. rewrite up_sub_ids. apply IH.
  - f_equal; auto.
    induction args; simpl; auto.
    f_equal; auto.
  - f_equal; auto.
    rewrite up_sub_ids. apply IH.
    induction brs; simpl; auto.
    f_equal; auto.
Qed.

Lemma apply_sub_rename : forall σ ξ t,
  apply_sub σ (rename ξ t) = apply_sub (fun x => σ (ξ x)) t.
Proof.
  fix IH 3. intros σ ξ t.
  destruct t as [x|i|A B|A t|t u|A t|I|I c args|I scrut C brs]; simpl; auto.
  - f_equal; auto.
    rewrite (IH (up_sub σ) (fun x => match x with 0 => 0 | S x0 => S (ξ x0) end) B).
    f_equal. apply functional_extensionality. intro n. destruct n; simpl; auto.
  - f_equal; auto.
    rewrite (IH (up_sub σ) (fun x => match x with 0 => 0 | S x0 => S (ξ x0) end) t).
    f_equal. apply functional_extensionality. intro n. destruct n; simpl; auto.
  - f_equal; auto.
  - f_equal; auto.
    rewrite (IH (up_sub σ) (fun x => match x with 0 => 0 | S x0 => S (ξ x0) end) t).
    f_equal. apply functional_extensionality. intro n. destruct n; simpl; auto.
  - f_equal; auto.
    induction args; simpl; auto.
    f_equal; auto.
  - f_equal; auto.
    rewrite (IH (up_sub σ) (fun x => match x with 0 => 0 | S x0 => S (ξ x0) end) C).
    f_equal. apply functional_extensionality. intro n. destruct n; simpl; auto.
    induction brs; simpl; auto.
    f_equal; auto.
Qed.

Lemma subst0_shift1 : forall s t, subst0 s (shift1 t) = t.
Proof.
  intros s t. unfold subst0, shift1, shift.
  rewrite apply_sub_rename. simpl.
  apply apply_sub_ids.
Qed.

Fixpoint apply_sub_comp (σ τ : sub) (t : tm) {struct t}
  : apply_sub σ (apply_sub τ t) = apply_sub (fun x => apply_sub σ (τ x)) t
with apply_sub_up_sub_shift1 (σ : sub) (t : tm) {struct t}
  : apply_sub (up_sub σ) (shift1 t) = shift1 (apply_sub σ t).
Proof.
  - destruct t as [x|i|A B|A t|t u|A t|I|I c args|I scrut C brs]; simpl; auto.
    (* tPi *)
    + f_equal; [symmetry; apply (apply_sub_comp σ τ A) | ].
      rewrite (apply_sub_comp (up_sub σ) (up_sub τ) B).
      f_equal. apply functional_extensionality.
      intro n. destruct n.
      * reflexivity.
      * simpl. rewrite apply_sub_up_sub_shift1. reflexivity.
    (* tLam *)
    + f_equal; [symmetry; apply (apply_sub_comp σ τ A) | ].
      rewrite (apply_sub_comp (up_sub σ) (up_sub τ) t).
      f_equal. apply functional_extensionality.
      intro n. destruct n.
      * reflexivity.
      * simpl. rewrite apply_sub_up_sub_shift1. reflexivity.
    (* tApp *)
    + f_equal; [symmetry; apply (apply_sub_comp σ τ t) | symmetry; apply (apply_sub_comp σ τ u)].
    (* tFix *)
    + f_equal; [symmetry; apply (apply_sub_comp σ τ A) | ].
      rewrite (apply_sub_comp (up_sub σ) (up_sub τ) t).
      f_equal. apply functional_extensionality.
      intro n. destruct n.
      * reflexivity.
      * simpl. rewrite apply_sub_up_sub_shift1. reflexivity.
    (* tRoll *)
    + f_equal; try reflexivity.
      induction args; simpl.
      * reflexivity.
      * f_equal; [symmetry; apply (apply_sub_comp σ τ a) | assumption].
    (* tCase *)
    + f_equal; [reflexivity | symmetry; apply (apply_sub_comp σ τ scrut) | | ].
      rewrite (apply_sub_comp (up_sub σ) (up_sub τ) C).
      f_equal. apply functional_extensionality.
      intro n. destruct n.
      * reflexivity.
      * simpl. rewrite apply_sub_up_sub_shift1. reflexivity.
      induction brs; simpl.
      * reflexivity.
      * f_equal; [symmetry; apply (apply_sub_comp σ τ a) | assumption].
  - destruct t as [x|i|A B|A t|t u|A t|I|I c args|I scrut C brs]; simpl.
    + reflexivity.
    + reflexivity.
    (* tPi *)
    + unfold shift1, shift.
      f_equal; [apply apply_sub_up_sub_shift1 | ].
      rewrite apply_sub_rename. simpl.
      apply apply_sub_up_sub_shift1.
    (* tLam *)
    + unfold shift1, shift.
      f_equal; [apply apply_sub_up_sub_shift1 | ].
      rewrite apply_sub_rename. simpl.
      apply apply_sub_up_sub_shift1.
    (* tApp *)
    + unfold shift1, shift.
      f_equal; [apply apply_sub_up_sub_shift1 | apply apply_sub_up_sub_shift1].
    (* tFix *)
    + unfold shift1, shift.
      f_equal; [apply apply_sub_up_sub_shift1 | ].
      rewrite apply_sub_rename. simpl.
      apply apply_sub_up_sub_shift1.
    + reflexivity.
    (* tRoll *)
    + unfold shift1, shift.
      f_equal; try reflexivity.
      induction args; simpl.
      * reflexivity.
      * f_equal; [apply apply_sub_up_sub_shift1 | assumption].
    (* tCase *)
    + unfold shift1, shift.
      f_equal; [reflexivity | apply apply_sub_up_sub_shift1 | | ].
      rewrite apply_sub_rename. simpl.
      apply apply_sub_up_sub_shift1.
      induction brs; simpl.
      * reflexivity.
      * f_equal; [apply apply_sub_up_sub_shift1 | assumption].
Qed.

Lemma subst0_subst0_eq : forall u1 u2 t,
  subst0 u1 (subst0 u2 t) =
  apply_sub (scons (subst0 u1 u2) (fun x => apply_sub (scons u1 ids) (tVar (S x)))) t.
Proof.
  intros u1 u2 t. unfold subst0.
  rewrite apply_sub_comp.
  f_equal. apply functional_extensionality. intros [|x]; simpl; auto.
  apply functional_extensionality. intros y. simpl.
  rewrite apply_sub_comp. simpl. reflexivity.
Qed.

(** ** Main substitution lemma *)

Lemma typing_subst0 : forall Σenv Γ A t B u,
  has_type Σenv (A :: Γ) t B ->
  has_type Σenv Γ u A ->
  has_type Σenv Γ (subst0 u t) (subst0 u B).
Proof.
  intros Σenv Γ A t B u Ht Hu.
  remember (A :: Γ) as Γ'.
  revert A Γ Hu HeqΓ'.
  induction Ht; intros A0 Γ0 Hu0 Heq; inversion Heq; subst; clear Heq; simpl.
  - destruct x; simpl in H.
    + inversion H; subst. rewrite subst0_shift1. assumption.
    + unfold ctx_lookup in H. simpl in H.
      destruct (ctx_lookup Γ0 n) eqn:Heq'; inversion H; subst.
      simpl. rewrite subst0_shift1.
      apply ty_var. auto.
  - apply ty_sort.
  - apply ty_pi with (i:=i) (j:=j).
    + apply (IHHt1 A0 Γ0 Hu0 eq_refl).
    + apply (IHHt2 A (A0 :: Γ0) Hu0 eq_refl).
  - apply ty_lam with (i:=i).
    + apply (IHHt1 A0 Γ0 Hu0 eq_refl).
    + apply (IHHt2 A (A0 :: Γ0) Hu0 eq_refl).
  - apply ty_app with (A:=subst0 u t0).
    + apply (IHHt1 A0 Γ0 Hu0 eq_refl).
    + apply (IHHt2 A0 Γ0 Hu0 eq_refl).
    + rewrite subst0_subst0_eq. reflexivity.
  - apply ty_fix with (i:=i).
    + apply (IHHt1 A0 Γ0 Hu0 eq_refl).
    + apply (IHHt2 A (A0 :: Γ0) Hu0 eq_refl).
  - apply ty_ind with (ΣI:=ΣI); auto.
  - apply ty_roll with (ΣI:=ΣI) (ctor:=ctor); auto.
    + rewrite map_length. auto.
    + rewrite Forall_forall in *.
      intros a Hin. apply Forall_forall with (x:=a) in H2; auto.
      eapply H2; eauto.
  - apply ty_case with (ΣI:=ΣI) (i:=i); auto.
    + apply (IHHt1 A0 Γ0 Hu0 eq_refl).
    + apply (IHHt2 (tInd I) (A0 :: Γ0) Hu0 eq_refl).
    + intros c ctor Hc.
      destruct (H4 c ctor Hc) as [br [Hb Hbr]].
      exists br; split; auto.
      eapply Hbr; eauto.
Qed.

(** ** Conjecture pairs *)

Theorem preservation :
  forall Σenv Γ t t' T,
    has_type Σenv Γ t T ->
    step t t' ->
    has_type Σenv Γ t' T.
Proof.
  intros Σenv Γ t t' T Ht Hstep.
  induction Hstep; subst.
  - inversion Ht; subst; clear Ht.
    inversion H2; subst; clear H2.
    eapply typing_subst0; eauto.
  - inversion Ht; subst; clear Ht.
    apply ty_app with (A:=A); auto.
  - inversion Ht; subst; clear Ht.
    eapply typing_subst0 with (A:=A) (Γ:=Γ); eauto.
    rewrite subst0_shift1. assumption.
  - inversion Ht; subst; clear Ht.
    apply ty_case with (ΣI:=ΣI) (i:=i); auto.
    intros c ctor Hc.
    destruct (H4 c ctor Hc) as [br [Hb Hbr]].
    exists br; split; auto.
  - inversion Ht; subst; clear Ht.
    rename H3 into Hscrut.
    inversion Hscrut; subst; clear Hscrut.
    rename I0 into I, c0 into c.
    destruct (H4 c ctor H7) as [br [Hb Hbr]].
    subst Hb. clear H4.
    set (As := repeat (tInd I) (ctor_param_arity ctor + ctor_rec_arity ctor)).
    assert (Hlen: length args = length As).
    { unfold As. rewrite repeat_length. unfold ctor_arity. lia. }
    revert br Hbr C.
    induction args as [|a args IH] in As, Hlen, H1, Hlen |- *; simpl; intros br Hbr C.
    + destruct As; simpl in *; inversion Hlen.
    + destruct As as [|A As']; simpl in *; try discriminate.
      inversion Hlen as [Hlen'].
      inversion H1 as [|a' args' Ha Hrest]; subst. clear H1.
      simpl in Hbr.
      apply IH with (As:=As') (args:=args); auto.
      * clear IH Hrest Ha.
        apply ty_app with (A:=A).
        -- exact Hbr.
        -- exact Ha.
        -- clear Ha Hrest Hbr.
           induction As'; simpl; auto.
           f_equal. apply IHAs'.
      * exact Hrest.
Qed.

Theorem preservation_neg : ~ (
  forall Σenv Γ t t' T,
    has_type Σenv Γ t T ->
    step t t' ->
    has_type Σenv Γ t' T).
Proof.
  exact (fun Hneg => Hneg preservation).
Qed.

Theorem progress :
  forall Σenv t T,
    has_type Σenv [] t T ->
    value t \/ exists t', step t t'.
Proof.
  intros Σenv t T Ht.
  remember [] as Γ.
  revert HeqΓ.
  induction Ht; intros Heq; subst; simpl; auto.
  - left. constructor.
  - left. constructor.
  - left. constructor.
  - left. constructor.
  - inversion Heq.
    destruct (IHHt1 eq_refl) as [Hv | [t1' Hstep]].
    + inversion Hv; subst.
      * inversion Ht1.
      * inversion Ht1.
      * right. exists (subst0 u t). apply step_beta.
      * inversion Ht1.
      * inversion Ht1.
    + right. exists (tApp t1' u). apply step_app1. exact Hstep.
  - inversion Heq.
    right. exists (subst0 (tFix A t) t). apply step_fix.
  - left. constructor.
  - left. constructor.
  - inversion Heq.
    inversion Heq.
    destruct (IHHt1 eq_refl) as [Hv | [scrut' Hstep]].
    + inversion Hv; subst.
      * inversion Ht1.
      * inversion Ht1.
      * inversion Ht1.
      * inversion Ht1.
      * rename I0 into I, c0 into c.
        destruct (H3 c ctor) as [br [Hb Hbr]].
        { unfold lookup_ctor. rewrite H0. reflexivity. }
        right. exists (apps br args). apply step_case_roll. exact Hb.
    + right. exists (tCase I scrut' C brs). apply step_case_scrut. exact Hstep.
Qed.

Theorem progress_neg : ~ (
  forall Σenv t T,
    has_type Σenv [] t T ->
    value t \/ exists t', step t t').
Proof.
  exact (fun Hneg => Hneg progress).
Qed.
