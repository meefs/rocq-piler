From Stdlib Require Import Arith List Lia PeanoNat Utf8.
Import ListNotations.

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

Definition upren (ξ : nat -> nat) : nat -> nat :=
  fun x => match x with 0 => 0 | S x => S (ξ x) end.

Lemma tm_ind_strong : forall (P : tm -> Prop),
  (forall x, P (tVar x)) ->
  (forall i, P (tSort i)) ->
  (forall A B, P A -> P B -> P (tPi A B)) ->
  (forall A t, P A -> P t -> P (tLam A t)) ->
  (forall t u, P t -> P u -> P (tApp t u)) ->
  (forall A t, P A -> P t -> P (tFix A t)) ->
  (forall I, P (tInd I)) ->
  (forall I c args, Forall P args -> P (tRoll I c args)) ->
  (forall I scrut C brs, P scrut -> P C -> Forall P brs -> P (tCase I scrut C brs)) ->
  forall t, P t.
Proof.
  intros P Hvar Hsort Hpi Hlam Happ Hfix Hind Hroll Hcase.
  fix go 1. intro t. destruct t as [x|i|A B|A t0|t0 u|A t0|I0|I0 c0 args|I0 scrut C brs].
  - apply Hvar.
  - apply Hsort.
  - apply Hpi; apply go.
  - apply Hlam; apply go.
  - apply Happ; apply go.
  - apply Hfix; apply go.
  - apply Hind.
  - apply Hroll. induction args as [|a rest IHrest]; constructor; [apply go | exact IHrest].
  - apply Hcase; try apply go.
    induction brs as [|b rest IHrest]; constructor; [apply go | exact IHrest].
Defined.

Lemma Forall_map_eq : forall {A B : Type} (f g : A -> B) l,
  Forall (fun x => f x = g x) l -> map f l = map g l.
Proof. induction 1; simpl; f_equal; auto. Qed.

Lemma map_id_Forall : forall {A : Type} (f : A -> A) l,
  Forall (fun x => f x = x) l -> map f l = l.
Proof. induction 1; simpl; f_equal; auto. Qed.

Lemma Forall_nth_error : forall {A : Type} (P : A -> Prop) l n x,
  Forall P l -> nth_error l n = Some x -> P x.
Proof.
  intros A P l n x HF. revert n. induction HF; intros [|]; simpl; intros; try discriminate.
  - congruence.
  - eapply IHHF; eauto.
Qed.

Lemma rename_ext : forall t ξ ψ, (forall x, ξ x = ψ x) -> rename ξ t = rename ψ t.
Proof.
  induction t using tm_ind_strong; intros; simpl; f_equal; auto.
  - apply IHt2; intros [|]; simpl; auto; f_equal; auto.
  - apply IHt2; intros [|]; simpl; auto; f_equal; auto.
  - apply IHt2; intros [|]; simpl; auto; f_equal; auto.
  - apply Forall_map_eq. revert H. apply Forall_impl. intros a Ha. apply Ha. auto.
  - apply IHt2; intros [|]; simpl; auto; f_equal; auto.
  - apply Forall_map_eq. revert H. apply Forall_impl. intros a Ha. apply Ha. auto.
Qed.

Lemma rename_id : forall t, rename (fun x => x) t = t.
Proof.
  induction t using tm_ind_strong; simpl; f_equal; auto.
  all: try (erewrite rename_ext; [eauto | intros [|]; auto]).
  all: apply map_id_Forall; revert H; apply Forall_impl; auto.
Qed.

Lemma rename_comp : forall t ξ ψ, rename ξ (rename ψ t) = rename (fun x => ξ (ψ x)) t.
Proof.
  induction t using tm_ind_strong; intros; simpl; f_equal; auto.
  - rewrite IHt2; apply rename_ext; intros [|]; simpl; auto.
  - rewrite IHt2; apply rename_ext; intros [|]; simpl; auto.
  - rewrite IHt2; apply rename_ext; intros [|]; simpl; auto.
  - rewrite map_map. apply Forall_map_eq. revert H. apply Forall_impl. intros a Ha. apply Ha.
  - rewrite IHt2; apply rename_ext; intros [|]; simpl; auto.
  - rewrite map_map. apply Forall_map_eq. revert H. apply Forall_impl. intros a Ha. apply Ha.
Qed.

Lemma apply_sub_ext : forall t σ τ, (forall x, σ x = τ x) -> apply_sub σ t = apply_sub τ t.
Proof.
  induction t using tm_ind_strong; intros; simpl; f_equal; auto.
  - apply IHt2; intros [|]; simpl; unfold up_sub, scons, shift1, shift; auto; f_equal; auto.
  - apply IHt2; intros [|]; simpl; unfold up_sub, scons, shift1, shift; auto; f_equal; auto.
  - apply IHt2; intros [|]; simpl; unfold up_sub, scons, shift1, shift; auto; f_equal; auto.
  - apply Forall_map_eq. revert H. apply Forall_impl. intros a Ha. eapply Ha; eauto.
  - apply IHt2; intros [|]; simpl; unfold up_sub, scons, shift1, shift; auto; f_equal; auto.
  - apply Forall_map_eq. revert H. apply Forall_impl. intros a Ha. eapply Ha; eauto.
Qed.

Lemma apply_sub_ren : forall t ξ, apply_sub (ren ξ) t = rename ξ t.
Proof.
  induction t using tm_ind_strong; intros; simpl; f_equal; auto.
  - rewrite <- IHt2; apply apply_sub_ext; intros [|]; simpl; unfold ren, up_sub, scons, shift1, shift; auto.
  - rewrite <- IHt2; apply apply_sub_ext; intros [|]; simpl; unfold ren, up_sub, scons, shift1, shift; auto.
  - rewrite <- IHt2; apply apply_sub_ext; intros [|]; simpl; unfold ren, up_sub, scons, shift1, shift; auto.
  - apply Forall_map_eq. revert H. apply Forall_impl. intros a Ha. apply Ha.
  - rewrite <- IHt2; apply apply_sub_ext; intros [|]; simpl; unfold ren, up_sub, scons, shift1, shift; auto.
  - apply Forall_map_eq. revert H. apply Forall_impl. intros a Ha. apply Ha.
Qed.

Lemma apply_sub_ids : forall t, apply_sub ids t = t.
Proof.
  induction t using tm_ind_strong; simpl; f_equal; auto.
  all: try (erewrite apply_sub_ext; [eauto|]; intros [|]; simpl; unfold up_sub, scons, ids, shift1, shift; auto; rewrite rename_id; auto).
  all: apply map_id_Forall; revert H; apply Forall_impl; auto.
Qed.

Lemma apply_sub_rename : forall t σ ξ, apply_sub σ (rename ξ t) = apply_sub (fun x => σ (ξ x)) t.
Proof.
  induction t using tm_ind_strong; intros; simpl; f_equal; auto.
  - rewrite IHt2; apply apply_sub_ext; intros [|]; simpl; unfold up_sub, scons; auto.
  - rewrite IHt2; apply apply_sub_ext; intros [|]; simpl; unfold up_sub, scons; auto.
  - rewrite IHt2; apply apply_sub_ext; intros [|]; simpl; unfold up_sub, scons; auto.
  - rewrite map_map. apply Forall_map_eq. revert H. apply Forall_impl. intros a Ha. apply Ha.
  - rewrite IHt2; apply apply_sub_ext; intros [|]; simpl; unfold up_sub, scons; auto.
  - rewrite map_map. apply Forall_map_eq. revert H. apply Forall_impl. intros a Ha. apply Ha.
Qed.

Lemma rename_apply_sub : forall t ξ σ, rename ξ (apply_sub σ t) = apply_sub (fun x => rename ξ (σ x)) t.
Proof.
  induction t using tm_ind_strong; intros; simpl; f_equal; auto.
  - rewrite IHt2; apply apply_sub_ext; intros [|]; simpl; unfold up_sub, scons, shift1, shift; auto.
    rewrite !rename_comp. apply rename_ext. intros; simpl; auto.
  - rewrite IHt2; apply apply_sub_ext; intros [|]; simpl; unfold up_sub, scons, shift1, shift; auto.
    rewrite !rename_comp. apply rename_ext. intros; simpl; auto.
  - rewrite IHt2; apply apply_sub_ext; intros [|]; simpl; unfold up_sub, scons, shift1, shift; auto.
    rewrite !rename_comp. apply rename_ext. intros; simpl; auto.
  - rewrite map_map. apply Forall_map_eq. revert H. apply Forall_impl. intros a Ha. apply Ha.
  - rewrite IHt2; apply apply_sub_ext; intros [|]; simpl; unfold up_sub, scons, shift1, shift; auto.
    rewrite !rename_comp. apply rename_ext. intros; simpl; auto.
  - rewrite map_map. apply Forall_map_eq. revert H. apply Forall_impl. intros a Ha. apply Ha.
Qed.

Lemma apply_sub_up_shift1 : forall σ t, apply_sub (up_sub σ) (shift1 t) = shift1 (apply_sub σ t).
Proof.
  intros. unfold shift1, shift.
  rewrite apply_sub_rename. rewrite rename_apply_sub.
  apply apply_sub_ext. intros x. simpl. unfold up_sub, scons, shift1, shift. auto.
Qed.

Lemma subst0_shift1 : forall s t, subst0 s (shift1 t) = t.
Proof.
  intros. unfold subst0, shift1, shift.
  rewrite apply_sub_rename.
  erewrite apply_sub_ext. apply apply_sub_ids.
  intros x. simpl. unfold scons, ids. auto.
Qed.

Lemma apply_sub_comp : forall t σ τ, apply_sub σ (apply_sub τ t) = apply_sub (fun x => apply_sub σ (τ x)) t.
Proof.
  induction t using tm_ind_strong; intros; simpl; f_equal; auto.
  - rewrite IHt2; apply apply_sub_ext; intros [|]; simpl; auto.
    rewrite apply_sub_up_shift1; auto.
  - rewrite IHt2; apply apply_sub_ext; intros [|]; simpl; auto.
    rewrite apply_sub_up_shift1; auto.
  - rewrite IHt2; apply apply_sub_ext; intros [|]; simpl; auto.
    rewrite apply_sub_up_shift1; auto.
  - rewrite map_map. apply Forall_map_eq. revert H. apply Forall_impl. intros a Ha. apply Ha.
  - rewrite IHt2; apply apply_sub_ext; intros [|]; simpl; auto.
    rewrite apply_sub_up_shift1; auto.
  - rewrite map_map. apply Forall_map_eq. revert H. apply Forall_impl. intros a Ha. apply Ha.
Qed.

Definition good_ren (Γ Δ : ctx) (ξ : nat -> nat) : Prop :=
  forall x A, ctx_lookup Γ x = Some A -> ctx_lookup Δ (ξ x) = Some (rename ξ A).

Lemma good_ren_up : forall Γ Δ ξ A,
  good_ren Γ Δ ξ -> good_ren (A :: Γ) (rename ξ A :: Δ) (upren ξ).
Proof.
  unfold good_ren, upren. intros. destruct x; simpl in *.
  - injection H0; intros; subst. simpl. unfold shift1, shift. f_equal.
    rewrite !rename_comp. apply rename_ext. intros; simpl; auto.
  - destruct (ctx_lookup Γ x) eqn:E; simpl in *; [|discriminate].
    injection H0; intros; subst. specialize (H _ _ E). simpl. rewrite H. simpl.
    unfold shift1, shift. f_equal. rewrite !rename_comp.
    apply rename_ext. intros. simpl. lia.
Qed.

Lemma good_ren_S : forall Γ B, good_ren Γ (B :: Γ) S.
Proof.
  unfold good_ren. intros Γ B x A H. simpl. rewrite H. simpl. auto.
Qed.

Lemma nat_iter_comm : forall {A : Type} (f : A -> A) n x,
  Nat.iter n f (f x) = f (Nat.iter n f x).
Proof. induction n; simpl; intros; auto. rewrite IHn. auto. Qed.

Lemma nat_iter_succ_r : forall {A : Type} (f : A -> A) n x,
  Nat.iter (S n) f x = Nat.iter n f (f x).
Proof. intros. rewrite nat_iter_comm. auto. Qed.

Lemma rename_mk_pis_ind : forall n I ξ body,
  rename ξ (mk_pis (repeat (tInd I) n) body) =
  mk_pis (repeat (tInd I) n) (rename (Nat.iter n upren ξ) body).
Proof.
  induction n; intros.
  - reflexivity.
  - cbn [repeat mk_pis rename Nat.iter]. fold (upren ξ).
    f_equal. rewrite IHn. f_equal. f_equal.
    symmetry. apply nat_iter_succ_r.
Qed.


Lemma iter_upren_lt : forall m ξ k, k < m -> Nat.iter m upren ξ k = k.
Proof.
induction m; intros; [lia|]; simpl; destruct k; [auto|]; simpl; f_equal; apply IHm; lia.
Qed.


Lemma iter_upren_add : forall m ξ n, Nat.iter m upren ξ (m + n) = m + ξ n.
Proof.
induction m; intros; simpl; [lia|]; f_equal; apply IHm.
Qed.

Lemma rename_motive_inst : forall I c m ξ C,
  rename (Nat.iter m upren ξ) (motive_inst I c m C) =
  motive_inst I c m (rename (upren ξ) C).
Proof.
intros; unfold motive_inst; rewrite rename_apply_sub; rewrite apply_sub_rename; apply apply_sub_ext; intros [|n]; simpl.
- f_equal. rewrite map_map. apply map_ext_in. intros a Ha. simpl. f_equal. apply iter_upren_lt. apply in_rev in Ha. apply in_seq in Ha. lia. - unfold ren. simpl. f_equal. apply iter_upren_add.
Qed.


Lemma rename_branch_type : forall ξ I c n C, rename ξ (mk_pis (repeat (tInd I) n) (motive_inst I c n C)) = mk_pis (repeat (tInd I) n) (motive_inst I c n (rename (upren ξ) C)).
Proof.
intros; rewrite rename_mk_pis_ind; f_equal; apply rename_motive_inst.
Qed.

Lemma rename_typing : forall t Σenv Γ T,
  has_type Σenv Γ t T ->
  forall Δ ξ, good_ren Γ Δ ξ ->
  has_type Σenv Δ (rename ξ t) (rename ξ T).
Proof.
  induction t using tm_ind_strong; intros Σ Γ T Hty Δ ξ Hren; inversion Hty; subst; simpl.
  - constructor. apply Hren. auto.
  - constructor.
  - assert (H' := IHt1 _ _ _ ltac:(eassumption) _ _ Hren); simpl in H'.
    assert (H'' := IHt2 _ _ _ ltac:(eassumption) _ _ (good_ren_up _ _ _ _ Hren)); simpl in H''.
    exact (ty_pi _ _ _ _ _ _ H' H'').
  - assert (H' := IHt1 _ _ _ ltac:(eassumption) _ _ Hren); simpl in H'.
    assert (H'' := IHt2 _ _ _ ltac:(eassumption) _ _ (good_ren_up _ _ _ _ Hren)); simpl in H''.
    exact (ty_lam _ _ _ _ _ _ H' H'').
  - assert (Htype: rename ξ (subst0 t2 B) = subst0 (rename ξ t2) (rename (upren ξ) B)).
    { unfold subst0. rewrite rename_apply_sub. rewrite apply_sub_rename.
      apply apply_sub_ext. intros [|]; simpl; unfold scons, ids; auto. }
    rewrite Htype.
    assert (HA := IHt1 _ _ _ ltac:(eassumption) _ _ Hren); simpl in HA.
    assert (HB := IHt2 _ _ _ ltac:(eassumption) _ _ Hren); simpl in HB.
    exact (ty_app _ _ _ _ _ _ HA HB).
  - assert (H' := IHt1 _ _ _ ltac:(eassumption) _ _ Hren); simpl in H'.
    assert (H'' := IHt2 _ _ _ ltac:(eassumption) _ _ (good_ren_up _ _ _ _ Hren)).
    assert (Heq: rename (upren ξ) (shift1 T) = shift1 (rename ξ T)).
    { unfold shift1, shift. rewrite !rename_comp. apply rename_ext. intros; simpl; auto. }
    rewrite Heq in H''.
    exact (ty_fix _ _ _ _ _ H' H'').
  - econstructor; eauto.
  - econstructor; eauto.
    + rewrite map_length. eauto.
    + rewrite Forall_forall in *. intros a Ha.
      apply in_map_iff in Ha. destruct Ha as [a0 [<- Ha0]].
      match goal with HIH : forall x, In x args -> _ |- _ =>
        specialize (HIH a0 Ha0) end.
      match goal with Htyp : forall x, In x args -> _ |- _ =>
        specialize (Htyp a0 Ha0) end.
      match goal with HIH : forall _ _ _, has_type _ _ a0 _ -> _,
                      Htyp : has_type _ _ a0 _ |- _ =>
        specialize (HIH _ _ _ Htyp _ _ Hren); simpl in HIH; auto end.
  - assert (Htype: rename ξ (subst0 t1 t2) = subst0 (rename ξ t1) (rename (upren ξ) t2)).
    { unfold subst0. rewrite rename_apply_sub. rewrite apply_sub_rename.
      apply apply_sub_ext. intros [|]; simpl; unfold scons, ids; auto. }
    rewrite Htype. eapply ty_case.
    + eauto.
    + rewrite map_length. eauto.
    + assert (Hscrut := IHt1 _ _ _ ltac:(eassumption) _ _ Hren); simpl in Hscrut. exact Hscrut.
    + assert (HC := IHt2 _ _ _ ltac:(eassumption) _ _ (good_ren_up _ _ _ _ Hren)); simpl in HC. exact HC.
    + intros c0 ctor0 Hc0.
      match goal with H : forall c ctor, _ -> exists br, _ |- _ =>
        specialize (H c0 ctor0 Hc0) as [br0 [Hbr0 Htyp0]]; simpl in Htyp0 end.
      exists (rename ξ br0). split.
      * unfold branch in *. rewrite nth_error_map. rewrite Hbr0. simpl. auto.
      * rewrite Forall_forall in H.
        assert (Hin: In br0 brs) by (eapply nth_error_In; eauto).
        specialize (H br0 Hin).
        rewrite repeat_length in Htyp0.
        assert (Hbr := H _ _ _ Htyp0 _ _ Hren).
        rewrite rename_branch_type in Hbr.
        cbv zeta. rewrite repeat_length. exact Hbr.
Qed.

Lemma weakening : forall Σenv Γ t T B,
  has_type Σenv Γ t T -> has_type Σenv (B :: Γ) (shift1 t) (shift1 T).
Proof.
  intros. unfold shift1, shift.
  replace (rename (Nat.add 1) t) with (rename S t) by (apply rename_ext; intros; lia).
  replace (rename (Nat.add 1) T) with (rename S T) by (apply rename_ext; intros; lia).
  eapply rename_typing; eauto. apply good_ren_S.
Qed.

Definition good_sub (Σenv : env) (Γ : ctx) (Δ : ctx) (σ : sub) : Prop :=
  forall x A, ctx_lookup Δ x = Some A -> has_type Σenv Γ (σ x) (apply_sub σ A).

Lemma good_sub_up : forall Σenv Γ Δ σ A,
  good_sub Σenv Γ Δ σ -> good_sub Σenv (apply_sub σ A :: Γ) (A :: Δ) (up_sub σ).
Proof.
  unfold good_sub. intros Σenv Γ Δ σ A Hgood x B Hlook.
  destruct x; simpl in *.
  - injection Hlook; intros; subst. constructor. simpl. f_equal.
    rewrite apply_sub_up_shift1. auto.
  - destruct (ctx_lookup Δ x) eqn:E; simpl in *; [|discriminate].
    injection Hlook; intros; subst. rewrite apply_sub_up_shift1.
    apply weakening. apply Hgood. auto.
Qed.

Lemma apply_sub_mk_pis_ind : forall n I σ body,
  apply_sub σ (mk_pis (repeat (tInd I) n) body) =
  mk_pis (repeat (tInd I) n) (apply_sub (Nat.iter n up_sub σ) body).
Proof.
  induction n; intros.
  - reflexivity.
  - cbn [repeat mk_pis apply_sub Nat.iter].
    f_equal. rewrite IHn. f_equal. f_equal.
    symmetry. apply (nat_iter_succ_r up_sub).
Qed.


Lemma iter_up_sub_lt : forall m σ k, k < m -> Nat.iter m up_sub σ k = tVar k.
Proof.
induction m; intros; [lia|]; simpl; destruct k; [auto|]; unfold up_sub at 1, scons at 1; unfold shift1, shift; rewrite IHm; [simpl; auto | lia].
Qed.


Lemma iter_up_sub_add : forall m σ n, Nat.iter m up_sub σ (m + n) = rename (Nat.add m) (σ n).
Proof.
induction m; intros; simpl. - rewrite rename_id; auto. - unfold up_sub at 1, scons at 1, shift1, shift. rewrite IHm. rewrite rename_comp. apply rename_ext. intros; lia.
Qed.

Lemma apply_sub_motive_inst : forall I c m σ C,
  apply_sub (Nat.iter m up_sub σ) (motive_inst I c m C) =
  motive_inst I c m (apply_sub (up_sub σ) C).
Proof.
intros; unfold motive_inst; rewrite !apply_sub_comp; apply apply_sub_ext; intros [|n]; simpl.
- f_equal. rewrite map_map. apply map_ext_in. intros a Ha. simpl. apply iter_up_sub_lt. apply in_rev in Ha. apply in_seq in Ha. lia. - rewrite iter_up_sub_add. unfold shift1, shift. rewrite apply_sub_rename. rewrite <- apply_sub_ren. apply apply_sub_ext. intros x; simpl; unfold scons, ren; auto.
Qed.


Lemma apply_sub_branch_type : forall σ I c n C, apply_sub σ (mk_pis (repeat (tInd I) n) (motive_inst I c n C)) = mk_pis (repeat (tInd I) n) (motive_inst I c n (apply_sub (up_sub σ) C)).
Proof.
intros; rewrite apply_sub_mk_pis_ind; f_equal; apply apply_sub_motive_inst.
Qed.

Lemma typing_sub : forall t Σenv Δ T,
  has_type Σenv Δ t T ->
  forall Γ σ, good_sub Σenv Γ Δ σ ->
  has_type Σenv Γ (apply_sub σ t) (apply_sub σ T).
Proof.
  induction t using tm_ind_strong; intros Σ Δ T Hty Γ σ Hgood; inversion Hty; subst; simpl.
  - apply Hgood. auto.
  - constructor.
  - assert (H' := IHt1 _ _ _ ltac:(eassumption) _ _ Hgood); simpl in H'.
    assert (H'' := IHt2 _ _ _ ltac:(eassumption) _ _ (good_sub_up _ _ _ _ _ Hgood)); simpl in H''.
    exact (ty_pi _ _ _ _ _ _ H' H'').
  - assert (H' := IHt1 _ _ _ ltac:(eassumption) _ _ Hgood); simpl in H'.
    assert (H'' := IHt2 _ _ _ ltac:(eassumption) _ _ (good_sub_up _ _ _ _ _ Hgood)); simpl in H''.
    exact (ty_lam _ _ _ _ _ _ H' H'').
  - assert (Htype: apply_sub σ (subst0 t2 B) = subst0 (apply_sub σ t2) (apply_sub (up_sub σ) B)).
    { unfold subst0. rewrite !apply_sub_comp.
      apply apply_sub_ext. intros [|]; simpl; [auto|].
      unfold ids; simpl. symmetry. apply subst0_shift1. }
    rewrite Htype.
    assert (HA := IHt1 _ _ _ ltac:(eassumption) _ _ Hgood); simpl in HA.
    assert (HB := IHt2 _ _ _ ltac:(eassumption) _ _ Hgood); simpl in HB.
    exact (ty_app _ _ _ _ _ _ HA HB).
  - assert (H' := IHt1 _ _ _ ltac:(eassumption) _ _ Hgood); simpl in H'.
    assert (H'' := IHt2 _ _ _ ltac:(eassumption) _ _ (good_sub_up _ _ _ _ _ Hgood)).
    rewrite apply_sub_up_shift1 in H''.
    exact (ty_fix _ _ _ _ _ H' H'').
  - econstructor; eauto.
  - econstructor; eauto.
    + rewrite map_length. eauto.
    + rewrite Forall_forall in *. intros a Ha.
      apply in_map_iff in Ha. destruct Ha as [a0 [<- Ha0]].
      match goal with HIH : forall x, In x args -> _ |- _ => specialize (HIH a0 Ha0) end.
      match goal with Htyp : forall x, In x args -> _ |- _ => specialize (Htyp a0 Ha0) end.
      match goal with HIH : forall _ _ _, has_type _ _ a0 _ -> _,
                      Htyp : has_type _ _ a0 _ |- _ =>
        specialize (HIH _ _ _ Htyp _ _ Hgood); simpl in HIH; auto end.
  - assert (Htype: apply_sub σ (subst0 t1 t2) = subst0 (apply_sub σ t1) (apply_sub (up_sub σ) t2)).
    { unfold subst0. rewrite !apply_sub_comp.
      apply apply_sub_ext. intros [|]; simpl; [auto|].
      unfold ids; simpl. symmetry. apply subst0_shift1. }
    rewrite Htype. eapply ty_case.
    + eauto.
    + rewrite map_length. eauto.
    + assert (Hscrut := IHt1 _ _ _ ltac:(eassumption) _ _ Hgood); simpl in Hscrut. exact Hscrut.
    + assert (HC := IHt2 _ _ _ ltac:(eassumption) _ _ (good_sub_up _ _ _ _ _ Hgood)); simpl in HC. exact HC.
    + intros c0 ctor0 Hc0.
      match goal with HBR : forall c ctor, _ -> exists br, _ |- _ =>
        specialize (HBR c0 ctor0 Hc0) as [br0 [Hbr0 Htyp0]]; simpl in Htyp0 end.
      exists (apply_sub σ br0). split.
      * unfold branch in *. rewrite nth_error_map. rewrite Hbr0. simpl. auto.
      * rewrite Forall_forall in H.
        assert (Hin: In br0 brs) by (eapply nth_error_In; eauto).
        specialize (H br0 Hin).
        rewrite repeat_length in Htyp0.
        assert (Hbr := H _ _ _ Htyp0 _ _ Hgood).
        rewrite apply_sub_branch_type in Hbr.
        cbv zeta. rewrite repeat_length. exact Hbr.
Qed.

Lemma good_sub_single : forall Σenv Γ A u,
  has_type Σenv Γ u A -> good_sub Σenv Γ (A :: Γ) (scons u ids).
Proof.
  unfold good_sub. intros Σenv Γ A u H x B Hlook.
  destruct x; simpl in Hlook.
  - injection Hlook; intros; subst.
    assert (Heq: apply_sub (scons u ids) (shift1 A) = A) by exact (subst0_shift1 u A).
    rewrite Heq. auto.
  - destruct (ctx_lookup Γ x) eqn:E; simpl in Hlook; [|discriminate].
    injection Hlook; intros; subst. simpl.
    assert (Heq : apply_sub (scons u ids) (shift1 t) = t) by exact (subst0_shift1 u t).
    rewrite Heq. constructor. auto.
Qed.

Lemma subst_typing : forall Σenv Γ A t T u,
  has_type Σenv (A :: Γ) t T -> has_type Σenv Γ u A ->
  has_type Σenv Γ (subst0 u t) (subst0 u T).
Proof.
  intros. unfold subst0. eapply typing_sub; eauto. apply good_sub_single. auto.
Qed.

Lemma subst0_mk_pis_ind : forall n I s body,
  subst0 s (mk_pis (repeat (tInd I) n) body) =
  mk_pis (repeat (tInd I) n) (apply_sub (Nat.iter n up_sub (scons s ids)) body).
Proof.
  intros. unfold subst0. apply apply_sub_mk_pis_ind.
Qed.

Lemma apps_correct_type : forall args Σenv Γ I c C i,
  Forall (fun a => has_type Σenv Γ a (tInd I)) args ->
  has_type Σenv (tInd I :: Γ) C (tSort i) ->
  forall f,
  has_type Σenv Γ f (mk_pis (repeat (tInd I) (length args)) (motive_inst I c (length args) C)) ->
  has_type Σenv Γ (apps f args) (subst0 (tRoll I c args) C).
Proof. Admitted.

Lemma canonical_pi : forall Σenv t A B,
  has_type Σenv [] t (tPi A B) -> value t -> exists A' body, t = tLam A' body.
Proof. intros. inversion H0; subst; inversion H; subst; eauto. Qed.

Lemma canonical_ind : forall Σenv t I,
  has_type Σenv [] t (tInd I) -> value t -> exists c args, t = tRoll I c args.
Proof. intros. inversion H0; subst; inversion H; subst; eauto. Qed.

Lemma ctx_lookup_nil : forall x, ctx_lookup [] x = None.
Proof. destruct x; reflexivity. Qed.

Theorem preservation :
  forall Σenv Γ t t' T,
    has_type Σenv Γ t T -> step t t' -> has_type Σenv Γ t' T.
Proof.
  intros Σenv Γ t t' T Htype Hstep.
  revert T Htype. induction Hstep; intros.
  - inversion Htype; subst.
    match goal with H : has_type _ _ (tLam _ _) _ |- _ => inversion H; subst end.
    eapply subst_typing; eauto.
  - inversion Htype; subst. econstructor; eauto.
  - inversion Htype; subst.
    match goal with HA : has_type _ _ _ (tSort _), Ht : has_type _ (_ :: _) _ (shift1 _) |- _ =>
      assert (Hfix : has_type Σenv Γ (tFix T t) T) by (econstructor; eauto);
      pose proof (subst_typing _ _ _ _ _ _ Ht Hfix) as Hsub;
      rewrite subst0_shift1 in Hsub; exact Hsub
    end.
  - admit.
  - admit. (* step_case_roll - uses apps_correct_type *)
Admitted.

Theorem progress :
  forall Σenv t T,
    has_type Σenv [] t T -> value t \/ exists t', step t t'.
Proof. Admitted.
