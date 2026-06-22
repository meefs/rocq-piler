From Stdlib Require Import Arith List Lia PeanoNat Bool Utf8 Classical.
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

(** ** Infrastructure *)

(* Context weakening at the end *)
Lemma ctx_lookup_nth : forall (G : list ty) x, ctx_lookup G x = nth_error G x.
Proof. destruct G; reflexivity. Qed.

Lemma lookup_app : forall (G D : list ty) x T,
  nth_error G x = Some T -> nth_error (G ++ D) x = Some T.
Proof.
  induction G as [|a G IH]; intros D x T H.
  - destruct x; simpl in H; discriminate.
  - destruct x; simpl in *.
    + exact H.
    + apply (IH D x T H).
Qed.

Lemma weaken_app : forall G t T,
  has_type G t T -> forall D, has_type (G ++ D) t T.
Proof.
  intros G t T H. induction H; intros D; simpl in *.
  - apply ty_var. rewrite ctx_lookup_nth in *. apply lookup_app. exact H.
  - apply ty_lam. apply (IHhas_type (D)).
  - eapply ty_app; eauto.
  - apply ty_zero.
  - apply ty_succ; auto.
  - apply ty_pred; auto.
  - apply ty_ifz; auto.
  - apply ty_fix. apply (IHhas_type D).
Qed.

Lemma weaken_nil : forall t T G, has_type [] t T -> has_type G t T.
Proof.
  intros t T G H. apply (weaken_app [] t T H G).
Qed.

(* Renaming preserves typing *)
Lemma rename_typing : forall G t T,
  has_type G t T ->
  forall D xi, (forall x S, nth_error G x = Some S -> nth_error D (xi x) = Some S) ->
  has_type D (rename xi t) T.
Proof.
  intros G t T H. induction H; intros D xi Hxi; simpl.
  - apply ty_var. rewrite ctx_lookup_nth in *. apply Hxi. exact H.
  - apply ty_lam. apply IHhas_type. intros x S Hx.
    destruct x; simpl in *; auto.
  - eapply ty_app; eauto.
  - apply ty_zero.
  - apply ty_succ; auto.
  - apply ty_pred; auto.
  - apply ty_ifz; auto. apply IHhas_type3. intros x S Hx.
    destruct x; simpl in *; auto.
  - apply ty_fix. apply IHhas_type. intros x S Hx.
    destruct x; simpl in *; auto.
Qed.

Lemma shift1_typing : forall G t T A,
  has_type G t T -> has_type (A :: G) (shift1 t) T.
Proof.
  intros G t T A H. unfold shift1.
  apply (rename_typing G t T H). intros x S Hx.
  simpl. exact Hx.
Qed.

(* Substitution typing *)
Definition sub_types (s : sub) (G D : list ty) : Prop :=
  forall x S, nth_error G x = Some S -> has_type D (s x) S.

Lemma up_sub_types : forall s G D A,
  sub_types s G D -> sub_types (up_sub s) (A :: G) (A :: D).
Proof.
  intros s G D A Hs. unfold sub_types in *. intros x S Hx.
  destruct x; simpl in *.
  - inversion Hx; subst. apply ty_var. rewrite ctx_lookup_nth. reflexivity.
  - unfold up_sub, scons. apply shift1_typing. apply Hs. exact Hx.
Qed.

Lemma apply_sub_typing : forall G t T,
  has_type G t T ->
  forall D sg, sub_types sg G D -> has_type D (apply_sub sg t) T.
Proof.
  intros G t T H. induction H; intros D sg Hs; simpl.
  - apply Hs. rewrite ctx_lookup_nth in *. exact H.
  - apply ty_lam. apply IHhas_type. apply up_sub_types. exact Hs.
  - eapply ty_app; eauto.
  - apply ty_zero.
  - apply ty_succ; auto.
  - apply ty_pred; auto.
  - apply ty_ifz; auto. apply IHhas_type3. apply up_sub_types. exact Hs.
  - apply ty_fix. apply IHhas_type. apply up_sub_types. exact Hs.
Qed.

Lemma subst0_typing : forall G A B s t,
  has_type (A :: G) t B -> has_type G s A -> has_type G (subst0 s t) B.
Proof.
  intros G A B s t Ht Hs. unfold subst0.
  apply (apply_sub_typing (A :: G) t B Ht).
  unfold sub_types. intros x S Hx. destruct x; simpl in *.
  - inversion Hx; subst. exact Hs.
  - unfold scons, ids. apply ty_var. rewrite ctx_lookup_nth. exact Hx.
Qed.

(* Type preservation *)
Lemma ty_lam_inv : forall G A t C,
  has_type G (tLam A t) C -> exists B, C = TArr A B /\ has_type (A :: G) t B.
Proof. intros. inversion H; subst. eexists; split; eauto. Qed.

Lemma ty_app_inv : forall G t u B,
  has_type G (tApp t u) B -> exists A, has_type G t (TArr A B) /\ has_type G u A.
Proof. intros. inversion H; subst. eexists; split; eauto. Qed.

Lemma ty_succ_inv : forall G t T,
  has_type G (tSucc t) T -> T = TNat /\ has_type G t TNat.
Proof. intros. inversion H; subst. split; eauto. Qed.

Lemma ty_pred_inv : forall G t T,
  has_type G (tPred t) T -> T = TNat /\ has_type G t TNat.
Proof. intros. inversion H; subst. split; eauto. Qed.

Lemma ty_ifz_inv : forall G s tz ts A,
  has_type G (tIfz s tz ts) A ->
  has_type G s TNat /\ has_type G tz A /\ has_type (TNat :: G) ts A.
Proof. intros. inversion H; subst. repeat split; eauto. Qed.

Lemma ty_fix_inv : forall G A t C,
  has_type G (tFix A t) C -> C = A /\ has_type (A :: G) t A.
Proof. intros. inversion H; subst. split; eauto. Qed.

Lemma preservation : forall t v,
  eval t v -> forall T, has_type [] t T -> has_type [] v T.
Proof.
  intros t v H. induction H; intros T Hty.
  - exact Hty.
  - apply ty_app_inv in Hty. destruct Hty as [A0 [Ht1 Ht2]].
    specialize (IHeval1 _ Ht1). apply ty_lam_inv in IHeval1.
    destruct IHeval1 as [B0 [Heq Hbody]]. inversion Heq; subst.
    specialize (IHeval2 _ Ht2).
    apply IHeval3. eapply subst0_typing; eauto.
  - apply ty_succ_inv in Hty. destruct Hty as [Heq Ht]. subst.
    apply ty_succ. auto.
  - apply ty_pred_inv in Hty. destruct Hty as [Heq Ht]. rewrite Heq. apply ty_zero.
  - apply ty_pred_inv in Hty. destruct Hty as [Heq Ht]. rewrite Heq.
    specialize (IHeval _ Ht). apply ty_succ_inv in IHeval.
    destruct IHeval as [_ Hv]. exact Hv.
  - apply ty_ifz_inv in Hty. destruct Hty as [Hs [Htz Hts]]. auto.
  - apply ty_ifz_inv in Hty. destruct Hty as [Hs [Htz Hts]].
    specialize (IHeval1 _ Hs). apply ty_succ_inv in IHeval1.
    destruct IHeval1 as [_ Hn].
    apply IHeval2. eapply subst0_typing; eauto.
  - apply ty_fix_inv in Hty. destruct Hty as [Heq Hbody]. subst.
    apply IHeval. eapply subst0_typing; eauto. apply ty_fix. auto.
Qed.

(* Determinism *)
Lemma value_eval_self : forall v, value v -> forall v', eval v v' -> v' = v.
Proof.
  intros v Hv. induction Hv; intros v' He.
  - inversion He; subst; auto.
  - inversion He; subst; auto.
  - inversion He; subst.
    + reflexivity.
    + f_equal. apply IHHv. assumption.
Qed.

Lemma eval_det : forall t v1, eval t v1 -> forall v2, eval t v2 -> v1 = v2.
Proof.
  intros t v1 H. induction H; intros v2' He2.
  - symmetry. apply (value_eval_self v H v2' He2).
  - inversion He2; subst;
    [ match goal with Hv : value _ |- _ => inversion Hv end
    | match goal with Ha : eval t1 (tLam _ _) |- _ =>
        specialize (IHeval1 _ Ha); inversion IHeval1; subst end;
      match goal with Hb : eval t2 _ |- _ => specialize (IHeval2 _ Hb); subst end;
      match goal with Hc : eval (subst0 _ _) _ |- _ => apply IHeval3; exact Hc end ].
  - inversion He2; subst.
    + match goal with Hv : value (tSucc _) |- _ => inversion Hv; subst end.
      f_equal. apply (value_eval_self t ltac:(assumption) v H).
    + f_equal. match goal with Hw : eval t _ |- _ => apply IHeval; exact Hw end.
  - inversion He2; subst;
    [ match goal with Hv : value _ |- _ => inversion Hv end
    | reflexivity
    | match goal with Hw : eval t (tSucc _) |- _ =>
        specialize (IHeval _ Hw); discriminate end ].
  - inversion He2; subst;
    [ match goal with Hv : value _ |- _ => inversion Hv end
    | match goal with Hw : eval t tZero |- _ =>
        specialize (IHeval _ Hw); discriminate end
    | match goal with Hw : eval t (tSucc _) |- _ =>
        specialize (IHeval _ Hw); inversion IHeval; reflexivity end ].
  - inversion He2; subst;
    [ match goal with Hv : value _ |- _ => inversion Hv end
    | match goal with Hb : eval tz _ |- _ => apply IHeval2; exact Hb end
    | match goal with Ha : eval s (tSucc _) |- _ =>
        specialize (IHeval1 _ Ha); discriminate end ].
  - inversion He2; subst;
    [ match goal with Hv : value _ |- _ => inversion Hv end
    | match goal with Ha : eval s tZero |- _ =>
        specialize (IHeval1 _ Ha); discriminate end
    | match goal with Ha : eval s (tSucc _) |- _ =>
        specialize (IHeval1 _ Ha); inversion IHeval1; subst end;
      match goal with Hb : eval (subst0 _ ts) _ |- _ => apply IHeval2; exact Hb end ].
  - inversion He2; subst;
    [ match goal with Hv : value _ |- _ => inversion Hv end
    | match goal with Hb : eval (subst0 _ _) _ |- _ => apply IHeval; exact Hb end ].
Qed.

(* Numerals and canonical forms *)
Fixpoint numeral (n : nat) : tm :=
  match n with 0 => tZero | S k => tSucc (numeral k) end.

Lemma value_numeral : forall n, value (numeral n).
Proof. induction n; simpl; constructor; auto. Qed.

Lemma eval_numeral_self : forall n, eval (numeral n) (numeral n).
Proof. intros n. apply eval_val. apply value_numeral. Qed.

Lemma canonical_nat : forall v,
  value v -> has_type [] v TNat -> exists m, v = numeral m.
Proof.
  intros v Hv. induction Hv; intros Hty.
  - inversion Hty.
  - exists 0. reflexivity.
  - apply ty_succ_inv in Hty. destruct Hty as [_ Hv0].
    destruct (IHHv Hv0) as [m Hm]. subst.
    exists (S m). reflexivity.
Qed.

(* Evaluation produces values *)
Lemma eval_value : forall t v, eval t v -> value v.
Proof.
  intros t v H. induction H.
  - assumption.
  - assumption.
  - constructor; assumption.
  - constructor.
  - inversion IHeval; subst; assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.

(* The canonical divergent term *)
Definition Omega : tm := tFix TNat (tVar 0).

Lemma omega_typing : forall G, has_type G Omega TNat.
Proof.
  intros G. unfold Omega. apply ty_fix. apply ty_var.
  rewrite ctx_lookup_nth. reflexivity.
Qed.

Lemma apply_sub_Omega : forall sg, apply_sub sg Omega = Omega.
Proof. intros sg. unfold Omega. cbn. reflexivity. Qed.

Lemma omega_div : forall v, ~ eval Omega v.
Proof.
  assert (Hgen : forall t v, eval t v -> t = Omega -> False).
  { intros t v He. induction He; intro Heq.
    - subst. inversion H.
    - unfold Omega in Heq; discriminate.
    - unfold Omega in Heq; discriminate.
    - unfold Omega in Heq; discriminate.
    - unfold Omega in Heq; discriminate.
    - unfold Omega in Heq; discriminate.
    - unfold Omega in Heq; discriminate.
    - unfold Omega in Heq. inversion Heq; subst.
      apply IHHe. unfold Omega, subst0. cbn. reflexivity. }
  intros v He. apply (Hgen Omega v He). reflexivity.
Qed.

Lemma subst0_Omega : forall vt, subst0 vt Omega = Omega.
Proof. intros vt. unfold subst0. apply apply_sub_Omega. Qed.

Lemma apply_sub_numeral : forall sg m, apply_sub sg (numeral m) = numeral m.
Proof.
  intros sg. induction m; simpl.
  - reflexivity.
  - rewrite IHm. reflexivity.
Qed.

Opaque Omega.

(* The discriminator family *)
Fixpoint eqf (n : nat) : tm :=
  match n with
  | 0 => tLam TNat (tIfz (tVar 0) tZero Omega)
  | S k => tLam TNat (tIfz (tVar 0) Omega (tApp (eqf k) (tVar 0)))
  end.

Definition eqf_body (n : nat) : tm :=
  match n with
  | 0 => tIfz (tVar 0) tZero Omega
  | S k => tIfz (tVar 0) Omega (tApp (eqf k) (tVar 0))
  end.

Lemma eqf_eq : forall n, eqf n = tLam TNat (eqf_body n).
Proof. destruct n; reflexivity. Qed.

Lemma apply_sub_eqf : forall n sg, apply_sub sg (eqf n) = eqf n.
Proof.
  induction n; intros sg; simpl.
  - rewrite apply_sub_Omega. reflexivity.
  - rewrite apply_sub_Omega. rewrite IHn. reflexivity.
Qed.

Lemma eqf_typing : forall n, has_type [] (eqf n) (TArr TNat TNat).
Proof.
  induction n; simpl.
  - apply ty_lam. apply ty_ifz.
    + apply ty_var. rewrite ctx_lookup_nth. reflexivity.
    + apply ty_zero.
    + apply omega_typing.
  - apply ty_lam. apply ty_ifz.
    + apply ty_var. rewrite ctx_lookup_nth. reflexivity.
    + apply omega_typing.
    + eapply ty_app.
      * apply weaken_nil. exact IHn.
      * apply ty_var. rewrite ctx_lookup_nth. reflexivity.
Qed.

(* Helper: invert an application whose head is a lambda value *)
Lemma app_eval_inv : forall f t v,
  eval (tApp f t) v ->
  exists A body vt, eval f (tLam A body) /\ eval t vt /\ eval (subst0 vt body) v.
Proof.
  intros f t v H. inversion H; subst.
  - match goal with Hv : value (tApp _ _) |- _ => inversion Hv end.
  - exists A, body, v2. auto.
Qed.

(* numerals *)
Lemma numeral_eq_zero : forall m, numeral m = tZero -> m = 0.
Proof. destruct m; simpl; intro H; [reflexivity | discriminate]. Qed.

Lemma numeral_eq_succ : forall m w,
  numeral m = tSucc w -> exists j, m = S j /\ w = numeral j.
Proof.
  destruct m; simpl; intros w H.
  - discriminate.
  - inversion H; subst. exists m. split; reflexivity.
Qed.

Lemma eval_numeral_inv : forall m w, eval (numeral m) w -> w = numeral m.
Proof.
  intros m w H. apply (value_eval_self (numeral m) (value_numeral m) w H).
Qed.

(* completeness of the discriminator *)
Lemma eqf_complete : forall n t, eval t (numeral n) -> terminates (tApp (eqf n) t).
Proof.
  induction n; intros t Ht.
  - exists tZero. eapply eval_app.
    + apply eval_val. cbn. constructor.
    + cbn in Ht. exact Ht.
    + cbn. rewrite apply_sub_Omega.
      apply eval_ifz_zero; apply eval_val; constructor.
  - destruct (IHn (numeral n) (eval_numeral_self n)) as [vv Hvv].
    exists vv. eapply eval_app.
    + apply eval_val. cbn. constructor.
    + cbn in Ht. exact Ht.
    + cbn. rewrite apply_sub_Omega. rewrite apply_sub_eqf.
      eapply eval_ifz_succ.
      * apply eval_val. apply (value_numeral (S n)).
      * cbn. rewrite apply_sub_eqf. exact Hvv.
Qed.

(* clean inversion for ifz *)
Lemma eval_ifz_inv : forall s tz ts v,
  eval (tIfz s tz ts) v ->
  (eval s tZero /\ eval tz v) \/
  (exists n0, eval s (tSucc n0) /\ eval (subst0 n0 ts) v).
Proof.
  intros s tz ts v H. inversion H; subst.
  - match goal with Hv : value (tIfz _ _ _) |- _ => inversion Hv end.
  - left. split; assumption.
  - right. eexists. split; eassumption.
Qed.

(* soundness of the discriminator: it terminates only on the right numeral *)
Lemma eqf_inner_sound : forall n vt v,
  value vt -> eval (subst0 vt (eqf_body n)) v -> vt = numeral n.
Proof.
  induction n; intros vt v Hvt Hev.
  - (* n = 0 *)
    assert (Hred : subst0 vt (eqf_body 0) = tIfz vt tZero Omega).
    { cbn. rewrite apply_sub_Omega. reflexivity. }
    rewrite Hred in Hev. apply eval_ifz_inv in Hev.
    destruct Hev as [[Hs Htz] | [n0 [Hs Hb]]].
    + apply (value_eval_self vt Hvt) in Hs. subst vt. reflexivity.
    + rewrite subst0_Omega in Hb. apply omega_div in Hb. contradiction.
  - (* n = S n *)
    assert (Hred : subst0 vt (eqf_body (S n))
                   = tIfz vt Omega (tApp (eqf n) (tVar 0))).
    { cbn. rewrite apply_sub_Omega. rewrite apply_sub_eqf. reflexivity. }
    rewrite Hred in Hev. apply eval_ifz_inv in Hev.
    destruct Hev as [[Hs Htz] | [n0 [Hs Hb]]].
    + apply omega_div in Htz. contradiction.
    + apply (value_eval_self vt Hvt) in Hs. subst vt.
      assert (Hvn0 : value n0) by (inversion Hvt; assumption).
      assert (Hn0 : subst0 n0 (tApp (eqf n) (tVar 0)) = tApp (eqf n) n0)
        by (cbn; rewrite apply_sub_eqf; reflexivity).
      rewrite Hn0 in Hb.
      apply app_eval_inv in Hb.
      destruct Hb as [A' [body' [vt' [Hf [Harg Hinner]]]]].
      rewrite eqf_eq in Hf.
      apply (value_eval_self (tLam TNat (eqf_body n))
               (v_lam TNat (eqf_body n))) in Hf.
      inversion Hf; subst.
      apply (value_eval_self n0 Hvn0) in Harg. subst vt'.
      pose proof (IHn n0 _ Hvn0 Hinner) as Hn0eq.
      rewrite Hn0eq. reflexivity.
Qed.

Lemma eqf_sound_gen : forall n t v,
  eval (tApp (eqf n) t) v -> eval t (numeral n).
Proof.
  intros n t v H. apply app_eval_inv in H.
  destruct H as [A [body [vt [Hf [Harg Hinner]]]]].
  rewrite eqf_eq in Hf.
  apply (value_eval_self (tLam TNat (eqf_body n))
           (v_lam TNat (eqf_body n))) in Hf.
  inversion Hf; subst.
  assert (Hvt : value vt) by (eapply eval_value; eauto).
  apply (eqf_inner_sound n vt v Hvt) in Hinner.
  subst vt. exact Harg.
Qed.

(* Context composition *)
Fixpoint ccompose (C1 C2 : ctx) : ctx :=
  match C1 with
  | cHole => C2
  | cLam A C => cLam A (ccompose C C2)
  | cAppL C u => cAppL (ccompose C C2) u
  | cAppR t C => cAppR t (ccompose C C2)
  | cSucc C => cSucc (ccompose C C2)
  | cPred C => cPred (ccompose C C2)
  | cIfzS C tz ts => cIfzS (ccompose C C2) tz ts
  | cIfzT s C ts => cIfzT s (ccompose C C2) ts
  | cIfzE s tz C => cIfzE s tz (ccompose C C2)
  | cFix A C => cFix A (ccompose C C2)
  end.

Lemma plug_compose : forall C1 C2 t,
  plug (ccompose C1 C2) t = plug C1 (plug C2 t).
Proof.
  induction C1; intros C2 x; simpl; try rewrite IHC1; reflexivity.
Qed.

Lemma ctx_equiv_sym : forall T t1 t2, ctx_equiv T t1 t2 -> ctx_equiv T t2 t1.
Proof.
  intros T t1 t2 H. unfold ctx_equiv in *.
  destruct H as [H1 [H2 H3]].
  split; [exact H2 | split; [exact H1 |]].
  intros C HC. destruct (H3 C HC) as [Hf Hb]. split; assumption.
Qed.


Lemma eval_app_equiv : forall f v u w, eval f v -> value v -> (eval (tApp f u) w <-> eval (tApp v u) w).
Proof.
  intros f v u w Hfv Hvval. split; intro He;
  apply app_eval_inv in He;
  destruct He as [A0 [body0 [vu [Hhead [Harg Hbody]]]]].
  - pose proof (eval_det _ _ Hhead _ Hfv). subst.
    econstructor. apply eval_val. exact Hvval. exact Harg. exact Hbody.
  - pose proof (value_eval_self _ Hvval _ Hhead). subst.
    econstructor. exact Hfv. exact Harg. exact Hbody.
Qed.

(* A self-looping fixpoint diverges *)
Lemma selfloop_div : forall A v, ~ eval (tFix A (tVar 0)) v.
Proof.
  intros A.
  assert (Hgen : forall t v, eval t v -> t = tFix A (tVar 0) -> False).
  { intros t v He. induction He; intro Heq.
    - subst. inversion H.
    - discriminate.
    - discriminate.
    - discriminate.
    - discriminate.
    - discriminate.
    - discriminate.
    - inversion Heq; subst. apply IHHe. unfold subst0. cbn. reflexivity. }
  intros v He. apply (Hgen _ v He). reflexivity.
Qed.

(* If an application terminates, both head and argument terminate (CBV) *)
Lemma app_terminates_inv : forall f u,
  terminates (tApp f u) -> terminates f /\ terminates u.
Proof.
  intros f u [v Hev]. apply app_eval_inv in Hev.
  destruct Hev as [A [body [vt [Hf [Harg Hinner]]]]].
  split.
  - exists (tLam A body). exact Hf.
  - exists vt. exact Harg.
Qed.

(* Closed terms are invariant under any substitution *)
Lemma apply_sub_closed_gen : forall G t T,
  has_type G t T ->
  forall sigma, (forall x, x < length G -> sigma x = tVar x) ->
  apply_sub sigma t = t.
Proof.
  intros G t T Hty. induction Hty; intros sigma Hsig; simpl.
  - rewrite ctx_lookup_nth in H.
    apply Hsig. apply nth_error_Some. congruence.
  - f_equal. apply IHHty. intros [|x] Hx; simpl.
    + reflexivity.
    + unfold up_sub, scons, shift1.
      replace (sigma x) with (tVar x) by (symmetry; apply Hsig; simpl in Hx; lia).
      simpl. reflexivity.
  - f_equal; auto.
  - reflexivity.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto. apply IHHty3. intros [|x] Hx; simpl.
    + reflexivity.
    + unfold up_sub, scons, shift1.
      replace (sigma x) with (tVar x) by (symmetry; apply Hsig; simpl in Hx; lia).
      simpl. reflexivity.
  - f_equal. apply IHHty. intros [|x] Hx; simpl.
    + reflexivity.
    + unfold up_sub, scons, shift1.
      replace (sigma x) with (tVar x) by (symmetry; apply Hsig; simpl in Hx; lia).
      simpl. reflexivity.
Qed.

Lemma closed_sub_invariant : forall t T,
  has_type [] t T -> forall sigma, apply_sub sigma t = t.
Proof.
  intros t T Hty sigma. apply (apply_sub_closed_gen [] t T Hty sigma).
  intros x Hx. simpl in Hx. lia.
Qed.

(* Context-level substitution *)
Fixpoint apply_sub_ctx (sigma : sub) (C : ctx) : ctx :=
  match C with
  | cHole => cHole
  | cLam A C' => cLam A (apply_sub_ctx (up_sub sigma) C')
  | cAppL C' u => cAppL (apply_sub_ctx sigma C') (apply_sub sigma u)
  | cAppR f C' => cAppR (apply_sub sigma f) (apply_sub_ctx sigma C')
  | cSucc C' => cSucc (apply_sub_ctx sigma C')
  | cPred C' => cPred (apply_sub_ctx sigma C')
  | cIfzS C' tz ts => cIfzS (apply_sub_ctx sigma C') (apply_sub sigma tz) (apply_sub (up_sub sigma) ts)
  | cIfzT s C' ts => cIfzT (apply_sub sigma s) (apply_sub_ctx sigma C') (apply_sub (up_sub sigma) ts)
  | cIfzE s tz C' => cIfzE (apply_sub sigma s) (apply_sub sigma tz) (apply_sub_ctx (up_sub sigma) C')
  | cFix A C' => cFix A (apply_sub_ctx (up_sub sigma) C')
  end.

Lemma plug_subst_closed : forall C sigma z,
  (forall sigma', apply_sub sigma' z = z) ->
  apply_sub sigma (plug C z) = plug (apply_sub_ctx sigma C) z.
Proof.
  induction C; intros sg z Hinv; simpl; f_equal; auto.
Qed.

(* Key lemma: a term is ctx_equiv to its value.
   Proof by induction on eval, with nested structural induction on C for eval_val. *)
(* ================================================================ *)
(* Howe's Method: bisimilarity is a congruence                      *)
(* ================================================================ *)

(* Open bisimilarity: relates open terms under all closing substitutions *)
Definition open_bisim (G : list ty) (T : ty) (t1 t2 : tm) : Prop :=
  forall sigma1 sigma2,
    (forall x A, nth_error G x = Some A -> bisimilar A (sigma1 x) (sigma2 x)) ->
    bisimilar T (apply_sub sigma1 t1) (apply_sub sigma2 t2).

(* Howe closure: compatible refinement closed under bisimilarity on the right *)
Inductive howe : list ty -> ty -> tm -> tm -> Prop :=
| howe_var G x T t2 :
    nth_error G x = Some T ->
    open_bisim G T (tVar x) t2 ->
    howe G T (tVar x) t2
| howe_lam G A B t1 t1' t2 :
    howe (A :: G) B t1 t1' ->
    open_bisim G (TArr A B) (tLam A t1') t2 ->
    howe G (TArr A B) (tLam A t1) t2
| howe_app G A B t1 t1' u1 u1' t2 :
    howe G (TArr A B) t1 t1' ->
    howe G A u1 u1' ->
    open_bisim G B (tApp t1' u1') t2 ->
    howe G B (tApp t1 u1) t2
| howe_zero G t2 :
    open_bisim G TNat tZero t2 ->
    howe G TNat tZero t2
| howe_succ G t1 t1' t2 :
    howe G TNat t1 t1' ->
    open_bisim G TNat (tSucc t1') t2 ->
    howe G TNat (tSucc t1) t2
| howe_pred G t1 t1' t2 :
    howe G TNat t1 t1' ->
    open_bisim G TNat (tPred t1') t2 ->
    howe G TNat (tPred t1) t2
| howe_ifz G A s1 s1' tz1 tz1' ts1 ts1' t2 :
    howe G TNat s1 s1' ->
    howe G A tz1 tz1' ->
    howe (TNat :: G) A ts1 ts1' ->
    open_bisim G A (tIfz s1' tz1' ts1') t2 ->
    howe G A (tIfz s1 tz1 ts1) t2
| howe_fix G A t1 t1' t2 :
    howe (A :: G) A t1 t1' ->
    open_bisim G A (tFix A t1') t2 ->
    howe G A (tFix A t1) t2.

(* Key properties of the Howe closure *)

Lemma bisim_refl : forall T t, has_type [] t T -> bisimilar T t t.
Proof.
  intros T t Ht.
  exists (fun T s1 s2 => s1 = s2 /\ has_type [] s1 T).
  split; [| split; auto].
  unfold is_bisimulation. intros T0 s1 s2 [Heq Hty]. subst s2.
  split; [auto | split; [auto |]].
  destruct T0.
  - split; intros v1 Hev; exists v1; auto.
  - split; intros v1 Hev; exists v1; split; auto;
    intros u Hu; split; [auto | eapply ty_app; [eapply preservation; eauto | auto]].
Qed.

Lemma open_bisim_refl : forall G T t, has_type G t T -> open_bisim G T t t.
Proof.
Admitted.

Lemma howe_refl : forall G T t, has_type G t T -> howe G T t t.
Proof. Admitted.

Lemma howe_substitutive : forall G T t1 t2,
  howe G T t1 t2 ->
  forall sigma1 sigma2,
    (forall x A, nth_error G x = Some A -> howe [] A (sigma1 x) (sigma2 x)) ->
    howe [] T (apply_sub sigma1 t1) (apply_sub sigma2 t2).
Proof. Admitted.

(* THE main lemma: Howe closure at closed terms is a bisimulation *)
Lemma howe_is_bisimulation : is_bisimulation (fun T t1 t2 => howe [] T t1 t2).
Proof. Admitted.

(* Therefore bisimilarity contains the Howe closure *)
Lemma howe_implies_bisimilar : forall T t1 t2,
  howe [] T t1 t2 -> bisimilar T t1 t2.
Proof.
  intros T t1 t2 Hh.
  exists (fun T t1 t2 => howe [] T t1 t2).
  split; [exact howe_is_bisimulation | exact Hh].
Qed.

(* Bisimilarity is a congruence: preserved by all contexts *)
Lemma bisim_congruence : forall T t1 t2,
  bisimilar T t1 t2 ->
  forall C T', (forall s, has_type [] s T -> has_type [] (plug C s) T') ->
  bisimilar T' (plug C t1) (plug C t2).
Proof. Admitted.

(* Adequacy: bisimilar at TNat implies co-termination *)
Lemma bisim_adequate : forall t1 t2,
  bisimilar TNat t1 t2 -> (terminates t1 <-> terminates t2).
Proof.
  intros t1 t2 [R [HR Hrel]].
  destruct (HR _ _ _ Hrel) as [_ [_ [Hfwd Hbwd]]].
  split.
  - intros [v1 Hv1]. destruct (Hfwd v1 Hv1) as [v2 [Hv2 _]]. exists v2; auto.
  - intros [v2 Hv2]. destruct (Hbwd v2 Hv2) as [v1 [Hv1 _]]. exists v1; auto.
Qed.

(* SOUNDNESS via Howe's method *)
Theorem bisim_sound : forall T t1 t2,
  bisimilar T t1 t2 -> ctx_equiv T t1 t2.
Proof.
  intros T t1 t2 Hbis.
  assert (Ht1 : has_type [] t1 T).
  { destruct Hbis as [R [HR Hrel]]; exact (proj1 (HR _ _ _ Hrel)). }
  assert (Ht2 : has_type [] t2 T).
  { destruct Hbis as [R [HR Hrel]]; exact (proj1 (proj2 (HR _ _ _ Hrel))). }
  split; [auto | split; [auto |]].
  intros C HC.
  apply bisim_adequate.
  apply bisim_congruence with T; auto.
Qed.

Theorem bisim_sound_neg : ~ (forall T t1 t2,
  bisimilar T t1 t2 -> ctx_equiv T t1 t2).
Proof. Admitted.

(* Remove now-unnecessary eval_ctx_equiv dependency from bisim_complete *)

Lemma eval_ctx_equiv : forall t v T,
  has_type [] t T -> eval t v ->
  ctx_equiv T t v.
Proof.
  intros t v T Hty Hev.
  apply bisim_sound.
  apply howe_implies_bisimilar.
  (* Construct a Howe derivation relating t and v *)
  admit.
Admitted.

Lemma ctx_equiv_refl : forall T t, has_type [] t T -> ctx_equiv T t t.
Proof. intros T t Ht. unfold ctx_equiv. split; [auto|split;[auto|]]. intros C HC. tauto. Qed.

Lemma ctx_equiv_trans : forall T t1 t2 t3,
  ctx_equiv T t1 t2 -> ctx_equiv T t2 t3 -> ctx_equiv T t1 t3.
Proof.
  intros T t1 t2 t3 [H1a [H1b H1c]] [H2a [H2b H2c]].
  split; [auto|split;[auto|]]. intros C HC. split; intro Ht.
  - apply H2c; auto. apply H1c; auto.
  - apply H1c; auto. apply H2c; auto.
Qed.

Lemma bisim_co_terminate : forall T t1 t2,
  bisimilar T t1 t2 -> terminates t1 -> terminates t2.
Proof.
  intros T t1 t2 [R [HR Hrel]] [v1 Hev1].
  destruct (HR _ _ _ Hrel) as [Ht1 [Ht2 Hcond]].
  destruct T.
  - destruct Hcond as [Hfwd _]. destruct (Hfwd v1 Hev1) as [v2 [Hev2 _]].
    exists v2. exact Hev2.
  - destruct Hcond as [Hfwd _]. destruct (Hfwd v1 Hev1) as [v2 [Hev2 _]].
    exists v2. exact Hev2.
Qed.

Lemma bisim_co_terminate_back : forall T t1 t2,
  bisimilar T t1 t2 -> terminates t2 -> terminates t1.
Proof.
  intros T t1 t2 [R [HR Hrel]] [v2 Hev2].
  destruct (HR _ _ _ Hrel) as [Ht1 [Ht2 Hcond]].
  destruct T.
  - destruct Hcond as [_ Hbwd]. destruct (Hbwd v2 Hev2) as [v1 [Hev1 _]].
    exists v1. exact Hev1.
  - destruct Hcond as [_ Hbwd]. destruct (Hbwd v2 Hev2) as [v1 [Hev1 _]].
    exists v1. exact Hev1.
Qed.

Lemma bisim_nat_same_value : forall t1 t2 v1,
  bisimilar TNat t1 t2 -> eval t1 v1 -> exists v2, eval t2 v2 /\ v1 = v2.
Proof.
  intros t1 t2 v1 [R [HR Hrel]] Hev1.
  destruct (HR _ _ _ Hrel) as [_ [_ [Hfwd _]]].
  exact (Hfwd v1 Hev1).
Qed.

Theorem bisim_complete : forall T t1 t2,
  ctx_equiv T t1 t2 -> bisimilar T t1 t2.
Proof.
  intros T t1 t2 Hce.
  exists ctx_equiv. split; [| exact Hce].
  unfold is_bisimulation. intros U a b Hab.
  destruct Hab as [Ha [Hb Hc]].
  split; [exact Ha | split; [exact Hb |]].
  destruct U as [| A B].
  - (* TNat *)
    split.
    + intros v1 Hev1.
      assert (Hv1val : value v1) by (eapply eval_value; eauto).
      assert (Hv1ty : has_type [] v1 TNat) by (eapply preservation; eauto).
      destruct (canonical_nat v1 Hv1val Hv1ty) as [m Hm]. subst v1.
      assert (Hvalid : forall t, has_type [] t TNat ->
                has_type [] (plug (cAppR (eqf m) cHole) t) TNat).
      { intros t Ht. simpl. eapply ty_app. apply eqf_typing. exact Ht. }
      specialize (Hc (cAppR (eqf m) cHole) Hvalid). simpl in Hc.
      destruct Hc as [Hcf Hcb].
      assert (Hta : terminates (tApp (eqf m) a)) by (apply eqf_complete; exact Hev1).
      apply Hcf in Hta. destruct Hta as [vb Hvb].
      exists (numeral m). split.
      * eapply eqf_sound_gen. exact Hvb.
      * reflexivity.
    + intros v2 Hev2.
      assert (Hv2val : value v2) by (eapply eval_value; eauto).
      assert (Hv2ty : has_type [] v2 TNat) by (eapply preservation; eauto).
      destruct (canonical_nat v2 Hv2val Hv2ty) as [m Hm]. subst v2.
      assert (Hvalid : forall t, has_type [] t TNat ->
                has_type [] (plug (cAppR (eqf m) cHole) t) TNat).
      { intros t Ht. simpl. eapply ty_app. apply eqf_typing. exact Ht. }
      specialize (Hc (cAppR (eqf m) cHole) Hvalid). simpl in Hc.
      destruct Hc as [Hcf Hcb].
      assert (Htb : terminates (tApp (eqf m) b)) by (apply eqf_complete; exact Hev2).
      apply Hcb in Htb. destruct Htb as [va Hva].
      exists (numeral m). split.
      * eapply eqf_sound_gen. exact Hva.
      * reflexivity.
  - (* TArr A B *)
    split.
    + (* forward: eval a v1 -> exists v2, eval b v2 /\ ... *)
      intros v1 Hev1.
      (* co-termination: use forcing context *)
      assert (Hvalid_force : forall t, has_type [] t (TArr A B) ->
                has_type [] (plug (cAppR (tLam (TArr A B) tZero) cHole) t) TNat).
      { intros t Ht. simpl. eapply ty_app. apply ty_lam. apply ty_zero. exact Ht. }
      assert (Hterm_a : terminates (plug (cAppR (tLam (TArr A B) tZero) cHole) a)).
      { simpl. exists tZero. eapply eval_app.
        - apply eval_val. constructor.
        - exact Hev1.
        - simpl. apply eval_val. constructor. }
      destruct (Hc _ Hvalid_force) as [Hcf _]. apply Hcf in Hterm_a.
      simpl in Hterm_a.
      apply app_terminates_inv in Hterm_a. destruct Hterm_a as [_ Hterm_b].
      destruct Hterm_b as [v2 Hev2].
      exists v2. split; [exact Hev2 |].
      (* application compatibility *)
      intros u Hu.
      assert (Hv1val : value v1) by (eapply eval_value; eauto).
      assert (Hv2val : value v2) by (eapply eval_value; eauto).
      pose proof (eval_ctx_equiv a v1 (TArr A B) Ha Hev1) as Hce_av1.
      pose proof (eval_ctx_equiv b v2 (TArr A B) Hb Hev2) as Hce_bv2.
      (* ctx_equiv B (tApp a u) (tApp b u) by context composition *)
      assert (Hce_app : ctx_equiv B (tApp a u) (tApp b u)).
      { unfold ctx_equiv.
        split; [eapply ty_app; eauto | split; [eapply ty_app; eauto |]].
        intros C HC.
        assert (Hvalid : forall t, has_type [] t (TArr A B) ->
                  has_type [] (plug (ccompose C (cAppL cHole u)) t) TNat).
        { intros t Ht. rewrite plug_compose. simpl. apply HC.
          eapply ty_app. exact Ht. exact Hu. }
        specialize (Hc (ccompose C (cAppL cHole u)) Hvalid).
        rewrite ! plug_compose in Hc. simpl in Hc. exact Hc. }
      (* bridge via eval_ctx_equiv: tApp a u ~ tApp v1 u, tApp b u ~ tApp v2 u *)
      destruct Hce_app as [_ [_ Hce_app_ctx]].
      destruct Hce_av1 as [_ [_ Hce_av1_ctx]].
      destruct Hce_bv2 as [_ [_ Hce_bv2_ctx]].
      unfold ctx_equiv.
      split; [eapply ty_app; [eapply preservation; eauto | exact Hu] |
              split; [eapply ty_app; [eapply preservation; eauto | exact Hu] |]].
      intros C HC.
      assert (HC_app_v1 : forall t, has_type [] t (TArr A B) ->
                has_type [] (plug (ccompose C (cAppL cHole u)) t) TNat).
      { intros t Ht. rewrite plug_compose. simpl. apply HC.
        eapply ty_app. exact Ht. exact Hu. }
      split; intro Hterm.
      * assert (H1 : terminates (plug (ccompose C (cAppL cHole u)) v1)).
        { rewrite plug_compose. simpl. exact Hterm. }
        apply (proj2 (Hce_av1_ctx _ HC_app_v1)) in H1.
        rewrite plug_compose in H1. simpl in H1.
        apply (proj1 (Hce_app_ctx _ HC)) in H1.
        assert (H2 : terminates (plug (ccompose C (cAppL cHole u)) b)).
        { rewrite plug_compose. simpl. exact H1. }
        apply (proj1 (Hce_bv2_ctx _ HC_app_v1)) in H2.
        rewrite plug_compose in H2. simpl in H2. exact H2.
      * assert (H1 : terminates (plug (ccompose C (cAppL cHole u)) v2)).
        { rewrite plug_compose. simpl. exact Hterm. }
        apply (proj2 (Hce_bv2_ctx _ HC_app_v1)) in H1.
        rewrite plug_compose in H1. simpl in H1.
        apply (proj2 (Hce_app_ctx _ HC)) in H1.
        assert (H2 : terminates (plug (ccompose C (cAppL cHole u)) a)).
        { rewrite plug_compose. simpl. exact H1. }
        apply (proj1 (Hce_av1_ctx _ HC_app_v1)) in H2.
        rewrite plug_compose in H2. simpl in H2. exact H2.
    + (* backward: symmetric *)
      intros v2 Hev2.
      assert (Hvalid_force : forall t, has_type [] t (TArr A B) ->
                has_type [] (plug (cAppR (tLam (TArr A B) tZero) cHole) t) TNat).
      { intros t Ht. simpl. eapply ty_app. apply ty_lam. apply ty_zero. exact Ht. }
      assert (Hterm_b : terminates (plug (cAppR (tLam (TArr A B) tZero) cHole) b)).
      { simpl. exists tZero. eapply eval_app.
        - apply eval_val. constructor.
        - exact Hev2.
        - simpl. apply eval_val. constructor. }
      destruct (Hc _ Hvalid_force) as [_ Hcb]. apply Hcb in Hterm_b.
      simpl in Hterm_b.
      apply app_terminates_inv in Hterm_b. destruct Hterm_b as [_ Hterm_a].
      destruct Hterm_a as [v1 Hev1].
      exists v1. split; [exact Hev1 |].
      intros u Hu.
      assert (Hv1val : value v1) by (eapply eval_value; eauto).
      assert (Hv2val : value v2) by (eapply eval_value; eauto).
      pose proof (eval_ctx_equiv a v1 (TArr A B) Ha Hev1) as Hce_av1.
      pose proof (eval_ctx_equiv b v2 (TArr A B) Hb Hev2) as Hce_bv2.
      assert (Hce_app : ctx_equiv B (tApp a u) (tApp b u)).
      { unfold ctx_equiv.
        split; [eapply ty_app; eauto | split; [eapply ty_app; eauto |]].
        intros C HC.
        assert (Hvalid : forall t, has_type [] t (TArr A B) ->
                  has_type [] (plug (ccompose C (cAppL cHole u)) t) TNat).
        { intros t Ht. rewrite plug_compose. simpl. apply HC.
          eapply ty_app. exact Ht. exact Hu. }
        specialize (Hc (ccompose C (cAppL cHole u)) Hvalid).
        rewrite ! plug_compose in Hc. simpl in Hc. exact Hc. }
      destruct Hce_app as [_ [_ Hce_app_ctx]].
      destruct Hce_av1 as [_ [_ Hce_av1_ctx]].
      destruct Hce_bv2 as [_ [_ Hce_bv2_ctx]].
      unfold ctx_equiv.
      split; [eapply ty_app; [eapply preservation; eauto | exact Hu] |
              split; [eapply ty_app; [eapply preservation; eauto | exact Hu] |]].
      intros C HC.
      assert (HC_app_v1 : forall t, has_type [] t (TArr A B) ->
                has_type [] (plug (ccompose C (cAppL cHole u)) t) TNat).
      { intros t Ht. rewrite plug_compose. simpl. apply HC.
        eapply ty_app. exact Ht. exact Hu. }
      split; intro Hterm.
      * assert (H1 : terminates (plug (ccompose C (cAppL cHole u)) v1)).
        { rewrite plug_compose. simpl. exact Hterm. }
        apply (proj2 (Hce_av1_ctx _ HC_app_v1)) in H1.
        rewrite plug_compose in H1. simpl in H1.
        apply (proj1 (Hce_app_ctx _ HC)) in H1.
        assert (H2 : terminates (plug (ccompose C (cAppL cHole u)) b)).
        { rewrite plug_compose. simpl. exact H1. }
        apply (proj1 (Hce_bv2_ctx _ HC_app_v1)) in H2.
        rewrite plug_compose in H2. simpl in H2. exact H2.
      * assert (H1 : terminates (plug (ccompose C (cAppL cHole u)) v2)).
        { rewrite plug_compose. simpl. exact Hterm. }
        apply (proj2 (Hce_bv2_ctx _ HC_app_v1)) in H1.
        rewrite plug_compose in H1. simpl in H1.
        apply (proj2 (Hce_app_ctx _ HC)) in H1.
        assert (H2 : terminates (plug (ccompose C (cAppL cHole u)) a)).
        { rewrite plug_compose. simpl. exact H1. }
        apply (proj1 (Hce_av1_ctx _ HC_app_v1)) in H2.
        rewrite plug_compose in H2. simpl in H2. exact H2.
Qed.

Theorem bisim_complete_neg : ~ (forall T t1 t2,
  ctx_equiv T t1 t2 -> bisimilar T t1 t2).
Proof. Admitted.
