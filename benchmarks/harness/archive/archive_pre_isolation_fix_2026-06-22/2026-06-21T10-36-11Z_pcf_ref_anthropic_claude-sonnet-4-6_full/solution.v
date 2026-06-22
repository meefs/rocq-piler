From Stdlib Require Import Arith List Lia.
Import ListNotations.

(** * PCF + References: Type Preservation — Benchmark *)

Inductive ty : Type :=
  | TyNat | TyBool | TyArrow : ty -> ty -> ty | TyRef : ty -> ty.

Inductive tm : Type :=
  | Var : nat -> tm | Num : nat -> tm | BOOL : bool -> tm
  | Succ : tm -> tm | Pred : tm -> tm | IsZero : tm -> tm
  | If : tm -> tm -> tm -> tm
  | Lam : ty -> tm -> tm | App : tm -> tm -> tm | Fix : tm -> tm
  | Ref : tm -> tm | Deref : tm -> tm | Assign : tm -> tm -> tm | Loc : nat -> tm.

Definition ctx := list ty.
Definition store_ty := list ty.

Inductive has_type : ctx -> store_ty -> tm -> ty -> Prop :=
  | T_Var : forall G S x T, nth_error G x = Some T -> has_type G S (Var x) T
  | T_Num : forall G S n, has_type G S (Num n) TyNat
  | T_Bool : forall G S b, has_type G S (BOOL b) TyBool
  | T_Succ : forall G S t, has_type G S t TyNat -> has_type G S (Succ t) TyNat
  | T_Pred : forall G S t, has_type G S t TyNat -> has_type G S (Pred t) TyNat
  | T_IsZero : forall G S t, has_type G S t TyNat -> has_type G S (IsZero t) TyBool
  | T_If : forall G S t1 t2 t3 T, has_type G S t1 TyBool -> has_type G S t2 T -> has_type G S t3 T -> has_type G S (If t1 t2 t3) T
  | T_Lam : forall G S T1 T2 t, has_type (T1 :: G) S t T2 -> has_type G S (Lam T1 t) (TyArrow T1 T2)
  | T_App : forall G S t1 t2 T1 T2, has_type G S t1 (TyArrow T1 T2) -> has_type G S t2 T1 -> has_type G S (App t1 t2) T2
  | T_Fix : forall G S t T, has_type (T :: G) S t T -> has_type G S (Fix t) T
  | T_Ref : forall G S t T, has_type G S t T -> has_type G S (Ref t) (TyRef T)
  | T_Deref : forall G S t T, has_type G S t (TyRef T) -> has_type G S (Deref t) T
  | T_Assign : forall G S t1 t2 T, has_type G S t1 (TyRef T) -> has_type G S t2 T -> has_type G S (Assign t1 t2) TyNat
  | T_Loc : forall G S l T, nth_error S l = Some T -> has_type G S (Loc l) (TyRef T).

Inductive value : tm -> Prop :=
  | V_Num : forall n, value (Num n)
  | V_Bool : forall b, value (BOOL b)
  | V_Lam : forall T t, value (Lam T t)
  | V_Loc : forall l, value (Loc l).

Fixpoint shift_at (d : nat) (t : tm) : tm :=
  match t with
  | Var x => if x <? d then Var x else Var (x + 1)
  | Num n => Num n | BOOL b => BOOL b
  | Succ t1 => Succ (shift_at d t1) | Pred t1 => Pred (shift_at d t1)
  | IsZero t1 => IsZero (shift_at d t1)
  | If t1 t2 t3 => If (shift_at d t1) (shift_at d t2) (shift_at d t3)
  | Lam T t1 => Lam T (shift_at (S d) t1)
  | App t1 t2 => App (shift_at d t1) (shift_at d t2)
  | Fix t1 => Fix (shift_at (S d) t1)
  | Ref t1 => Ref (shift_at d t1) | Deref t1 => Deref (shift_at d t1)
  | Assign t1 t2 => Assign (shift_at d t1) (shift_at d t2)
  | Loc l => Loc l
  end.

Definition shift (t : tm) : tm := shift_at 0 t.

Fixpoint subst (j : nat) (s t : tm) : tm :=
  match t with
  | Var x => if Nat.eqb x j then s else Var x
  | Num n => Num n | BOOL b => BOOL b
  | Succ t1 => Succ (subst j s t1) | Pred t1 => Pred (subst j s t1)
  | IsZero t1 => IsZero (subst j s t1)
  | If t1 t2 t3 => If (subst j s t1) (subst j s t2) (subst j s t3)
  | Lam T t1 => Lam T (subst (S j) (shift s) t1)
  | App t1 t2 => App (subst j s t1) (subst j s t2)
  | Fix t1 => Fix (subst (S j) (shift s) t1)
  | Ref t1 => Ref (subst j s t1) | Deref t1 => Deref (subst j s t1)
  | Assign t1 t2 => Assign (subst j s t1) (subst j s t2)
  | Loc l => Loc l
  end.

Definition heap := list (nat * tm).

Fixpoint heap_lookup (l : nat) (mu : heap) : option tm :=
  match mu with
  | [] => None
  | (l', v) :: mu' => if Nat.eqb l l' then Some v else heap_lookup l mu'
  end.

Fixpoint heap_update (l : nat) (v : tm) (mu : heap) : heap :=
  match mu with
  | [] => []
  | (l', v') :: mu' => if Nat.eqb l l' then (l, v) :: mu'
                        else (l', v') :: heap_update l v mu'
  end.

Inductive heap_ok : heap -> store_ty -> Prop :=
  | heap_empty : forall S, heap_ok [] S
  | heap_cons : forall l v mu S T, heap_ok mu S -> has_type [] S v T -> nth_error S l = Some T -> heap_ok ((l, v) :: mu) S.

Inductive step : tm -> heap -> tm -> heap -> Prop :=
  | S_Succ : forall t mu t' mu', step t mu t' mu' -> step (Succ t) mu (Succ t') mu'
  | S_PredZero : forall mu, step (Pred (Num 0)) mu (Num 0) mu
  | S_PredSucc : forall n mu, step (Pred (Num (S n))) mu (Num n) mu
  | S_Pred : forall t mu t' mu', step t mu t' mu' -> step (Pred t) mu (Pred t') mu'
  | S_IsZeroZero : forall mu, step (IsZero (Num 0)) mu (BOOL true) mu
  | S_IsZeroSucc : forall n mu, step (IsZero (Num (S n))) mu (BOOL false) mu
  | S_IsZero : forall t mu t' mu', step t mu t' mu' -> step (IsZero t) mu (IsZero t') mu'
  | S_IfTrue : forall t1 t2 mu, step (If (BOOL true) t1 t2) mu t1 mu
  | S_IfFalse : forall t1 t2 mu, step (If (BOOL false) t1 t2) mu t2 mu
  | S_If : forall t1 mu t1' mu' t2 t3, step t1 mu t1' mu' -> step (If t1 t2 t3) mu (If t1' t2 t3) mu'
  | S_App1 : forall t1 mu t1' mu' t2, step t1 mu t1' mu' -> step (App t1 t2) mu (App t1' t2) mu'
  | S_App2 : forall v1 t2 mu t2' mu', value v1 -> step t2 mu t2' mu' -> step (App v1 t2) mu (App v1 t2') mu'
  | S_AppAbs : forall T t1 v2 mu, value v2 -> step (App (Lam T t1) v2) mu (subst 0 v2 t1) mu
  | S_Fix : forall t mu, step (Fix t) mu (subst 0 (Fix t) t) mu
  | S_Ref : forall t mu t' mu', step t mu t' mu' -> step (Ref t) mu (Ref t') mu'
  | S_RefV : forall v mu, value v -> step (Ref v) mu (Loc (length mu)) ((length mu, v) :: mu)
  | S_Deref : forall t mu t' mu', step t mu t' mu' -> step (Deref t) mu (Deref t') mu'
  | S_DerefLoc : forall l mu v, heap_lookup l mu = Some v -> step (Deref (Loc l)) mu v mu
  | S_Assign1 : forall t1 mu t1' mu' t2, step t1 mu t1' mu' -> step (Assign t1 t2) mu (Assign t1' t2) mu'
  | S_Assign2 : forall l t2 mu t2' mu', step t2 mu t2' mu' -> step (Assign (Loc l) t2) mu (Assign (Loc l) t2') mu'
  | S_AssignV : forall l v mu, value v -> step (Assign (Loc l) v) mu (Num 0) (heap_update l v mu).

Definition extends (S' S : store_ty) : Prop := exists S2, S' = S ++ S2.

(** ** Auxiliary Lemmas *)

Lemma extends_refl : forall S, extends S S.
Proof. intro S. exists []. rewrite app_nil_r. reflexivity. Qed.

Lemma extends_trans : forall S1 S2 S3,
  extends S2 S1 -> extends S3 S2 -> extends S3 S1.
Proof.
  intros S1 S2 S3 [S12 H12] [S23 H23].
  exists (S12 ++ S23). subst. rewrite app_assoc. reflexivity.
Qed.

Lemma extends_app : forall S T, extends (S ++ T) S.
Proof. intros S T. exists T. reflexivity. Qed.

Lemma nth_error_extends : forall S S' l T,
  extends S' S -> nth_error S l = Some T -> nth_error S' l = Some T.
Proof.
  intros S S' l T [S2 H] Hlook; subst;
  rewrite nth_error_app1; [exact Hlook | eapply nth_error_Some; rewrite Hlook; discriminate].
Qed.

Lemma has_type_store_weaken : forall G S S' t T,
  has_type G S t T -> extends S' S -> has_type G S' t T.
Proof.
  intros G S S' t T Ht Hext.
  induction Ht; try (econstructor; eauto; fail).
  - constructor. eapply nth_error_extends; eauto.
Qed.

Lemma nth_error_app_Some : forall (A : Type) (l1 l2 : list A) n x,
  nth_error l1 n = Some x -> nth_error (l1 ++ l2) n = Some x.
Proof.
  intros A l1. induction l1; intros l2 n x H.
  - destruct n; simpl in H; discriminate.
  - destruct n; simpl in *; auto.
Qed.

Lemma nth_error_app1_Some : forall (A : Type) (l1 l2 : list A) n x,
  nth_error l1 n = Some x -> nth_error (l1 ++ l2) n = Some x.
Proof.
  intros. apply nth_error_app_Some; auto.
Qed.

Lemma shift_at_type : forall G1 G2 S t T U,
  has_type (G1 ++ G2) S t T ->
  has_type (G1 ++ U :: G2) S (shift_at (length G1) t) T.
Proof.
  intros G1 G2 S t T U Ht;
  remember (G1 ++ G2) as G eqn:HG;
  generalize dependent G2; generalize dependent G1;
  induction Ht; intros G1 G2 HG; subst; simpl.
  - destruct (Nat.ltb_spec x (length G1)).
    + apply T_Var; rewrite nth_error_app1 in H |- *; auto;
      apply nth_error_Some; rewrite H; discriminate.
    + apply T_Var; rewrite nth_error_app2 in H; [| lia];
      rewrite nth_error_app2; [| lia];
      replace (x + 1 - length G1) with (1 + (x - length G1)) by lia;
      simpl; exact H.
  - constructor.
  - constructor.
  - constructor; apply IHHt; reflexivity.
  - constructor; apply IHHt; reflexivity.
  - constructor; apply IHHt; reflexivity.
  - apply T_If; [apply IHHt1 | apply IHHt2 | apply IHHt3]; reflexivity.
  - apply T_Lam; apply (IHHt (T1 :: G1) G2); simpl; reflexivity.
  - econstructor; [apply IHHt1 | apply IHHt2]; reflexivity.
  - apply T_Fix; apply (IHHt (T :: G1) G2); simpl; reflexivity.
  - constructor; apply IHHt; reflexivity.
  - constructor; apply IHHt; reflexivity.
  - econstructor; [apply IHHt1 | apply IHHt2]; reflexivity.
  - apply T_Loc; auto.
Qed.

Lemma shift_type : forall G S t T U,
  has_type G S t T -> has_type (U :: G) S (shift t) T.
Proof.
  intros G S t T U Ht.
  unfold shift.
  apply (shift_at_type [] G S t T U). simpl. exact Ht.
Qed.

(** Substitution at depth |G1|: substitute U-typed term into context G1++[U] *)
Lemma subst_type_aux : forall G1 S s t T U,
  has_type (G1 ++ [U]) S t T ->
  has_type G1 S s U ->
  has_type G1 S (subst (length G1) s t) T.
Proof.
  intros G1 S s t; revert G1 S s; induction t;
    intros G1 S s T U Ht Hs; inversion Ht; subst; simpl.
  - (* Var *)
    destruct (Nat.eqb_spec n (length G1)) as [Heq | Hne].
    + subst. rewrite nth_error_app2 in H2; [| lia].
      rewrite Nat.sub_diag in H2. simpl in H2. injection H2. intro. subst. exact Hs.
    + apply T_Var.
      destruct (lt_dec n (length G1)) as [Hlt | Hge].
      * rewrite nth_error_app1 in H2; [exact H2 | lia].
      * rewrite nth_error_app2 in H2; [| lia].
        assert (n - length G1 >= 1) by lia.
        destruct (n - length G1) as [| m]; [lia |].
        simpl in H2. destruct m; simpl in H2; discriminate.
  - constructor.
  - constructor.
  - constructor; eapply IHt; eauto.
  - constructor; eapply IHt; eauto.
  - constructor; eapply IHt; eauto.
  - apply T_If; [eapply IHt1 | eapply IHt2 | eapply IHt3]; eauto.
  - apply T_Lam.
    apply (IHt (t :: G1) S (shift s) T2 U); auto.
    apply shift_type; exact Hs.
  - econstructor; [eapply IHt1 | eapply IHt2]; eauto.
  - apply T_Fix.
    apply (IHt (T :: G1) S (shift s) T U); auto.
    apply shift_type; exact Hs.
  - constructor; eapply IHt; eauto.
  - constructor; eapply IHt; eauto.
  - econstructor; [eapply IHt1 | eapply IHt2]; eauto.
  - apply T_Loc; auto.
Qed.

Lemma subst_type_0 : forall S s t T U,
  has_type [U] S t T ->
  has_type [] S s U ->
  has_type [] S (subst 0 s t) T.
Proof.
  intros S s t T U Ht Hs.
  apply (subst_type_aux [] S s t T U); [simpl; exact Ht | exact Hs].
Qed.

(** Heap invariant lemmas *)

Lemma heap_ok_update : forall mu S l v T,
  heap_ok mu S ->
  has_type [] S v T ->
  nth_error S l = Some T ->
  heap_ok (heap_update l v mu) S.
Proof.
  intros mu S l v T Hok Hv Hlook.
  induction Hok; simpl; [constructor |].
  destruct (Nat.eqb_spec l l0); subst; econstructor; eauto.
Qed.

Lemma heap_lookup_typed : forall mu S l T v,
  heap_ok mu S ->
  nth_error S l = Some T ->
  heap_lookup l mu = Some v ->
  has_type [] S v T.
Proof.
  intros mu S l T v Hok.
  induction Hok; intros Hlook Hlookup.
  - simpl in Hlookup. discriminate.
  - simpl in Hlookup.
    destruct (Nat.eqb_spec l l0).
    + subst. injection Hlookup. intro. subst.
      rewrite Hlook in H0. injection H0. intro. subst. exact H.
    + apply IHHok; auto.
Qed.

Lemma heap_update_length : forall mu l v,
  length (heap_update l v mu) = length mu.
Proof.
  intros mu l v.
  induction mu as [| [l' v'] mu' IH]; simpl; auto.
  destruct (Nat.eqb l l'); simpl; auto.
Qed.

(** heap_ok_cons: adding a new entry for location (length mu) to the heap *)
Lemma heap_ok_cons_new : forall mu S v T,
  heap_ok mu S ->
  has_type [] (S ++ [T]) v T ->
  length mu = length S ->
  heap_ok ((length mu, v) :: mu) (S ++ [T]).
Proof.
  intros mu S v T Hok Hv Hlen.
  apply heap_cons with (T := T); [| exact Hv |].
  - (* heap_ok mu (S ++ [T]) *)
    clear Hv Hlen.
    induction Hok; [constructor |].
    eapply heap_cons; [apply IHHok |
      eapply has_type_store_weaken; [exact H | apply extends_app] |
      apply nth_error_app_Some; exact H0].
  - (* nth_error (S ++ [T]) (length mu) = Some T *)
    rewrite Hlen.
    rewrite nth_error_app2; [| lia].
    rewrite Nat.sub_diag. simpl. reflexivity.
Qed.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Theorem preservation :
  forall t mu t' mu' T S,
    has_type [] S t T ->
    step t mu t' mu' ->
    heap_ok mu S ->
    length mu >= length S ->
    exists S',
      extends S' S /\
      heap_ok mu' S' /\
      has_type [] S' t' T.
Proof.
  intros t mu t' mu' Ty S Ht Hstep.
  revert Ty S Ht.
  induction Hstep; intros Ty S Ht Hok Hlen; inversion Ht; subst.
  (* S_Succ *)
  - destruct (IHHstep TyNat S H2 Hok Hlen) as [S' [Hext [Hok' Ht']]].
    exists S'; split; [exact Hext | split; [exact Hok' | constructor; exact Ht']].
  (* S_PredZero *)
  - exists S; split; [apply extends_refl | split; [exact Hok | constructor]].
  (* S_PredSucc *)
  - exists S; split; [apply extends_refl | split; [exact Hok | constructor]].
  (* S_Pred *)
  - destruct (IHHstep TyNat S H2 Hok Hlen) as [S' [Hext [Hok' Ht']]].
    exists S'; split; [exact Hext | split; [exact Hok' | constructor; exact Ht']].
  (* S_IsZeroZero *)
  - exists S; split; [apply extends_refl | split; [exact Hok | constructor]].
  (* S_IsZeroSucc *)
  - exists S; split; [apply extends_refl | split; [exact Hok | constructor]].
  (* S_IsZero *)
  - destruct (IHHstep TyNat S H2 Hok Hlen) as [S' [Hext [Hok' Ht']]].
    exists S'; split; [exact Hext | split; [exact Hok' | constructor; exact Ht']].
  (* S_IfTrue *)
  - exists S; split; [apply extends_refl | split; [exact Hok | exact H6]].
  (* S_IfFalse *)
  - exists S; split; [apply extends_refl | split; [exact Hok | exact H7]].
  (* S_If *)
  - destruct (IHHstep TyBool S H4 Hok Hlen) as [S' [Hext [Hok' Ht']]].
    exists S'; split; [exact Hext | split; [exact Hok' |
      apply T_If; [exact Ht' | eapply has_type_store_weaken; eauto |
                   eapply has_type_store_weaken; eauto]]].
  (* S_App1 *)
  - destruct (IHHstep (TyArrow T1 Ty) S H3 Hok Hlen) as [S' [Hext [Hok' Ht']]].
    exists S'; split; [exact Hext | split; [exact Hok' |
      econstructor; [exact Ht' | eapply has_type_store_weaken; eauto]]].
  (* S_App2 *)
  - destruct (IHHstep T1 S H6 Hok Hlen) as [S' [Hext [Hok' Ht']]].
    exists S'; split; [exact Hext | split; [exact Hok' |
      econstructor; [eapply has_type_store_weaken; eauto | exact Ht']]].
  (* S_AppAbs *)
  - inversion H4; subst.
    exists S; split; [apply extends_refl | split; [exact Hok |]].
    apply subst_type_0 with (U := T1); auto.
  (* S_Fix *)
  - exists S; split; [apply extends_refl | split; [exact Hok |]].
    apply subst_type_0 with (U := Ty); [exact H2 | constructor; exact H2].
  (* S_Ref *)
  - destruct (IHHstep T S H2 Hok Hlen) as [S' [Hext [Hok' Ht']]].
    exists S'; split; [exact Hext | split; [exact Hok' | constructor; exact Ht']].
  (* S_RefV *)
  - (* New location: length mu, new store type S' = S ++ repeat T (length mu - length S + 1) *)
    exists (S ++ repeat T (length mu - length S + 1)).
    split; [apply extends_app |].
    split.
    + (* heap_ok ((length mu, v) :: mu) (S ++ repeat T ...) *)
      apply heap_cons with (T := T).
      * (* heap_ok mu (S ++ repeat T ...) -- needs to be proved for inner mu *)
        (* Use a separate assert/cut to avoid IH issues *)
        assert (Haux : forall mu' S',
          heap_ok mu' S' ->
          heap_ok mu' (S' ++ repeat T (length mu - length S + 1))).
        { intros mu' S' Hok'.
          induction Hok'; [constructor |].
          eapply heap_cons; [apply IHHok' |
            eapply has_type_store_weaken; [exact H0 | apply extends_app] |
            apply nth_error_app_Some; exact H1].
        }
        apply Haux. exact Hok.
      * (* has_type [] (S ++ repeat T ...) v T *)
        eapply has_type_store_weaken; [exact H3 | apply extends_app].
      * (* nth_error (S ++ repeat T ...) (length mu) = Some T *)
        rewrite nth_error_app2; [| lia].
        apply nth_error_repeat. lia.
    + (* has_type [] (S ++ repeat T ...) (Loc (length mu)) (TyRef T) *)
      apply T_Loc.
      rewrite nth_error_app2; [| lia].
      apply nth_error_repeat. lia.
  (* S_Deref *)
  - destruct (IHHstep (TyRef Ty) S H2 Hok Hlen) as [S' [Hext [Hok' Ht']]].
    exists S'; split; [exact Hext | split; [exact Hok' | constructor; exact Ht']].
  (* S_DerefLoc *)
  - inversion H3; subst.
    exists S; split; [apply extends_refl | split; [exact Hok |]].
    eapply heap_lookup_typed; eauto.
  (* S_Assign1 *)
  - destruct (IHHstep (TyRef T) S H3 Hok Hlen) as [S' [Hext [Hok' Ht']]].
    exists S'; split; [exact Hext | split; [exact Hok' |
      econstructor; [exact Ht' | eapply has_type_store_weaken; eauto]]].
  (* S_Assign2 *)
  - destruct (IHHstep T S H5 Hok Hlen) as [S' [Hext [Hok' Ht']]].
    exists S'; split; [exact Hext | split; [exact Hok' |
      econstructor; [eapply has_type_store_weaken; eauto | exact Ht']]].
  (* S_AssignV *)
  - inversion H4; subst.
    exists S; split; [apply extends_refl | split; [| constructor]].
    eapply heap_ok_update; eauto.
Qed.

Theorem preservation_neg : ~ (
  forall t mu t' mu' T S,
    has_type [] S t T ->
    step t mu t' mu' ->
    heap_ok mu S ->
    length mu >= length S ->
    exists S',
      extends S' S /\
      heap_ok mu' S' /\
      has_type [] S' t' T).
Proof.
Admitted.
