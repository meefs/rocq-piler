(** * Snakelet WP Benchmark — Iris Separation Logic for Axiomander *)

From stdpp Require Export strings gmap.
From stdpp Require Import countable decidable.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import lifting.
From iris.program_logic Require Export language.
From iris.base_logic.lib Require Export gen_heap.
From iris.algebra Require Import dfrac.
From stdpp Require Import fin_maps fin_map_dom.
Open Scope Z_scope.

From Stdlib Require Import BinInt Uint63Axioms Floats.PrimFloat.

(* ========================================================================= *)
(*  SnakeletLang — definitions and infrastructure (all Qed)                  *)
(* ========================================================================= *)

(** * Locations *)
Inductive loc := Loc (l : positive).

#[global] Instance loc_eq_dec : EqDecision loc.
Proof. solve_decision. Qed.

#[global] Instance loc_countable : Countable loc.
Proof.
  apply (inj_countable' (λ '(Loc l), l) Loc); abstract (by intros []).
Qed.

#[global] Program Instance loc_infinite : Infinite loc :=
  inj_infinite (λ p, Loc p) (λ l, match l with Loc p => Some p end) _.
Next Obligation. done. Qed.

(** * Values *)
Inductive sn_val :=
  | LitInt (n : Z)
  | LitBool (b : bool)
  | LitFloat (f : float)
  | LitString (s : string)
  | LitTuple (vs : list sn_val)
  | LitList (vs : list sn_val)
  | LitDict (kvs : list (sn_val * sn_val))
  | LitSet (vs : list sn_val)
  | LitLoc (l : loc)
  | LitUnit.

Definition LitV (v : sn_val) : sn_val := v.

(** * Expressions *)
Inductive binop := AddOp | SubOp | MulOp | DivOp | EqOp | LeOp | LtOp | GtOp | GeOp
                 | LenOp | InOp | UnionOp | InterOp.

Inductive sn_expr :=
  | Val (v : sn_val)
  | Var (x : string)
  | Let (x : string) (e1 e2 : sn_expr)
  | BinOp (op : binop) (e1 e2 : sn_expr)
  | Load (e : sn_expr)
  | Store (e1 e2 : sn_expr)
  | Alloc (e : sn_expr)
  | If (e0 e1 e2 : sn_expr)
  | FAA (e1 e2 : sn_expr)
  | Fork (e : sn_expr)
  | DictGet (l key : sn_expr)
  | DictSet (l key sn_val : sn_expr)
  | Raise (e : sn_expr)
  | Try (body handler : sn_expr)
  | Call (f : string) (args : list sn_expr).

(** * Evaluation contexts *)
Inductive sn_ectx_item :=
  | LetCtx (x : string) (e2 : sn_expr)
  | BinOpLCtx (op : binop) (v2 : sn_val)
  | BinOpRCtx (op : binop) (v1 : sn_val)
  | IfCtx (e1 e2 : sn_expr)
  | LoadCtx
  | StoreLCtx (v2 : sn_val)
  | StoreRCtx (e1 : sn_expr)
  | AllocCtx
  | FaaLCtx (v2 : sn_val)
  | FaaRCtx (v1 : sn_val).

Definition fill_item (Ki : sn_ectx_item) (x : sn_expr) : sn_expr :=
  match Ki with
  | LetCtx x0 e2 => Let x0 x e2
  | BinOpLCtx op v2 => BinOp op x (Val v2)
  | BinOpRCtx op v1 => BinOp op (Val v1) x
  | IfCtx e1 e2 => If x e1 e2
  | LoadCtx => Load x
  | StoreLCtx v2 => Store x (Val v2)
  | StoreRCtx e1 => Store e1 x
  | AllocCtx => Alloc x
  | FaaLCtx v2 => FAA x (Val v2)
  | FaaRCtx v1 => FAA (Val v1) x
  end.

Definition fill_K (K : list sn_ectx_item) (x : sn_expr) : sn_expr :=
  foldr fill_item x K.

(** * Values and evaluation *)
Definition of_val (v : sn_val) : sn_expr := Val v.
Definition to_val (e : sn_expr) : option sn_val :=
  match e with Val v => Some v | _ => None end.
Definition sn_state : Type := gmap loc sn_val.

Lemma fill_not_val K (x : sn_expr) : to_val x = None → to_val (fill_K K x) = None.
Proof.
  induction K as [|Ki K IH]; simpl; [auto|].
  intros H. destruct Ki; simpl; reflexivity.
Qed.

Lemma fill_K_val K (x : sn_expr) (v : sn_val) : fill_K K x = Val v ↔ K = [] ∧ x = Val v.
Proof.
  split.
  - intros H. induction K as [|Ki K IH]; simpl in H.
    + split; auto.
    + destruct Ki; simpl in H; discriminate H.
  - intros [-> ->]; reflexivity.
Qed.

Lemma fill_item_inj Ki (a b : sn_expr) : fill_item Ki a = fill_item Ki b → a = b.
Proof. destruct Ki; simpl; injection 1; auto. Qed.

(** * Substitution *)
Fixpoint subst (x : string) (v : sn_val) (e : sn_expr) : sn_expr :=
  match e with
  | Val _ => e
  | Var y => if String.eqb x y then Val v else e
  | Let y e1 e2 =>
      Let y (subst x v e1) (if String.eqb x y then e2 else subst x v e2)
  | BinOp op e1 e2 => BinOp op (subst x v e1) (subst x v e2)
  | Load e => Load (subst x v e)
  | Store e1 e2 => Store (subst x v e1) (subst x v e2)
  | Alloc e => Alloc (subst x v e)
  | If e0 e1 e2 => If (subst x v e0) (subst x v e1) (subst x v e2)
  | FAA e1 e2 => FAA (subst x v e1) (subst x v e2)
  | Fork e => Fork (subst x v e)
  | DictGet l key => DictGet (subst x v l) (subst x v key)
  | DictSet l key v' => DictSet (subst x v l) (subst x v key) (subst x v v')
  | Raise e => Raise (subst x v e)
  | Try body handler => Try (subst x v body) (subst x v handler)
  | Call f args => Call f (List.map (subst x v) args)
  end.

(** * Pure steps *)
Definition z_to_float (n : Z) : float :=
  PrimFloat.of_uint63 (of_Z n).

Fixpoint val_list_len (vs : list sn_val) : Z :=
  match vs with
  | [] => 0
  | _ :: vs' => 1 + val_list_len vs'
  end%Z.

Fixpoint val_eqb (fuel : nat) (v1 v2 : sn_val) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match v1, v2 with
      | LitInt n1, LitInt n2 => bool_decide (n1 = n2)
      | LitBool b1, LitBool b2 => Bool.eqb b1 b2
      | LitFloat f1, LitFloat f2 => PrimFloat.eqb f1 f2
      | LitString s1, LitString s2 => String.eqb s1 s2
      | LitTuple vs1, LitTuple vs2 => val_list_eqb fuel' vs1 vs2
      | LitList vs1, LitList vs2 => val_list_eqb fuel' vs1 vs2
      | LitSet vs1, LitSet vs2 => val_list_eqb fuel' vs1 vs2
      | LitDict kvs1, LitDict kvs2 => val_kvlist_eqb fuel' kvs1 kvs2
      | LitLoc l1, LitLoc l2 =>
          match l1, l2 with Loc p1, Loc p2 => Pos.eqb p1 p2 end
      | LitUnit, LitUnit => true
      | _, _ => false
      end
  end
with val_list_eqb (fuel : nat) (vs1 vs2 : list sn_val) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match vs1, vs2 with
      | [], [] => true
      | v1 :: vs1', v2 :: vs2' => val_eqb fuel' v1 v2 && val_list_eqb fuel' vs1' vs2'
      | _, _ => false
      end
  end
with val_kvlist_eqb (fuel : nat) (kvs1 kvs2 : list (sn_val * sn_val)) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match kvs1, kvs2 with
      | [], [] => true
      | (k1,v1) :: kvs1', (k2,v2) :: kvs2' =>
          val_eqb fuel' k1 k2 && val_eqb fuel' v1 v2 && val_kvlist_eqb fuel' kvs1' kvs2'
      | _, _ => false
      end
  end.

Definition val_eq (v1 v2 : sn_val) : bool := val_eqb 50 v1 v2.

Fixpoint val_list_mem (fuel : nat) (x : sn_val) (vs : list sn_val) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match vs with
      | [] => false
      | v :: vs' => val_eqb fuel' x v || val_list_mem fuel' x vs'
      end
  end.

Definition binop_eval (op : binop) (v1 v2 : sn_val) : sn_val :=
  match v1, v2 with
  | LitInt n1, LitInt n2 =>
      match op with
      | AddOp => LitInt (n1 + n2)
      | SubOp => LitInt (n1 - n2)
      | MulOp => LitInt (n1 * n2)
      | DivOp => LitFloat (PrimFloat.div (z_to_float n1) (z_to_float n2))
      | EqOp  => LitBool (bool_decide (n1 = n2))
      | LeOp  => LitBool (bool_decide (n1 <= n2))
      | LtOp  => LitBool (bool_decide (n1 < n2))
      | GtOp  => LitBool (bool_decide (n1 > n2))
      | GeOp  => LitBool (bool_decide (n1 >= n2))
      | _ => LitUnit
      end
  | LitFloat f1, LitFloat f2 =>
      match op with
      | AddOp => LitFloat (PrimFloat.add f1 f2)
      | SubOp => LitFloat (PrimFloat.sub f1 f2)
      | MulOp => LitFloat (PrimFloat.mul f1 f2)
      | DivOp => LitFloat (PrimFloat.div f1 f2)
      | EqOp  => LitBool (PrimFloat.eqb f1 f2)
      | LeOp  => LitBool (PrimFloat.leb f1 f2)
      | LtOp  => LitBool (PrimFloat.ltb f1 f2)
      | GtOp  => LitBool (negb (PrimFloat.leb f1 f2))
      | GeOp  => LitBool (negb (PrimFloat.ltb f1 f2))
      | _ => LitUnit
      end
  | LitInt n, LitFloat f =>
      match op with
      | AddOp => LitFloat (PrimFloat.add (z_to_float n) f)
      | SubOp => LitFloat (PrimFloat.sub (z_to_float n) f)
      | MulOp => LitFloat (PrimFloat.mul (z_to_float n) f)
      | DivOp => LitFloat (PrimFloat.div (z_to_float n) f)
      | _ => LitUnit
      end
  | LitFloat f, LitInt n =>
      match op with
      | AddOp => LitFloat (PrimFloat.add f (z_to_float n))
      | SubOp => LitFloat (PrimFloat.sub f (z_to_float n))
      | MulOp => LitFloat (PrimFloat.mul f (z_to_float n))
      | DivOp => LitFloat (PrimFloat.div f (z_to_float n))
      | _ => LitUnit
      end
  | LitString s1, LitString s2 =>
      match op with
      | AddOp => LitString (s1 ++ s2)
      | EqOp  => LitBool (String.eqb s1 s2)
      | LenOp => LitInt (Z.of_nat (String.length s1))
      | _ => LitUnit
      end
  | LitString s, _ =>
      match op with
      | LenOp => LitInt (Z.of_nat (String.length s))
      | _ => LitUnit
       end
  | LitBool b1, LitInt n =>
      match op with
      | AddOp => LitInt ((if b1 then 1 else 0)%Z + n)
      | SubOp => LitInt ((if b1 then 1 else 0)%Z - n)
      | MulOp => LitInt ((if b1 then 1 else 0)%Z * n)
      | _ => LitUnit
      end
  | LitInt n, LitBool b =>
      match op with
      | AddOp => LitInt (n + (if b then 1 else 0)%Z)
      | SubOp => LitInt (n - (if b then 1 else 0)%Z)
      | MulOp => LitInt (n * (if b then 1 else 0)%Z)
      | _ => LitUnit
      end
  | LitTuple vs1, LitTuple vs2 =>
      match op with
      | AddOp => LitTuple (vs1 ++ vs2)
      | EqOp  => LitBool (val_eq (LitTuple vs1) (LitTuple vs2))
      | LenOp => LitInt (val_list_len vs1)
      | InOp  => LitBool (val_list_mem 50 v2 vs1)
      | _ => LitUnit
      end
  | LitTuple vs, _ =>
      match op with
      | LenOp => LitInt (val_list_len vs)
      | InOp  => LitBool (val_list_mem 50 v2 vs)
      | _ => LitUnit
      end
  | LitList vs1, LitList vs2 =>
      match op with
      | AddOp => LitList (vs1 ++ vs2)
      | EqOp  => LitBool (val_eq (LitList vs1) (LitList vs2))
      | LenOp => LitInt (val_list_len vs1)
      | InOp  => LitBool (val_list_mem 50 v2 vs1)
      | _ => LitUnit
      end
  | LitList vs, _ =>
      match op with
      | LenOp => LitInt (val_list_len vs)
      | InOp  => LitBool (val_list_mem 50 v2 vs)
      | _ => LitUnit
      end
  | LitSet vs1, LitSet vs2 =>
      match op with
      | EqOp  => LitBool (val_eq (LitSet vs1) (LitSet vs2))
      | LenOp => LitInt (val_list_len vs1)
      | InOp  => LitBool (val_list_mem 50 v2 vs1)
      | UnionOp => LitSet vs1
      | InterOp => LitSet vs1
      | _ => LitUnit
      end
  | LitSet vs, _ =>
      match op with
      | LenOp => LitInt (val_list_len vs)
      | InOp  => LitBool (val_list_mem 50 v2 vs)
      | _ => LitUnit
      end
  | LitDict kvs, _ =>
      match op with
      | LenOp => LitInt (val_list_len (List.map fst kvs))
      | _ => LitUnit
       end
  | _, _ => LitUnit
  end.

Inductive pure_step : sn_expr → sn_expr → Prop :=
  | PureLet v x e2 : pure_step (Let x (Val v) e2) (subst x v e2)
  | PureBinOp op v1 v2 :
      pure_step (BinOp op (Val v1) (Val v2)) (Val (binop_eval op v1 v2))
  | PureIfTrue e1 e2 : pure_step (If (Val (LitBool true)) e1 e2) e1
  | PureIfFalse e1 e2 : pure_step (If (Val (LitBool false)) e1 e2) e2
  | PureTryReturn v handler : pure_step (Try (Val v) handler) (Val v).

Definition lit_as_z (v : sn_val) : Z :=
  match v with LitInt n => n | _ => 0 end.

(** * Function context *)
Inductive fun_entry :=
  | FunSpec (spec : list sn_val → sn_val → Prop)
  | FunDef (params : list string) (body : sn_expr).

Class FunCtx := { fun_entries : string → option fun_entry }.

#[export] Instance default_fun_ctx : FunCtx | 100 := {| fun_entries := λ _, None |}.

Fixpoint subst_list (params : list string) (vs : list sn_val) (e : sn_expr) : sn_expr :=
  match params, vs with
  | x :: params', v :: vs' => subst_list params' vs' (subst x v e)
  | _, _ => e
  end.

Lemma map_Val_inj (vs1 vs2 : list sn_val) :
  map Val vs1 = map Val vs2 → vs1 = vs2.
Proof.
  revert vs2. induction vs1 as [|v1 vs1 IH]; intros [|v2 vs2] H;
    simpl in H; try discriminate.
  - reflexivity.
  - injection H as Hv Hvs. f_equal; [exact Hv | apply IH, Hvs].
Qed.

Section with_fun_ctx.
Context `{FC : FunCtx}.

Inductive head_step : sn_expr → sn_state → sn_expr → sn_state → list sn_expr → Prop :=
  | HeadLoad l v σ :
      σ !! l = Some v →
      head_step (Load (Val (LitLoc l))) σ (Val v) σ []
  | HeadStore l v σ :
      is_Some (σ !! l) →
      head_step (Store (Val (LitLoc l)) (Val v)) σ
                (Val LitUnit) (<[l:=v]> σ) []
  | HeadAlloc v σ l :
      σ !! l = None →
      head_step (Alloc (Val v)) σ (Val (LitLoc l))
                (<[l:=v]> σ) []
  | HeadFAA l v z σ :
      σ !! l = Some (LitInt z) →
      head_step (FAA (Val (LitLoc l)) (Val v)) σ
                (Val (LitInt z)) (<[l:=LitInt (z + lit_as_z v)]> σ) []
  | HeadFork e σ :
      head_step (Fork e) σ (Val LitUnit) σ [e]
  | HeadRaise v σ :
      head_step (Raise (Val v)) σ (Val v) σ []
  | HeadTryBody body handler σ body' σ' efs :
      head_step body σ body' σ' efs →
      head_step (Try body handler) σ body' σ' efs
  | HeadCallSpec f vs σ spec v :
      fun_entries f = Some (FunSpec spec) →
      spec vs v →
      head_step (Call f (map Val vs)) σ (Val v) σ []
  | HeadCallUnfold f vs σ params body :
      fun_entries f = Some (FunDef params body) →
      length vs = length params →
      head_step (Call f (map Val vs)) σ (subst_list params vs body) σ [].

Definition observation : Type := unit.

Inductive prim_step : sn_expr → sn_state → list observation → sn_expr → sn_state → list sn_expr → Prop :=
  | PrimPureStep K x σ x' :
      pure_step x x' →
      prim_step (fill_K K x) σ [] (fill_K K x') σ []
  | PrimHeadStep K x σ x' σ' efs :
      head_step x σ x' σ' efs →
      prim_step (fill_K K x) σ [] (fill_K K x') σ' efs.

Lemma snakelet_lang_mixin : LanguageMixin of_val to_val prim_step.
Proof.
  split.
  - intros v. unfold of_val, to_val. reflexivity.
  - intros e v Hto. unfold to_val in Hto. destruct e; try discriminate.
    injection Hto as ->. unfold of_val. reflexivity.
  - intros ex σ κ ex' σ' efs Hprim.
    inversion Hprim as [K x0 σ0 x0' Hpure | K x0 σ0 x0' σ0' efs0 Hhead]; subst.
    + apply (fill_not_val K x0). inversion Hpure; subst; simpl; auto.
    + apply (fill_not_val K x0). destruct Hhead; subst; simpl; auto.
Qed.

Canonical Structure snakelet_lang := Language snakelet_lang_mixin.

Lemma to_val_pure_step x x' : pure_step x x' → to_val x = None.
Proof. intros H; inversion H; simpl; auto. Qed.

Lemma to_val_head_step x σ x' σ' efs : head_step x σ x' σ' efs → to_val x = None.
Proof. intros H; inversion H; simpl; auto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  destruct Ki1, Ki2; simpl; intros Hn1 Hn2 Heq.
  all: first [discriminate Heq | idtac].
  all: injection Heq; intros; subst; simpl in *; try discriminate; auto.
Qed.

Lemma fill_not_pure Ki x : to_val x = None → ∀ e', pure_step (fill_item Ki x) e' → False.
Proof.
  intros Hval e' Hpure.
  destruct Ki; simpl in *; inversion Hpure; subst;
    try match goal with H: Val ?v = ?x |- _ => symmetry in H; injection H; intros -> end;
    simpl in Hval; congruence.
Qed.

Lemma fill_not_head Ki x : to_val x = None → ∀ σ e' σ' efs, head_step (fill_item Ki x) σ e' σ' efs → False.
Proof.
  intros Hval σ e' σ' efs Hhead.
  destruct Ki; simpl in *; inversion Hhead; subst;
    try match goal with H: Val ?v = ?x |- _ => symmetry in H; injection H; intros -> end;
    simpl in Hval; congruence.
Qed.

Global Instance snakelet_ctx_lang_ctx Ki :
  LanguageCtx (fill_item Ki).
Proof.
  split.
  - intros x Hval. destruct Ki; simpl; try (by inversion Hval); done.
  - intros x1 σ1 κ x2 σ2 efs Hprim.
    inversion Hprim as [K x σ x' Hpure | K x σ x' σ' efs0 Hhead]; subst.
    + eapply (PrimPureStep (Ki :: K) _ _ _ Hpure).
    + eapply (PrimHeadStep (Ki :: K) _ _ _ _ _ Hhead).
  - intros x1' σ1 κ x2 σ2 efs Hval Hprim.
    inversion Hprim; subst; [rename H0 into Hpure | rename H0 into Hhead].
    + unfold language.to_val in Hval; simpl in Hval.
      change (expr snakelet_lang) with sn_expr in *.
      rename Ki into Ki0.
      destruct K as [|Ki' K'']; simpl in H.
      { subst x. exfalso. eapply fill_not_pure; eauto. }
      pose proof (to_val_pure_step _ _ Hpure) as Hval_x.
      pose proof (fill_not_val K'' x Hval_x) as Hval_fill.
      pose proof (fill_item_no_val_inj Ki' Ki0 (fill_K K'' x) x1' Hval_fill Hval H) as Heq.
      subst Ki'.
      apply (fill_item_inj Ki0) in H.
      subst x1'.
      eexists (fill_K K'' x'); split.
      { simpl; reflexivity. }
      eapply (PrimPureStep K'' x σ2 x' Hpure).
    + unfold language.to_val in Hval; simpl in Hval.
      change (expr snakelet_lang) with sn_expr in *.
      rename Ki into Ki0.
      destruct K as [|Ki' K'']; simpl in H.
      { subst x. exfalso. eapply fill_not_head; eauto. }
      pose proof (to_val_head_step _ _ _ _ _ Hhead) as Hval_x.
      pose proof (fill_not_val K'' x Hval_x) as Hval_fill.
      pose proof (fill_item_no_val_inj Ki' Ki0 (fill_K K'' x) x1' Hval_fill Hval H) as Heq.
      subst Ki'.
      apply (fill_item_inj Ki0) in H.
      subst x1'.
      eexists (fill_K K'' x'); split.
      { simpl; reflexivity. }
      eapply (PrimHeadStep K'' x σ1 x' σ2 efs Hhead).
Qed.

End with_fun_ctx.

(** Notations for writing SnakeletLang programs tersely. *)
Module snakelet_notation.
  Declare Scope snakelet_scope.
  Delimit Scope snakelet_scope with S.

  Notation "# n" := (Val (LitInt (n : Z)))
    (at level 8, n at level 1, format "# n") : snakelet_scope.
  Notation "# l" := (Val (LitLoc (l : loc)))
    (at level 8, l at level 1, format "# l") : snakelet_scope.
  Notation "#true" := (Val (LitBool true)) : snakelet_scope.
  Notation "#false" := (Val (LitBool false)) : snakelet_scope.

  Notation "! e" := (Load e)
    (at level 9, right associativity, format "! e") : snakelet_scope.
  Notation "e1 <- e2" := (Store e1 e2)
    (at level 80, format "e1  <-  e2") : snakelet_scope.
  Notation "'ref' e" := (Alloc e)
    (at level 9, format "'ref'  e") : snakelet_scope.

  Notation "e1 + e2" := (BinOp AddOp e1 e2)
    (at level 50, left associativity) : snakelet_scope.
  Notation "e1 - e2" := (BinOp SubOp e1 e2)
    (at level 50, left associativity) : snakelet_scope.
  Notation "e1 * e2" := (BinOp MulOp e1 e2)
    (at level 40, left associativity) : snakelet_scope.
  Notation "e1 / e2" := (BinOp DivOp e1 e2)
    (at level 40, left associativity) : snakelet_scope.
  Notation "e1 = e2" := (BinOp EqOp e1 e2)
    (at level 70, no associativity) : snakelet_scope.
  Notation "e1 < e2" := (BinOp LtOp e1 e2)
    (at level 70, no associativity) : snakelet_scope.
  Notation "e1 <= e2" := (BinOp LeOp e1 e2)
    (at level 70, no associativity) : snakelet_scope.
End snakelet_notation.

Import snakelet_notation.

(* ========================================================================= *)
(*  SnakeletWp — Iris weakest-precondition proofs (ALL ADMITTED)             *)
(* ========================================================================= *)

Local Notation "l ↦{ dq } v" := (pointsto l dq v)
  (at level 20, dq custom dfrac at level 1, format "l  ↦{ dq }  v") : bi_scope.
Local Notation "l ↦ v" := (pointsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.

Class snakelet_heapGS_gen hlc Σ := SnakeletHeapGS {
  #[global] snakelet_invGS :: invGS_gen hlc Σ;
  #[global] snakelet_gen_heapG :: gen_heapGS loc sn_val Σ;
}.
Global Existing Instance snakelet_invGS.
Global Existing Instance snakelet_gen_heapG.
Notation snakelet_heapGS := (snakelet_heapGS_gen HasLc).

Section snakelet_wp.
  Context `{!snakelet_heapGS_gen hlc Σ}.
  Context `{FC : FunCtx}.

  Definition snakelet_state_interp (σ : sn_state) (ns : nat) (κs : list observation) (nt : nat) : iProp Σ :=
    gen_heap_interp σ.

  Global Program Instance snakelet_irisGS : irisGS_gen hlc snakelet_lang Σ := {|
    iris_invGS := snakelet_invGS;
    state_interp := snakelet_state_interp;
    fork_post _ := True%I;
    num_laters_per_step _ := 0%nat;
    state_interp_mono _ _ _ _ := fupd_intro _ _
  |}.
  Global Opaque iris_invGS.
  Implicit Types l : loc.

  (** Determinant lemmas — pure steps *)

  Lemma reducible_pure_step e e' σ :
    pure_step e e' → reducible e σ.
  Proof.
  Admitted.

  Lemma reducible_no_obs_pure_step e e' σ :
    pure_step e e' → reducible_no_obs e σ.
  Proof.
  Admitted.

  Lemma prim_binop_det op v1 v2 σ κ e2 σ2 efs :
    prim_step (BinOp op (Val v1) (Val v2)) σ κ e2 σ2 efs →
    κ = [] ∧ σ2 = σ ∧ efs = [] ∧ e2 = Val (binop_eval op v1 v2).
  Proof.
  Admitted.

  Lemma prim_let_det x v e σ κ e2 σ2 efs :
    prim_step (Let x (Val v) e) σ κ e2 σ2 efs →
    κ = [] ∧ σ2 = σ ∧ efs = [] ∧ e2 = subst x v e.
  Proof.
  Admitted.

  Lemma prim_if_true_det e1 e2 σ κ e2' σ2 efs :
    prim_step (If (Val (LitBool true)) e1 e2) σ κ e2' σ2 efs →
    κ = [] ∧ σ2 = σ ∧ efs = [] ∧ e2' = e1.
  Proof.
  Admitted.

  Lemma prim_if_false_det e1 e2 σ κ e2' σ2 efs :
    prim_step (If (Val (LitBool false)) e1 e2) σ κ e2' σ2 efs →
    κ = [] ∧ σ2 = σ ∧ efs = [] ∧ e2' = e2.
  Proof.
  Admitted.

  (** Head-step determinant lemmas *)

  Lemma head_load_det l σ e2 σ2 efs :
    head_step (Load (Val (LitLoc l))) σ e2 σ2 efs →
    ∃ v, σ !! l = Some v ∧ e2 = Val v ∧ σ2 = σ ∧ efs = [].
  Proof.
  Admitted.

  Lemma head_store_det l v σ e2 σ2 efs :
    head_step (Store (Val (LitLoc l)) (Val v)) σ e2 σ2 efs →
    is_Some (σ !! l) ∧ e2 = Val LitUnit ∧ σ2 = <[l:=v]> σ ∧ efs = [].
  Proof.
  Admitted.

  Lemma head_alloc_det v σ e2 σ2 efs :
    head_step (Alloc (Val v)) σ e2 σ2 efs →
    ∃ l, σ !! l = None ∧ e2 = Val (LitLoc l) ∧ σ2 = <[l:=v]> σ ∧ efs = [].
  Proof.
  Admitted.

  Lemma head_faa_det l v σ e2 σ2 efs :
    head_step (FAA (Val (LitLoc l)) (Val v)) σ e2 σ2 efs →
    ∃ z, σ !! l = Some (LitInt z) ∧
         e2 = Val (LitInt z) ∧ σ2 = <[l:=LitInt (z + lit_as_z v)]> σ ∧ efs = [].
  Proof.
  Admitted.

  Lemma head_fork_det e σ e2 σ2 efs :
    head_step (Fork e) σ e2 σ2 efs →
    e2 = Val LitUnit ∧ σ2 = σ ∧ efs = [e].
  Proof.
  Admitted.

  Lemma prim_load_det l σ κ e2 σ2 efs v :
    σ !! l = Some v →
    prim_step (Load (Val (LitLoc l))) σ κ e2 σ2 efs →
    κ = [] ∧ σ2 = σ ∧ efs = [] ∧ e2 = Val v.
  Proof.
  Admitted.

  Lemma prim_store_det l v σ κ e2 σ2 efs :
    is_Some (σ !! l) →
    prim_step (Store (Val (LitLoc l)) (Val v)) σ κ e2 σ2 efs →
    κ = [] ∧ σ2 = <[l:=v]> σ ∧ efs = [] ∧ e2 = Val LitUnit.
  Proof.
  Admitted.

  Lemma prim_alloc_det v σ κ e2 σ2 efs :
    prim_step (Alloc (Val v)) σ κ e2 σ2 efs →
    ∃ l, σ !! l = None ∧ κ = [] ∧ σ2 = <[l:=v]> σ ∧ efs = [] ∧ e2 = Val (LitLoc l).
  Proof.
  Admitted.

  (** Pure WP lemmas *)

  Lemma wp_binop s E op v1 v2 Φ :
    ▷ Φ (binop_eval op v1 v2) -∗
    WP BinOp op (Val v1) (Val v2) @ s; E {{ Φ }}.
  Proof.
  Admitted.

  Lemma wp_let s E x v e2 Φ :
    ▷ WP subst x v e2 @ s; E {{ Φ }} -∗
    WP Let x (Val v) e2 @ s; E {{ Φ }}.
  Proof.
  Admitted.

  Lemma wp_if_true s E e1 e2 Φ :
    ▷ WP e1 @ s; E {{ Φ }} -∗
    WP If (Val (LitBool true)) e1 e2 @ s; E {{ Φ }}.
  Proof.
  Admitted.

  Lemma wp_if_false s E e1 e2 Φ :
    ▷ WP e2 @ s; E {{ Φ }} -∗
    WP If (Val (LitBool false)) e1 e2 @ s; E {{ Φ }}.
  Proof.
  Admitted.

  (** Stateful WP lemmas *)

  Lemma wp_load s E l v Φ :
    l ↦ v -∗
    (l ↦ v -∗ Φ v) -∗
    WP Load (Val (LitLoc l)) @ s; E {{ Φ }}.
  Proof.
  Admitted.

  Lemma wp_store s E l v (w : sn_val) Φ :
    l ↦ v -∗
    (l ↦ w -∗ Φ LitUnit) -∗
    WP Store (Val (LitLoc l)) (Val w) @ s; E {{ Φ }}.
  Proof.
  Admitted.

  Lemma fresh_loc (σ : sn_state) : ∃ l, σ !! l = None.
  Proof.
  Admitted.

  Lemma wp_alloc s E v Φ :
    (∀ l, l ↦ v -∗ Φ (LitLoc l)) -∗
    WP Alloc (Val v) @ s; E {{ Φ }}.
  Proof.
  Admitted.

  (** Call inversion lemma *)

  Lemma prim_call_inv f vs σ κ e2 σ2 efs :
    prim_step (Call f (map Val vs)) σ κ e2 σ2 efs →
    κ = [] ∧ σ2 = σ ∧ efs = [] ∧
    ((∃ spec w, fun_entries f = Some (FunSpec spec) ∧ spec vs w ∧ e2 = Val w) ∨
     (∃ params body, fun_entries f = Some (FunDef params body) ∧
        length vs = length params ∧ e2 = subst_list params vs body)).
  Proof.
  Admitted.

  (** Opaque call: spec-driven reasoning *)

  Lemma wp_call s E f spec vs v Φ :
    fun_entries f = Some (FunSpec spec) →
    spec vs v →
    (∀ w : sn_val, ⌜spec vs w⌝ -∗ Φ w) -∗
    WP Call f (map Val vs) @ s; E {{ Φ }}.
  Proof.
  Admitted.

  (** Transparent call: unfold the definition *)

  Lemma wp_call_unfold s E f params body vs Φ :
    fun_entries f = Some (FunDef params body) →
    length vs = length params →
    ▷ WP subst_list params vs body @ s; E {{ Φ }} -∗
    WP Call f (map Val vs) @ s; E {{ Φ }}.
  Proof.
  Admitted.

  Ltac snakelet_pures :=
    repeat (iApply wp_binop || iApply wp_let || iApply wp_if_true || iApply wp_if_false).

End snakelet_wp.

Ltac snakelet_pure_step :=
  lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (BinOp ?op (Val ?v1) (Val ?v2)) ?Φ) =>
      iApply (@wp_binop _ _ _ _ _ _ _ op v1 v2 Φ)
  | |- environments.envs_entails _ (wp _ _ (Let ?x (Val ?v) ?e2) ?Φ) =>
      iApply (@wp_let _ _ _ _ _ _ _ x v e2 Φ)
  | |- environments.envs_entails _ (wp _ _ (If (Val (LitBool true)) ?e1 ?e2) ?Φ) =>
      iApply (@wp_if_true _ _ _ _ _ _ _ e1 e2 Φ)
  | |- environments.envs_entails _ (wp _ _ (If (Val (LitBool false)) ?e1 ?e2) ?Φ) =>
      iApply (@wp_if_false _ _ _ _ _ _ _ e1 e2 Φ)
  end.

Ltac snakelet_pures := repeat snakelet_pure_step.

Global Instance into_val_val `{FunCtx} v : IntoVal (Val v) v.
Proof. done. Qed.
