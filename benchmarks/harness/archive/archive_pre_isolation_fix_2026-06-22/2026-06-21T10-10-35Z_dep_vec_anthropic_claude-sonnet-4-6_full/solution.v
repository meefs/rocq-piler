From Stdlib Require Import Arith Lia.

(** * A simple dependently-typed language: Nat + Vec — Benchmark *)

(** ** Types *)
Inductive ty : Type :=
  | TNat  : ty
  | TVec  : nat -> ty.

(** ** Terms *)
Inductive tm : Type :=
  | tzero  : tm
  | tsucc  : tm -> tm
  | tlit   : nat -> tm
  | tnil   : tm
  | tcons  : tm -> tm -> tm
  | thead  : tm -> tm
  | ttail  : tm -> tm.

(** ** Typing *)
Inductive has_type : tm -> ty -> Prop :=
  | T_Zero  : has_type tzero TNat
  | T_Succ  : forall t,
      has_type t TNat ->
      has_type (tsucc t) TNat
  | T_Lit   : forall n,
      has_type (tlit n) TNat
  | T_Nil   : has_type tnil (TVec 0)
  | T_Cons  : forall hd tl n,
      has_type hd TNat ->
      has_type tl (TVec n) ->
      has_type (tcons hd tl) (TVec (S n))
  | T_Head  : forall v n,
      has_type v (TVec (S n)) ->
      has_type (thead v) TNat
  | T_Tail  : forall v n,
      has_type v (TVec (S n)) ->
      has_type (ttail v) (TVec n).

(** ** Values *)
Inductive value : tm -> Prop :=
  | V_Zero  : value tzero
  | V_Succ  : forall t, value t -> value (tsucc t)
  | V_Lit   : forall n, value (tlit n)
  | V_Nil   : value tnil
  | V_Cons  : forall hd tl, value hd -> value tl -> value (tcons hd tl).

(** ** Small-step reduction *)
Inductive step : tm -> tm -> Prop :=
  | S_Succ  : forall t t',
      step t t' ->
      step (tsucc t) (tsucc t')
  | S_ConsHd : forall hd hd' tl,
      step hd hd' ->
      step (tcons hd tl) (tcons hd' tl)
  | S_ConsTl : forall hd tl tl',
      value hd ->
      step tl tl' ->
      step (tcons hd tl) (tcons hd tl')
  | S_Head  : forall v v',
      step v v' ->
      step (thead v) (thead v')
  | S_Tail  : forall v v',
      step v v' ->
      step (ttail v) (ttail v')
  | S_HeadCons : forall hd tl,
      value hd -> value tl ->
      step (thead (tcons hd tl)) hd
  | S_TailCons : forall hd tl,
      value hd -> value tl ->
      step (ttail (tcons hd tl)) tl.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Theorem preservation : forall t t' T,
  has_type t T ->
  step t t' ->
  has_type t' T.
Proof.
  intros t t' T Htype Hstep.
  revert T Htype.
  induction Hstep; intros T Htype; inversion Htype; subst.
  - (* S_Succ *)
    apply T_Succ. apply IHHstep. assumption.
  - (* S_ConsHd *)
    apply T_Cons.
    + apply IHHstep. assumption.
    + assumption.
  - (* S_ConsTl *)
    apply T_Cons.
    + assumption.
    + apply IHHstep. assumption.
  - (* S_Head *)
    eapply T_Head. apply IHHstep. eassumption.
  - (* S_Tail *)
    eapply T_Tail. apply IHHstep. eassumption.
  - (* S_HeadCons: step (thead (tcons hd tl)) hd *)
    (* H: value hd, H0: value tl, H2: has_type (tcons hd tl) (TVec (S n)) *)
    inversion H2; subst. assumption.
  - (* S_TailCons: step (ttail (tcons hd tl)) tl *)
    (* H: value hd, H0: value tl, H2: has_type (tcons hd tl) (TVec (S n)) *)
    inversion H2; subst. assumption.
Qed.

Theorem preservation_neg : ~ (forall t t' T,
  has_type t T ->
  step t t' ->
  has_type t' T).
Proof.
Admitted.

(** ** Progress *)
Theorem progress : forall t T,
  has_type t T ->
  value t \/ exists t', step t t'.
Proof.
  intros t T Htype.
  induction Htype.
  - (* T_Zero *)
    left. apply V_Zero.
  - (* T_Succ *)
    destruct IHHtype as [Hval | [t' Hstep]].
    + left. apply V_Succ. assumption.
    + right. exists (tsucc t'). apply S_Succ. assumption.
  - (* T_Lit *)
    left. apply V_Lit.
  - (* T_Nil *)
    left. apply V_Nil.
  - (* T_Cons *)
    destruct IHHtype1 as [Hval1 | [hd' Hstep1]].
    + destruct IHHtype2 as [Hval2 | [tl' Hstep2]].
      * left. apply V_Cons; assumption.
      * right. exists (tcons hd tl'). apply S_ConsTl; assumption.
    + right. exists (tcons hd' tl). apply S_ConsHd. assumption.
  - (* T_Head: has_type v (TVec (S n)), goal: value (thead v) \/ ... *)
    destruct IHHtype as [Hval | [v' Hstep]].
    + (* v is a value of type TVec (S n) *)
      inversion Hval; subst; inversion Htype; subst.
      right. eexists. eapply S_HeadCons; eassumption.
    + right. exists (thead v'). apply S_Head. assumption.
  - (* T_Tail: has_type v (TVec (S n)), goal: value (ttail v) \/ ... *)
    destruct IHHtype as [Hval | [v' Hstep]].
    + inversion Hval; subst; inversion Htype; subst.
      right. eexists. eapply S_TailCons; eassumption.
    + right. exists (ttail v'). apply S_Tail. assumption.
Qed.

Theorem progress_neg : ~ (forall t T,
  has_type t T ->
  value t \/ exists t', step t t').
Proof.
Admitted.
