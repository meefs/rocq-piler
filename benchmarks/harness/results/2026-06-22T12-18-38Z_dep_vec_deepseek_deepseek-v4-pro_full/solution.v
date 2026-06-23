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
intros t t' T Htype Hstep. revert T Htype. induction Hstep; intros T Htype.
inversion Htype; subst. apply T_Succ. apply IHHstep. auto.
inversion Htype; subst; eauto.
apply T_Cons with (n := n); [apply IHHstep; auto | auto].
inversion Htype; subst. apply T_Cons with (n := n); [auto | apply IHHstep; auto].
inversion Htype; subst. apply T_Head with (n := n); apply IHHstep; auto.
inversion Htype; subst. apply T_Tail with (n := n); apply IHHstep; auto.
inversion Htype; subst; eauto.
inversion H2; auto.
inversion Htype; subst; eauto.
inversion H2; auto.
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
induction 1.
left. apply V_Zero.
destruct IHhas_type; [left; apply V_Succ; auto | right; destruct H0; exists (tsucc x); apply S_Succ; auto].
left. apply V_Lit.
left. apply V_Nil.
destruct IHhas_type1 as [Vhd | [hd' Shd]]; [| right; exists (tcons hd' tl); apply S_ConsHd; auto]. destruct IHhas_type2 as [Vtl | [tl' Stl]]; [left; apply V_Cons; auto | right; exists (tcons hd tl'); apply S_ConsTl; auto].
destruct IHhas_type as [Vv | [v' Sv]]; [| right; exists (thead v'); apply S_Head; auto].
inversion H; subst; try discriminate; try (inversion Vv; fail).
inversion Vv; subst. right. exists hd. apply S_HeadCons; auto.
destruct IHhas_type as [Vv | [v' Sv]]; [| right; exists (ttail v'); apply S_Tail; auto].
inversion H; subst; try discriminate; try (inversion Vv; fail). inversion Vv; subst. right. exists tl. apply S_TailCons; auto.
Qed.

Theorem progress_neg : ~ (forall t T,
  has_type t T ->
  value t \/ exists t', step t t').
Proof.
Admitted.
