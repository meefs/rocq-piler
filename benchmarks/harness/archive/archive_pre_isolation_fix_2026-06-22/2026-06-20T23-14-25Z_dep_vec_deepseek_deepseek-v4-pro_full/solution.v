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
  intros t t' T Ht Hs; generalize dependent T; induction Hs; intros T Ht; inversion Ht; subst.
  { (* S_Succ:b7d58600 *) solve [ eauto using has_type ]. }
  { (* S_ConsHd:6f6a8f3f *) solve [ eauto using has_type ]. }
  { (* S_ConsTl:d4b192e7 *) solve [ eauto using has_type ]. }
  { (* S_Head:f5db2187 *) solve [ eauto using has_type ]. }
  { (* S_Tail:e91ffac9 *) solve [ eauto using has_type ]. }
  { (* S_HeadCons:eee10165 *) inversion H2; subst; assumption.
  }
  { (* S_TailCons:8365dbb0 *) inversion H2; subst; assumption.
  }
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
  intros t T Ht; induction Ht.
  { (* T_Zero:82f70714 *) solve [ left; constructor; auto ]. }
  { (* T_Succ:d627f52a *) solve [ destruct IHHt as [Hv | [t' Hs]]; [left; constructor; auto | right; eexists; constructor; eauto] ]. }
  { (* T_Lit:df0386de *) solve [ left; constructor; auto ]. }
  { (* T_Nil:1b3ed6d8 *) solve [ left; constructor; auto ]. }
  { (* T_Cons:8c5411b3 *) solve [ destruct IHHt1 as [Hv1 | [t1' Hs1]]; [destruct IHHt2 as [Hv2 | [t2' Hs2]]; [left; constructor; auto | right; eexists; eapply S_ConsTl; eauto] | right; eexists; eapply S_ConsHd; eauto] ]. }
  { (* T_Head:24fffffc *) solve [ destruct IHHt as [Hv | [v' Hs]]; [right; inversion Hv; subst; inversion Ht; subst; eexists; eapply S_HeadCons; eauto | right; eexists; constructor; eauto] ]. }
  { (* T_Tail:ef375e2c *) solve [ destruct IHHt as [Hv | [v' Hs]]; [right; inversion Hv; subst; inversion Ht; subst; eexists; eapply S_TailCons; eauto | right; eexists; constructor; eauto] ]. }
Qed.

Theorem progress_neg : ~ (forall t T,
  has_type t T ->
  value t \/ exists t', step t t').
Proof.
Admitted.
