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

(** ** Canonical forms lemma *)
Lemma canonical_forms_vec_S : forall v n,
  value v -> has_type v (TVec (S n)) ->
  exists hd tl, v = tcons hd tl /\ value hd /\ value tl.
Proof.
  intros v n Hval Htype. inversion Hval; subst; inversion Htype; subst.
  - exists hd, tl. repeat split; assumption.
Qed.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Theorem preservation : forall t t' T,
  has_type t T ->
  step t t' ->
  has_type t' T.
Proof.
  intros t t' T Htype Hstep. revert T Htype.
  induction Hstep as [t1 t1' Hstep1 IH1
                     | hd1 hd1' tl1 Hstep1 IH1
                     | hd1 tl1 tl1' Hval1 Hstep1 IH1
                     | v1 v1' Hstep1 IH1
                     | v1 v1' Hstep1 IH1
                     | hd1 tl1 Hval1 Hval2
                     | hd1 tl1 Hval1 Hval2];
    intros T Htype.
  - inversion Htype as [| ? Ht | | | | |]; subst. apply T_Succ. apply IH1. exact Ht.
  - inversion Htype as [| | | | ? ? ? Hhd Htl | |]; subst. apply T_Cons. apply IH1. exact Hhd. exact Htl.
  - inversion Htype as [| | | | ? ? ? Hhd Htl | |]; subst. apply T_Cons. exact Hhd. apply IH1. exact Htl.
  - inversion Htype as [| | | | | ? ? Hv |]; subst. apply (T_Head v1' n). apply (IH1 (TVec (S n))). exact Hv.
  - inversion Htype as [| | | | | | ? ? Hv]; subst. apply (T_Tail v1' n). apply (IH1 (TVec (S n))). exact Hv.
  - inversion Htype as [| | | | | ? ? Hv |]; subst.
    inversion Hv as [| | | | | |]; subst. assumption.
  - inversion Htype as [| | | | | | ? ? Hv]; subst.
    inversion Hv as [| | | | | |]; subst. assumption.
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
  intros t T H. induction H.
  - left. apply V_Zero.
  - destruct IHhas_type as [Hval | (t' & Hstep)].
    + left. apply V_Succ. exact Hval.
    + right. exists (tsucc t'). apply S_Succ. exact Hstep.
  - left. apply V_Lit.
  - left. apply V_Nil.
  - destruct IHhas_type1 as [Hval_hd | (hd' & Hstep_hd)].
    + destruct IHhas_type2 as [Hval_tl | (tl' & Hstep_tl)].
      * left. apply V_Cons; assumption.
      * right. exists (tcons hd tl'). apply S_ConsTl; assumption.
    + right. exists (tcons hd' tl). apply S_ConsHd; assumption.
  - destruct IHhas_type as [Hval | (v' & Hstep)].
    + apply canonical_forms_vec_S with (v := v) (n := n) in Hval; auto.
      destruct Hval as (hd & tl & Heq & Hval_hd & Hval_tl).
      subst v. right. exists hd. apply S_HeadCons; auto.
    + right. exists (thead v'). apply S_Head; auto.
  - destruct IHhas_type as [Hval | (v' & Hstep)].
    + apply canonical_forms_vec_S with (v := v) (n := n) in Hval; auto.
      destruct Hval as (hd & tl & Heq & Hval_hd & Hval_tl).
      subst v. right. exists tl. apply S_TailCons; auto.
    + right. exists (ttail v'). apply S_Tail; auto.
Qed.

Theorem progress_neg : ~ (forall t T,
  has_type t T ->
  value t \/ exists t', step t t').
Proof.
Admitted.
