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
  intros t t' T Ht Hstep. revert t' Hstep.
  induction Ht as [ | t Ht0 IHt0 | n
                   | 
                   | hd tl n Hhd IHhd Htl IHtl
                   | v n Hv IHv
                   | v n Hv IHv ];
    intros t' Hst; inversion Hst; subst.
  - match goal with H: step t ?y |- has_type (tsucc ?y) TNat =>
      apply T_Succ; apply (IHt0 _ H) end.
  - match goal with H: step hd ?y |- has_type (tcons ?y tl) (TVec (S n)) =>
      apply T_Cons with (n:=n); [apply (IHhd _ H) | apply Htl] end.
  - match goal with H: step tl ?y |- has_type (tcons hd ?y) (TVec (S n)) =>
      apply T_Cons with (n:=n); [apply Hhd | apply (IHtl _ H)] end.
  - match goal with H: step v ?y |- has_type (thead ?y) TNat =>
      apply T_Head with (n:=n); apply (IHv _ H) end.
  - inversion Hv; assumption.
  - match goal with H: step v ?y |- has_type (ttail ?y) (TVec n) =>
      apply T_Tail with (n:=n); apply (IHv _ H) end.
  - inversion Hv; assumption.
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
  intros t T Ht. induction Ht as [ | t Ht0 IHt0 | n
                                  | 
                                  | hd tl n Hhd IHhd Htl IHtl
                                  | v n Hv IHv
                                  | v n Hv IHv ].
  - left. apply V_Zero.
  - destruct IHt0 as [Hval | (t' & Hst)].
    + left. apply V_Succ; auto.
    + right. exists (tsucc t'). apply S_Succ; auto.
  - left. apply V_Lit.
  - left. apply V_Nil.
  - destruct IHhd as [Hv1 | (hd' & Hst1)].
    + destruct IHtl as [Hv2 | (tl' & Hst2)].
      * left. apply V_Cons; auto.
      * right. exists (tcons hd tl'). apply S_ConsTl; auto.
    + right. exists (tcons hd' tl). apply S_ConsHd; auto.
  - destruct IHv as [Hval | (v' & Hst)].
    + inversion Hval; subst; [inversion Hv | inversion Hv | inversion Hv | inversion Hv | ].
      match goal with
      | H0: value ?hd0, H1: value ?tl0 |- _ =>
        right; exists hd0; apply S_HeadCons; auto
      end.
    + right. exists (thead v'). apply S_Head; auto.
  - destruct IHv as [Hval | (v' & Hst)].
    + inversion Hval; subst; [inversion Hv | inversion Hv | inversion Hv | inversion Hv | ].
      match goal with
      | H0: value ?hd0, H1: value ?tl0 |- _ =>
        right; exists tl0; apply S_TailCons; auto
      end.
    + right. exists (ttail v'). apply S_Tail; auto.
Qed.

Theorem progress_neg : ~ (forall t T,
  has_type t T ->
  value t \/ exists t', step t t').
Proof.
Admitted.
