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
  intros t t' T HT HS.
  revert T HT.
  induction HS; intros T HT.
  - (* S_Succ *)
    inversion HT as [| ? Ht | | | | |]; subst.
    apply T_Succ. apply IHHS. exact Ht.
  - (* S_ConsHd *)
    inversion HT as [| | | | ? ? ? Hhd Htl | |]; subst.
    apply T_Cons with (n:=n).
    + apply IHHS. exact Hhd.
    + exact Htl.
  - (* S_ConsTl *)
    inversion HT as [| | | | ? ? ? Hhd Htl | |]; subst.
    apply T_Cons with (n:=n).
    + exact Hhd.
    + apply IHHS. exact Htl.
  - (* S_Head *)
    inversion HT as [| | | | | ? ? Hv |]; subst.
    apply T_Head with (n:=n). apply IHHS. exact Hv.
  - (* S_Tail *)
    inversion HT as [| | | | | | ? ? Hv]; subst.
    apply T_Tail with (n:=n). apply IHHS. exact Hv.
  - (* S_HeadCons *)
    inversion HT as [| | | | | ? ? Htc |]; subst.
    inversion Htc as [| | | | ? ? ? Hhd Htl | |]; subst.
    exact Hhd.
  - (* S_TailCons *)
    inversion HT as [| | | | | | ? ? Htc]; subst.
    inversion Htc as [| | | | ? ? ? Hhd Htl | |]; subst.
    exact Htl.
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
  intros t T HT.
  induction HT.
  - (* T_Zero *)
    left. apply V_Zero.
  - (* T_Succ *)
    destruct IHHT as [Hv | [t' HS']].
    + left. apply V_Succ. exact Hv.
    + right. exists (tsucc t'). apply S_Succ. exact HS'.
  - (* T_Lit *)
    left. apply V_Lit.
  - (* T_Nil *)
    left. apply V_Nil.
  - (* T_Cons *)
    destruct IHHT1 as [Hv_hd | [hd' HS_hd]].
    + destruct IHHT2 as [Hv_tl | [tl' HS_tl]].
      * left. apply V_Cons; assumption.
      * right. exists (tcons hd tl'). apply S_ConsTl; assumption.
    + right. exists (tcons hd' tl). apply S_ConsHd; assumption.
  - (* T_Head; IHHT : value v \/ (exists v', step v v'); also has_type v (TVec (S n)) is in context *)
    destruct IHHT as [Hval | [v' HS']].
    + (* Hval : value v *)
      inversion Hval; subst.
      * (* v = tzero *) match goal with [ H : has_type tzero _ |- _ ] => inversion H end.
      * (* v = tsucc _ *) match goal with [ H : has_type (tsucc _) _ |- _ ] => inversion H end.
      * (* v = tlit _ *) match goal with [ H : has_type (tlit _) _ |- _ ] => inversion H end.
      * (* v = tnil *) match goal with [ H : has_type tnil _ |- _ ] => inversion H end.
      * (* v = tcons hd tl *) right. exists hd. apply S_HeadCons; assumption.
    + right. exists (thead v'). apply S_Head; assumption.
  - (* T_Tail *)
    destruct IHHT as [Hval | [v' HS']].
    + inversion Hval; subst.
      * match goal with [ H : has_type tzero _ |- _ ] => inversion H end.
      * match goal with [ H : has_type (tsucc _) _ |- _ ] => inversion H end.
      * match goal with [ H : has_type (tlit _) _ |- _ ] => inversion H end.
      * match goal with [ H : has_type tnil _ |- _ ] => inversion H end.
      * right. exists tl. apply S_TailCons; assumption.
    + right. exists (ttail v'). apply S_Tail; assumption.
Qed.

Theorem progress_neg : ~ (forall t T,
  has_type t T ->
  value t \/ exists t', step t t').
Proof.
Admitted.
