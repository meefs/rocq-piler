From Stdlib Require Import Arith List Utf8.
Import ListNotations.

(* ASCII-only definitions *)
Definition f_ascii (xi : nat -> nat) (x : nat) : nat := xi x.
Definition g_ascii (sigma : nat -> nat) := sigma 0.

Lemma ascii_control : forall (n : nat), n = n.
Proof.
Admitted.

(* Unicode definitions that may shift byte offsets *)
Definition f (ξ : nat -> nat) (x : nat) : nat := ξ x.
Definition g (σ : nat -> nat) := σ 0.
Definition Σenv := 42.
Definition Γctx := 0.

Lemma unicode_preceding : forall (n : nat), n = n.
Proof.
Admitted.

Lemma ascii_oneline : True.
Proof. Admitted.
