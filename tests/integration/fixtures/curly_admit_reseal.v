From Stdlib Require Import Arith.

(** Fixture for testing insert_tactic admit_hash inside curly-brace bullets
    where the inserted tactic leaves open subgoals.

    The proof starts as Admitted.  Tests will use insert_tactic to build
    a curly-brace bullet structure, then replace admits inside curlies
    with tactics that leave subgoals (e.g. destruct n.).  The re-seal
    must produce valid Coq with properly nested admits inside the { }.
 *)

Lemma curly_admit_reseal : forall n : nat, n + 0 = n.
Proof.
intro n. induction n.
{ simpl. reflexivity. }.
{ simpl. rewrite IHn. reflexivity. }.
Qed.

(** Second lemma: explicit curly-brace admits so we can test admit_hash
    replacement without first building the bullet structure. *)
Lemma curly_admit_prebuilt : forall n : nat, n + 0 = n.
Proof.
  intro n. induction n.
  { admit. }
  { admit. }
  simpl.
Admitted.
