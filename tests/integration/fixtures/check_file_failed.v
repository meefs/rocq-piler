(** Fixture for check_file status bug: items after a failure
    should NOT show [Qed] — they were never verified by Coq. *)

Lemma good_before : True.
Proof. exact I. Qed.

Lemma also_good : 1 = 1.
Proof. reflexivity. Qed.

(* This proof is wrong: exact I proves True, not False *)
Lemma broken_proof : False.
Proof. exact I. Qed.

(* These are syntactically correct Qed proofs but Coq
   never reaches them because of the error above. *)
Lemma unreachable_qed : True.
Proof. exact I. Qed.

Lemma also_unreachable : 1 = 1.
Proof. reflexivity. Qed.

Definition unreachable_def := 42.
