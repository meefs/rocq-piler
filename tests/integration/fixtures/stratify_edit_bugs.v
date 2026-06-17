(** Fixture for reproducing stratify/insert_tactics admit-hash mismatch
    and edit_file replaceAll bugs. *)

Inductive color : Type := Red | Green | Blue.

(* Proof with multiple cases — stratify should create unique-hashed admits *)
Lemma color_eq_dec : forall c1 c2 : color, {c1 = c2} + {c1 <> c2}.
Proof.
Admitted.

(* Marker for edit_file replaceAll test *)
Lemma marker_a : True.
Proof. exact I. Qed.
Lemma marker_b : True.
Proof. exact I. Qed.
Lemma marker_c : True.
Proof. exact I. Qed.
