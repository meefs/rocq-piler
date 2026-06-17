Lemma close_admits_test : True /\ True /\ True.
Proof.
  split; [| split].
  - admit.
  - admit.
  - admit.
Admitted.

Lemma close_admits_mixed : (True /\ True) /\ (1 = 1).
Proof.
  split; [split |].
  - admit.
  - admit.
  - admit.
Admitted.
