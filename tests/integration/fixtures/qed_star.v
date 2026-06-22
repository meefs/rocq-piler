Lemma foo : True.
Proof. Admitted.

Lemma bar : True.
Proof. exact foo. Qed.

Lemma baz : 1 = 1.
Proof. reflexivity. Qed.
