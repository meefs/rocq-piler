Require Import Arith.

Lemma leb_total : forall n m, (n <=? m) = true \/ (m <=? n) = true.
Proof.
induction n as [| n' IHn]; intro m.
- left. destruct m; reflexivity.
- destruct m as [| m']; [right; reflexivity | simpl; destruct (IHn m') as [H | H]; [left; assumption | right; assumption]].
Qed.

