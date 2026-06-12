(* Two-level case elimination benchmark: determinism of a small-step
   relation.  The proof requires induction on the first derivation,
   then inversion on the second derivation INSIDE each case — the
   classic "eliminate twice" pattern from dependently typed calculi.

   Outer stratify closes SPlusV / SIfT / SIfF (their inner analysis is
   uniform).  SPlusL and SPlusR survive: their inner sub-cases mix
   congruence-via-IH with impossibility, so they need a nested
   stratify with skeleton "inversion Hs2; subst". *)

Inductive expr : Type :=
  | ENum : nat -> expr
  | EPlus : expr -> expr -> expr
  | EIf : bool -> expr -> expr -> expr.

Inductive sstep : expr -> expr -> Prop :=
  | SPlusL : forall e1 e1' e2, sstep e1 e1' -> sstep (EPlus e1 e2) (EPlus e1' e2)
  | SPlusR : forall n e2 e2', sstep e2 e2' -> sstep (EPlus (ENum n) e2) (EPlus (ENum n) e2')
  | SPlusV : forall n m, sstep (EPlus (ENum n) (ENum m)) (ENum (n + m))
  | SIfT : forall e1 e2, sstep (EIf true e1 e2) e1
  | SIfF : forall e1 e2, sstep (EIf false e1 e2) e2.

Lemma num_nostep : forall n e, ~ sstep (ENum n) e.
Proof. intros n e H. inversion H. Qed.

Theorem sstep_det : forall e e1, sstep e e1 -> forall e2, sstep e e2 -> e1 = e2.
Proof.
Admitted.
