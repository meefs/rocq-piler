From Stdlib Require Import Arith.

(** Experiment: term refinement proofs using holes (_) and the refine tactic.

    Instead of imperative tactic scripts:

        induction n; simpl; auto.

    we write proof *terms* with holes, and refine fills each hole:

        refine (
          nat_ind _ (eq_refl 0)
            (fun n IHn => eq_ind _ (S n) IHn _)
          n
        ).

    Each _ becomes a subgoal that the LLM can fill in a subsequent step. *)

(* Lemma 1: n + 0 = n — the simplest induction proof *)
Lemma plus_n_O : forall n : nat, n + 0 = n.
Proof.
  refine (
    nat_ind _ (eq_refl 0)
      (fun n IHn =>
        eq_ind _ (S n) (f_equal S IHn) _)
      n
  ).
  - (* base case: 0 + 0 = 0 *) simpl. reflexivity.
  - (* step case side condition (implicit arg) *) simpl. reflexivity.
Qed.

(* Lemma 2: 0 + n = n — proof entirely via refine with _ holes,
    no tactic blocks (just exact terms filling each hole) *)
Lemma plus_O_n : forall n : nat, 0 + n = n.
Proof.
  refine (
    nat_ind (fun n => 0 + n = n) (eq_refl 0)
      (fun n IHn => eq_ind _ (S n) (f_equal S IHn) _)
      n
  ).
  - (* base case hole: 0 + 0 = 0 *) exact (eq_refl 0).
  - (* step case hole: 0 + S n = S n [in eq_ind context] *) simpl. exact (eq_refl (S n)).
Qed.

(* Lemma 3: addition is associative — demonstrates deep term construction *)
Lemma plus_assoc : forall a b c : nat, a + b + c = a + (b + c).
Proof.
  refine (
    nat_ind (fun a => forall b c, a + b + c = a + (b + c))
      (fun b c => eq_refl (b + c))
      (fun a IHa b c =>
        eq_ind _ (S (a + b + c))
          (eq_ind _ (S (a + b + c))
            (f_equal S (IHa b c))
            (a + b + c = a + (b + c)))
          (S (a + b) + c = S (a + (b + c))))
      a
  ).
  (* Each hole: trivial simplification *) simpl. reflexivity.
  simpl. reflexivity.
  simpl. reflexivity.
Qed.

(* Lemma 4: to be completed via refine — the experiment target *)
Lemma plus_comm : forall n m : nat, n + m = m + n.
Proof.
  refine (fun n => nat_ind (fun n0 => forall m, n0 + m = m + n0) (fun m => _) (fun n0 IHn m => _) n).
  - rewrite (plus_n_O m). simpl. reflexivity.
  - simpl. simpl in IHn. rewrite (IHn m). rewrite (Nat.add_succ_r m n0) at 2. reflexivity.
Qed.
