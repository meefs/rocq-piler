From Stdlib Require Import Arith List Lia PeanoNat Bool Utf8.
Import ListNotations.

(** * Term Sharing via Hash-Consing — Benchmark
    DAG representation for a dependently typed calculus with inductives.
    Based on the term language from github.com/Scidonia/cyclic *)

(** ** Term language *)

Inductive tm : Type :=
| tVar (x : nat)
| tSort (i : nat)
| tPi (A : tm) (B : tm)
| tLam (A : tm) (t : tm)
| tApp (t u : tm)
| tFix (A : tm) (t : tm)
| tInd (I : nat)
| tRoll (I : nat) (c : nat) (args : list tm)
| tCase (I : nat) (scrut : tm) (C : tm) (brs : list tm).

(** ** Substitution machinery *)

Definition sub := nat -> tm.
Definition ids : sub := tVar.
Definition scons (s : tm) (σ : sub) : sub :=
  fun x => match x with 0 => s | S x => σ x end.

Fixpoint rename (ξ : nat -> nat) (t : tm) : tm :=
  match t with
  | tVar x => tVar (ξ x)
  | tSort i => tSort i
  | tPi A B => tPi (rename ξ A) (rename (fun x => match x with 0 => 0 | S x => S (ξ x) end) B)
  | tLam A t => tLam (rename ξ A) (rename (fun x => match x with 0 => 0 | S x => S (ξ x) end) t)
  | tApp t u => tApp (rename ξ t) (rename ξ u)
  | tFix A t => tFix (rename ξ A) (rename (fun x => match x with 0 => 0 | S x => S (ξ x) end) t)
  | tInd Ix => tInd Ix
  | tRoll Ix c args => tRoll Ix c (map (rename ξ) args)
  | tCase Ix scrut C brs =>
      tCase Ix (rename ξ scrut) (rename (fun x => match x with 0 => 0 | S x => S (ξ x) end) C) (map (rename ξ) brs)
  end.

Definition shift (n : nat) (t : tm) : tm := rename (Nat.add n) t.
Definition shift1 (t : tm) : tm := shift 1 t.

Definition up_sub (σ : sub) : sub :=
  scons (tVar 0) (fun x => shift1 (σ x)).

Fixpoint apply_sub (σ : sub) (t : tm) : tm :=
  match t with
  | tVar x => σ x
  | tSort i => tSort i
  | tPi A B => tPi (apply_sub σ A) (apply_sub (up_sub σ) B)
  | tLam A t => tLam (apply_sub σ A) (apply_sub (up_sub σ) t)
  | tApp t u => tApp (apply_sub σ t) (apply_sub σ u)
  | tFix A t => tFix (apply_sub σ A) (apply_sub (up_sub σ) t)
  | tInd Ix => tInd Ix
  | tRoll Ix c args => tRoll Ix c (map (apply_sub σ) args)
  | tCase Ix scrut C brs =>
      tCase Ix (apply_sub σ scrut) (apply_sub (up_sub σ) C) (map (apply_sub σ) brs)
  end.

Definition subst0 (s : tm) (t : tm) : tm :=
  apply_sub (scons s ids) t.

(** ** Term size *)

Fixpoint tm_size (t : tm) : nat :=
  match t with
  | tVar _ | tSort _ | tInd _ => 1
  | tPi A B => 1 + tm_size A + tm_size B
  | tLam A t => 1 + tm_size A + tm_size t
  | tApp t u => 1 + tm_size t + tm_size u
  | tFix A t => 1 + tm_size A + tm_size t
  | tRoll _ _ args =>
      1 + (fix go l := match l with [] => 0 | t :: l' => tm_size t + go l' end) args
  | tCase _ s C brs =>
      1 + tm_size s + tm_size C +
      (fix go l := match l with [] => 0 | t :: l' => tm_size t + go l' end) brs
  end.

(** ** Closedness *)

Fixpoint closed_below (n : nat) (t : tm) : bool :=
  match t with
  | tVar x => x <? n
  | tSort _ | tInd _ => true
  | tPi A B => closed_below n A && closed_below (S n) B
  | tLam A t => closed_below n A && closed_below (S n) t
  | tApp t u => closed_below n t && closed_below n u
  | tFix A t => closed_below n A && closed_below (S n) t
  | tRoll _ _ args =>
      (fix go l := match l with [] => true | t :: l' => closed_below n t && go l' end) args
  | tCase _ s C brs =>
      closed_below n s && closed_below (S n) C &&
      (fix go l := match l with [] => true | t :: l' => closed_below n t && go l' end) brs
  end.

Definition closed (t : tm) : Prop := closed_below 0 t = true.

(** ** DAG representation *)

Inductive node : Type :=
| nVar (x : nat)
| nSort (i : nat)
| nPi (a b : nat)
| nLam (a t : nat)
| nApp (t u : nat)
| nFix (a t : nat)
| nInd (I : nat)
| nRoll (I c : nat) (args : list nat)
| nCase (I : nat) (scrut mot : nat) (brs : list nat).

Definition dag := list node.

(** ** Decidable equality on nodes (infrastructure — proved) *)

Lemma list_nat_eq_dec : forall (l1 l2 : list nat), {l1 = l2} + {l1 <> l2}.
Proof. decide equality. apply Nat.eq_dec. Defined.

Lemma node_eq_dec : forall (n1 n2 : node), {n1 = n2} + {n1 <> n2}.
Proof. decide equality; try apply Nat.eq_dec; try apply list_nat_eq_dec. Defined.

Definition node_eqb (n1 n2 : node) : bool :=
  if node_eq_dec n1 n2 then true else false.

Lemma node_eqb_eq : forall n1 n2, node_eqb n1 n2 = true <-> n1 = n2.
Proof.
  intros. unfold node_eqb. destruct (node_eq_dec n1 n2); split; intros; auto; discriminate.
Qed.

(** ** Interning: lookup-or-append *)

Fixpoint find_index (f : node -> bool) (tbl : dag) (acc : nat) : option nat :=
  match tbl with
  | [] => None
  | n :: rest => if f n then Some acc else find_index f rest (S acc)
  end.

Definition intern (n : node) (tbl : dag) : dag * nat :=
  match find_index (node_eqb n) tbl 0 with
  | Some idx => (tbl, idx)
  | None => (tbl ++ [n], length tbl)
  end.

(** ** Sharing: tree → DAG *)

Fixpoint share (t : tm) (tbl : dag) {struct t} : dag * nat :=
  match t with
  | tVar x => intern (nVar x) tbl
  | tSort i => intern (nSort i) tbl
  | tPi A B =>
      let '(tbl1, a) := share A tbl in
      let '(tbl2, b) := share B tbl1 in
      intern (nPi a b) tbl2
  | tLam A body =>
      let '(tbl1, a) := share A tbl in
      let '(tbl2, ti) := share body tbl1 in
      intern (nLam a ti) tbl2
  | tApp f arg =>
      let '(tbl1, fi) := share f tbl in
      let '(tbl2, ai) := share arg tbl1 in
      intern (nApp fi ai) tbl2
  | tFix A body =>
      let '(tbl1, a) := share A tbl in
      let '(tbl2, ti) := share body tbl1 in
      intern (nFix a ti) tbl2
  | tInd Ix => intern (nInd Ix) tbl
  | tRoll Ix c args =>
      let '(tbl1, idxs) :=
        (fix go (ts : list tm) (acc : dag) {struct ts} : dag * list nat :=
          match ts with
          | [] => (acc, [])
          | t0 :: rest =>
              let '(acc1, idx) := share t0 acc in
              let '(acc2, idxs) := go rest acc1 in
              (acc2, idx :: idxs)
          end) args tbl in
      intern (nRoll Ix c idxs) tbl1
  | tCase Ix scrut C brs =>
      let '(tbl1, si) := share scrut tbl in
      let '(tbl2, ci) := share C tbl1 in
      let '(tbl3, bis) :=
        (fix go (ts : list tm) (acc : dag) {struct ts} : dag * list nat :=
          match ts with
          | [] => (acc, [])
          | t0 :: rest =>
              let '(acc1, idx) := share t0 acc in
              let '(acc2, idxs) := go rest acc1 in
              (acc2, idx :: idxs)
          end) brs tbl2 in
      intern (nCase Ix si ci bis) tbl3
  end.

(** ** Unfolding: DAG → tree *)

Fixpoint unfold (tbl : dag) (fuel : nat) (idx : nat) : option tm :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match nth_error tbl idx with
    | None => None
    | Some (nVar x) => Some (tVar x)
    | Some (nSort i) => Some (tSort i)
    | Some (nPi a b) =>
        match unfold tbl fuel' a, unfold tbl fuel' b with
        | Some A, Some B => Some (tPi A B)
        | _, _ => None
        end
    | Some (nLam a t) =>
        match unfold tbl fuel' a, unfold tbl fuel' t with
        | Some A, Some T => Some (tLam A T)
        | _, _ => None
        end
    | Some (nApp t u) =>
        match unfold tbl fuel' t, unfold tbl fuel' u with
        | Some T, Some U => Some (tApp T U)
        | _, _ => None
        end
    | Some (nFix a t) =>
        match unfold tbl fuel' a, unfold tbl fuel' t with
        | Some A, Some T => Some (tFix A T)
        | _, _ => None
        end
    | Some (nInd Ix) => Some (tInd Ix)
    | Some (nRoll Ix c args) =>
        match (fix go (l : list nat) :=
                 match l with
                 | [] => Some []
                 | i :: l' =>
                     match unfold tbl fuel' i, go l' with
                     | Some t0, Some ts => Some (t0 :: ts)
                     | _, _ => None
                     end
                 end) args with
        | Some ts => Some (tRoll Ix c ts)
        | None => None
        end
    | Some (nCase Ix s m brs) =>
        match unfold tbl fuel' s, unfold tbl fuel' m,
              (fix go (l : list nat) :=
                 match l with
                 | [] => Some []
                 | i :: l' =>
                     match unfold tbl fuel' i, go l' with
                     | Some t0, Some ts => Some (t0 :: ts)
                     | _, _ => None
                     end
                 end) brs with
        | Some Sc, Some Mo, Some Bs => Some (tCase Ix Sc Mo Bs)
        | _, _, _ => None
        end
    end
  end.

(** ** DAG-level substitution for closed terms *)

(** Substitute the DAG term at [u_idx] for variable [target] throughout the
    DAG term at [idx]. Under binders (Pi, Lam, Fix, Case motive), [target]
    is incremented. Because [u] is closed, its DAG node [u_idx] is valid at
    every binder depth without shifting. *)

Fixpoint dag_subst_closed
  (tbl : dag) (u_idx : nat) (target : nat) (idx : nat) (fuel : nat)
  : dag * nat :=
  match fuel with
  | 0 => (tbl, idx)
  | S fuel' =>
    match nth_error tbl idx with
    | None => (tbl, idx)
    | Some (nVar x) =>
        if Nat.eqb x target then (tbl, u_idx)
        else if target <? x then intern (nVar (x - 1)) tbl
        else (tbl, idx)
    | Some (nSort _) | Some (nInd _) => (tbl, idx)
    | Some (nPi a b) =>
        let '(tbl1, a') := dag_subst_closed tbl u_idx target a fuel' in
        let '(tbl2, b') := dag_subst_closed tbl1 u_idx (S target) b fuel' in
        intern (nPi a' b') tbl2
    | Some (nLam a ti) =>
        let '(tbl1, a') := dag_subst_closed tbl u_idx target a fuel' in
        let '(tbl2, t') := dag_subst_closed tbl1 u_idx (S target) ti fuel' in
        intern (nLam a' t') tbl2
    | Some (nApp ti ui) =>
        let '(tbl1, t') := dag_subst_closed tbl u_idx target ti fuel' in
        let '(tbl2, u') := dag_subst_closed tbl1 u_idx target ui fuel' in
        intern (nApp t' u') tbl2
    | Some (nFix a ti) =>
        let '(tbl1, a') := dag_subst_closed tbl u_idx target a fuel' in
        let '(tbl2, t') := dag_subst_closed tbl1 u_idx (S target) ti fuel' in
        intern (nFix a' t') tbl2
    | Some (nRoll Ix c args) =>
        let '(tbl1, args') :=
          (fix go tbl0 (l : list nat) :=
            match l with
            | [] => (tbl0, [])
            | i :: l' =>
                let '(tbl1, i') := dag_subst_closed tbl0 u_idx target i fuel' in
                let '(tbl2, is') := go tbl1 l' in
                (tbl2, i' :: is')
            end) tbl args in
        intern (nRoll Ix c args') tbl1
    | Some (nCase Ix s m brs) =>
        let '(tbl1, s') := dag_subst_closed tbl u_idx target s fuel' in
        let '(tbl2, m') := dag_subst_closed tbl1 u_idx (S target) m fuel' in
        let '(tbl3, brs') :=
          (fix go tbl0 (l : list nat) :=
            match l with
            | [] => (tbl0, [])
            | i :: l' =>
                let '(tbl1, i') := dag_subst_closed tbl0 u_idx target i fuel' in
                let '(tbl2, is') := go tbl1 l' in
                (tbl2, i' :: is')
            end) tbl2 brs in
        intern (nCase Ix s' m' brs') tbl3
    end
  end.

(** ** Helper definitions and lemmas for the share_size_le proof *)

Fixpoint share_list (ts : list tm) (tbl : dag) : dag * list nat :=
  match ts with
  | [] => (tbl, [])
  | t0 :: rest =>
      let '(tbl1, idx) := share t0 tbl in
      let '(tbl2, idxs) := share_list rest tbl1 in
      (tbl2, idx :: idxs)
  end.

Lemma share_tRoll_eq : forall I c args tbl,
  share (tRoll I c args) tbl =
  let '(tbl1, idxs) := share_list args tbl in intern (nRoll I c idxs) tbl1.
Proof. reflexivity. Qed.

Lemma share_tCase_eq : forall I scrut C brs tbl,
  share (tCase I scrut C brs) tbl =
  let '(tbl1, si) := share scrut tbl in
  let '(tbl2, ci) := share C tbl1 in
  let '(tbl3, bis) := share_list brs tbl2 in intern (nCase I si ci bis) tbl3.
Proof. reflexivity. Qed.

Lemma intern_length_succ : forall n tbl,
  length (fst (intern n tbl)) <= length tbl + 1.
Proof.
  intros n tbl.
  unfold intern.
  destruct (find_index (node_eqb n) tbl 0) as [idx|].
  - simpl; lia.
  - simpl; rewrite length_app; simpl; lia.
Qed.

Fixpoint sum_sizes (ts : list tm) : nat :=
  match ts with
  | [] => 0
  | t :: ts' => tm_size t + sum_sizes ts'
  end.

Lemma tm_size_tRoll : forall I c args,
  tm_size (tRoll I c args) = 1 + sum_sizes args.
Proof.
  induction args as [|t args IH]; simpl; rewrite ?IH; auto.
Qed.

Lemma tm_size_tCase : forall I scrut C brs,
  tm_size (tCase I scrut C brs) = 1 + tm_size scrut + tm_size C + sum_sizes brs.
Proof.
  intros I scrut C brs.
  induction brs as [|t brs IH]; simpl; rewrite ?IH; auto.
Qed.

Lemma share_length_bound : forall t tbl,
  length (fst (share t tbl)) <= length tbl + tm_size t.
Proof.
  enough (forall n t tbl, tm_size t < n -> length (fst (share t tbl)) <= length tbl + tm_size t) as H.
  { intros t tbl; eapply (H (S (tm_size t)) t tbl); lia. }
  induction n; intros t tbl Hsize.
  - lia.
  - destruct t as [x|i|A B|A body|f arg|A fixbody|Ix|I c args|I scrut C brs].
    + (* tVar x *)
      simpl. apply intern_length_succ.
    + (* tSort i *)
      simpl. apply intern_length_succ.
    + (* tPi A B *)
      simpl.
      destruct (share A tbl) as [tbl1 a] eqn:E1.
      destruct (share B tbl1) as [tbl2 b] eqn:E2.
      simpl.
      assert (HAsize : tm_size A < n) by (simpl in Hsize; lia).
      pose proof (IHn A tbl HAsize) as IHA.
      rewrite E1 in IHA; simpl in IHA.
      assert (HBsize : tm_size B < n) by (simpl in Hsize; lia).
      pose proof (IHn B tbl1 HBsize) as IHB.
      rewrite E2 in IHB; simpl in IHB.
      unfold intern; simpl.
      destruct (find_index (node_eqb (nPi a b)) tbl2 0) as [idx|]; simpl;
      [lia|rewrite length_app; simpl; lia].
    + (* tLam A body *)
      simpl.
      destruct (share A tbl) as [tbl1 a] eqn:E1.
      destruct (share body tbl1) as [tbl2 ti] eqn:E2.
      simpl.
      assert (HAsize : tm_size A < n) by (simpl in Hsize; lia).
      pose proof (IHn A tbl HAsize) as IHA.
      rewrite E1 in IHA; simpl in IHA.
      assert (HBsize : tm_size body < n) by (simpl in Hsize; lia).
      pose proof (IHn body tbl1 HBsize) as IHB.
      rewrite E2 in IHB; simpl in IHB.
      unfold intern; simpl.
      destruct (find_index (node_eqb (nLam a ti)) tbl2 0) as [idx|]; simpl;
      [lia|rewrite length_app; simpl; lia].
    + (* tApp f arg *)
      simpl.
      destruct (share f tbl) as [tbl1 a] eqn:E1.
      destruct (share arg tbl1) as [tbl2 b] eqn:E2.
      simpl.
      assert (HFsize : tm_size f < n) by (simpl in Hsize; lia).
      pose proof (IHn f tbl HFsize) as IHF.
      rewrite E1 in IHF; simpl in IHF.
      assert (HAsize : tm_size arg < n) by (simpl in Hsize; lia).
      pose proof (IHn arg tbl1 HAsize) as IHA.
      rewrite E2 in IHA; simpl in IHA.
      unfold intern; simpl.
      destruct (find_index (node_eqb (nApp a b)) tbl2 0) as [idx|]; simpl;
      [lia|rewrite length_app; simpl; lia].
    + (* tFix A fixbody *)
      simpl.
      destruct (share A tbl) as [tbl1 a] eqn:E1.
      destruct (share fixbody tbl1) as [tbl2 ti] eqn:E2.
      simpl.
      assert (HAsize : tm_size A < n) by (simpl in Hsize; lia).
      pose proof (IHn A tbl HAsize) as IHA.
      rewrite E1 in IHA; simpl in IHA.
      assert (HFsize : tm_size fixbody < n) by (simpl in Hsize; lia).
      pose proof (IHn fixbody tbl1 HFsize) as IHF.
      rewrite E2 in IHF; simpl in IHF.
      unfold intern; simpl.
      destruct (find_index (node_eqb (nFix a ti)) tbl2 0) as [idx|]; simpl;
      [lia|rewrite length_app; simpl; lia].
    + (* tInd Ix *)
      simpl. apply intern_length_succ.
    + (* tRoll I c args *)
      rewrite share_tRoll_eq.
      destruct (share_list args tbl) as [tbl1 idxs] eqn:Esl; simpl.
      rewrite tm_size_tRoll in Hsize.
      assert (length tbl1 <= length tbl + sum_sizes args).
      { revert tbl tbl1 idxs Esl Hsize.
        induction args as [|t0 args IHargs]; intros tbl0 tbl1 idxs Esl Hsize.
        { simpl in Esl; inversion Esl; subst; simpl; apply Nat.le_add_r. }
        { simpl in Esl.
          simpl sum_sizes in Hsize.
          destruct (share t0 tbl0) as [tbl' a] eqn:Et0.
          destruct (share_list args tbl') as [tbl'' ixs'] eqn:Eargs.
          inversion Esl; subst tbl1 idxs; clear Esl.
          simpl.
          assert (Ht0size : tm_size t0 < n) by lia.
          pose proof (IHn t0 tbl0 Ht0size) as Ht0bound.
          rewrite Et0 in Ht0bound; simpl in Ht0bound.
          assert (Hsize_tail : 1 + sum_sizes args < S n) by lia.
          pose proof (IHargs tbl' tbl'' ixs' Eargs Hsize_tail).
          lia. } }
      pose proof (intern_length_succ (nRoll I c idxs) tbl1) as Hint.
      cut (1 + sum_sizes args <= tm_size (tRoll I c args)).
      { intro; lia. }
      rewrite tm_size_tRoll.
      apply Nat.le_refl.
    + (* tCase I scrut C brs *)
      rewrite share_tCase_eq.
      destruct (share scrut tbl) as [tbl1 si] eqn:Escrut.
      destruct (share C tbl1) as [tbl2 ci] eqn:EC.
      destruct (share_list brs tbl2) as [tbl3 bis] eqn:Els; simpl.
      assert (HSsize : tm_size scrut < n) by (simpl in Hsize; lia).
      pose proof (IHn scrut tbl HSsize) as IHscrut.
      rewrite Escrut in IHscrut; simpl in IHscrut.
      assert (HCsize : tm_size C < n) by (simpl in Hsize; lia).
      pose proof (IHn C tbl1 HCsize) as IHC.
      rewrite EC in IHC; simpl in IHC.
      rewrite tm_size_tCase in Hsize.
      assert (length tbl3 <= length tbl2 + sum_sizes brs).
      { revert tbl2 tbl3 bis Els Hsize.
        induction brs as [|t0 brs IHbrs]; intros tbl2 tbl3 bis Els Hsize.
        { simpl in Els; inversion Els; subst; simpl; apply Nat.le_add_r. }
        { simpl in Els.
          simpl sum_sizes in Hsize.
          destruct (share t0 tbl2) as [tbl' a] eqn:Et0.
          destruct (share_list brs tbl') as [tbl'' ixs'] eqn:Eargs.
          inversion Els; subst tbl3 bis; clear Els.
          simpl.
          assert (Ht0size : tm_size t0 < n) by lia.
          pose proof (IHn t0 tbl2 Ht0size) as Ht0bound.
          rewrite Et0 in Ht0bound; simpl in Ht0bound.
          assert (Hsize_tail : 1 + tm_size scrut + tm_size C + sum_sizes brs < S n) by lia.
          pose proof (IHbrs tbl' tbl'' ixs' Hsize_tail Eargs).
          lia. } }
      pose proof (intern_length_succ (nCase I si ci bis) tbl3) as Hint.
      cut (1 + tm_size scrut + tm_size C + sum_sizes brs <= tm_size (tCase I scrut C brs)).
      { intro; lia. }
      rewrite tm_size_tCase.
      apply Nat.le_refl.
Qed.

Lemma share_list_length : forall ts tbl,
  length (fst (share_list ts tbl)) <= length tbl + sum_sizes ts.
Proof.
  induction ts as [|t ts IH]; intros tbl.
  - simpl; lia.
  - simpl.
    destruct (share t tbl) as [tbl1 a] eqn:Et.
    destruct (share_list ts tbl1) as [tbl2 idxs] eqn:Els.
    simpl.
    pose proof (share_length_bound t tbl).
    rewrite Et in H; simpl in H.
    pose proof (IH tbl1).
    rewrite Els in H0; simpl in H0.
    lia.
Qed.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Theorem unfold_share : forall t,
  let '(tbl, idx) := share t [] in
  unfold tbl (length tbl) idx = Some t.
Proof. Admitted.

Theorem unfold_share_neg : ~ (forall t,
  let '(tbl, idx) := share t [] in
  unfold tbl (length tbl) idx = Some t).
Proof. Admitted.

Theorem share_size_le : forall t,
  length (fst (share t [])) <= tm_size t.
Proof.
  intros t.
  pose proof (share_length_bound t []).
  simpl in H; exact H.
Qed.

Theorem share_size_le_neg : ~ (forall t,
  length (fst (share t [])) <= tm_size t).
Proof. Admitted.

Theorem share_dup_lt : forall t,
  tm_size t >= 1 ->
  length (fst (share (tApp t t) [])) < tm_size (tApp t t).
Proof. Admitted.

Theorem share_dup_lt_neg : ~ (forall t,
  tm_size t >= 1 ->
  length (fst (share (tApp t t) [])) < tm_size (tApp t t)).
Proof. Admitted.

Theorem dag_subst_closed_correct : forall t u,
  closed u ->
  let '(tbl_u, idx_u) := share u [] in
  let '(tbl_t, idx_t) := share t tbl_u in
  let '(tbl_res, idx_res) :=
    dag_subst_closed tbl_t idx_u 0 idx_t (length tbl_t) in
  unfold tbl_res (length tbl_res) idx_res = Some (subst0 u t).
Proof. Admitted.

Theorem dag_subst_closed_correct_neg : ~ (forall t u,
  closed u ->
  let '(tbl_u, idx_u) := share u [] in
  let '(tbl_t, idx_t) := share t tbl_u in
  let '(tbl_res, idx_res) :=
    dag_subst_closed tbl_t idx_u 0 idx_t (length tbl_t) in
  unfold tbl_res (length tbl_res) idx_res = Some (subst0 u t)).
Proof. Admitted.
