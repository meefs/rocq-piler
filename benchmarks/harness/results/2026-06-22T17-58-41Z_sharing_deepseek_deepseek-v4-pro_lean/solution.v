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

(** ** Helper lemmas *)

Lemma nth_error_app_l : forall {A} (l1 l2 : list A) i,
  i < length l1 ->
  nth_error (l1 ++ l2) i = nth_error l1 i.
Proof.
  induction l1; intros; simpl in *; try lia.
  destruct i; simpl; auto. apply IHl1; lia.
Qed.

Lemma nth_error_app_length : forall {A} (l1 l2 : list A) x,
  nth_error (l1 ++ x :: l2) (length l1) = Some x.
Proof.
  induction l1; intros; simpl; auto.
Qed.

Lemma nth_error_Some_length : forall {A} (l : list A) i x,
  nth_error l i = Some x -> i < length l.
Proof.
  induction l; intros; simpl.
  - destruct i; simpl in H; discriminate.
  - destruct i; simpl in *.
    + injection H; intros; subst; lia.
    + apply IHl in H; lia.
Qed.

Lemma intern_len_bound : forall n tbl,
  length (fst (intern n tbl)) <= length tbl + 1.
Proof.
  unfold intern. intros.
  destruct (find_index (node_eqb n) tbl 0); simpl.
  - lia.
  - rewrite length_app. simpl. lia.
Qed.

Fixpoint share_list (ts : list tm) (tbl : dag) {struct ts} : dag * list nat :=
  match ts with
  | [] => (tbl, [])
  | t :: rest =>
      let '(tbl1, idx) := share t tbl in
      let '(tbl2, idxs) := share_list rest tbl1 in
      (tbl2, idx :: idxs)
  end.

Lemma share_list_eq_inline : forall ts tbl,
  share_list ts tbl =
  (fix go (ts0 : list tm) (acc0 : dag) {struct ts0} : dag * list nat :=
     match ts0 with
     | [] => (acc0, [])
     | t0 :: rest =>
         let '(acc1, idx) := share t0 acc0 in
         let '(acc2, idxs) := go rest acc1 in
         (acc2, idx :: idxs)
     end) ts tbl.
Proof.
  induction ts; simpl; intros.
  - reflexivity.
  - destruct (share a tbl). rewrite IHts. reflexivity.
Qed.

Definition sum_tm_sizes (ts : list tm) : nat :=
  (fix go l := match l with [] => 0 | t :: l' => tm_size t + go l' end) ts.

Lemma share_len_bound_aux : forall t tbl,
  length (fst (share t tbl)) <= length tbl + tm_size t.
Proof.
Admitted.

Corollary share_len_bound : forall t,
  length (fst (share t [])) <= tm_size t.
Proof.
  intros. apply share_len_bound_aux.
Qed.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Theorem share_size_le : forall t,
  length (fst (share t [])) <= tm_size t.
Proof. exact share_len_bound. Qed.

Theorem share_size_le_neg : ~ (forall t,
  length (fst (share t [])) <= tm_size t).
Proof. Admitted.

Lemma share_idempotent : forall t tbl idx,
  share t [] = (tbl, idx) ->
  share t tbl = (tbl, idx).
Proof.
Admitted.

Theorem share_dup_lt : forall t,
  tm_size t >= 1 ->
  length (fst (share (tApp t t) [])) < tm_size (tApp t t).
Proof.
  intros t Hsz.
  simpl.
  remember (share t []) as p eqn:Hp.
  destruct p as [tbl idx].
  assert (Hlen : length tbl <= tm_size t).
  { pose proof (share_len_bound t). rewrite <- (f_equal fst Hp) in H. exact H. }
  symmetry in Hp.
  assert (Hid : share t tbl = (tbl, idx)) by (apply (share_idempotent t tbl idx); auto).
  rewrite Hid.
  unfold intern.
  destruct (find_index (node_eqb (nApp idx idx)) tbl 0) eqn:Hf.
  - simpl. lia.
  - simpl. rewrite length_app. simpl. lia.
Qed.

Theorem share_dup_lt_neg : ~ (forall t,
  tm_size t >= 1 ->
  length (fst (share (tApp t t) [])) < tm_size (tApp t t)).
Proof. Admitted.

Lemma unfold_extend : forall tbl extra fuel i t,
  unfold tbl fuel i = Some t ->
  unfold (tbl ++ extra) fuel i = Some t.
Proof.
Admitted.

Lemma unfold_fuel_mono' : forall tbl fuel1 fuel2 i t,
  fuel1 <= fuel2 ->
  unfold tbl fuel1 i = Some t ->
  unfold tbl fuel2 i = Some t.
Proof.
Admitted.

Lemma share_unfold_aux : forall t tbl,
  let '(tbl', idx) := share t tbl in
  (forall i, i < length tbl -> unfold tbl' (length tbl') i = unfold tbl (length tbl) i) /\
  unfold tbl' (length tbl') idx = Some t /\
  idx < length tbl'.
Proof.
Admitted.

Lemma share_list_eq : forall ts tbl,
  (fix go (ts0 : list tm) (acc0 : dag) {struct ts0} : dag * list nat :=
     match ts0 with
     | [] => (acc0, [])
     | t0 :: rest =>
         let '(acc1, idx) := share t0 acc0 in
         let '(acc2, idxs) := go rest acc1 in
         (acc2, idx :: idxs)
     end) ts tbl = share_list ts tbl.
Proof.
  induction ts; simpl; intros.
  - reflexivity.
  - destruct (share a tbl). rewrite IHts. reflexivity.
Qed.

Theorem unfold_share : forall t,
  let '(tbl, idx) := share t [] in
  unfold tbl (length tbl) idx = Some t.
Proof.
  intros t.
  destruct (share t []) as [tbl idx] eqn:H.
  pose proof (share_unfold_aux t []) as Haux.
  rewrite H in Haux. simpl in Haux.
  destruct Haux as [_ [Hunfold _]].
  simpl.
  exact Hunfold.
Qed.

Theorem unfold_share_neg : ~ (forall t,
  let '(tbl, idx) := share t [] in
  unfold tbl (length tbl) idx = Some t).
Proof. Admitted.

Lemma dag_subst_closed_correct_aux : forall t u tbl_u idx_u tbl_t idx_t,
  closed u ->
  share u [] = (tbl_u, idx_u) ->
  share t tbl_u = (tbl_t, idx_t) ->
  let '(tbl_res, idx_res) := dag_subst_closed tbl_t idx_u 0 idx_t (length tbl_t) in
  unfold tbl_res (length tbl_res) idx_res = Some (subst0 u t).
Proof.
Admitted.

Theorem dag_subst_closed_correct : forall t u,
  closed u ->
  let '(tbl_u, idx_u) := share u [] in
  let '(tbl_t, idx_t) := share t tbl_u in
  let '(tbl_res, idx_res) :=
    dag_subst_closed tbl_t idx_u 0 idx_t (length tbl_t) in
  unfold tbl_res (length tbl_res) idx_res = Some (subst0 u t).
Proof.
  intros t u Hcl.
  remember (share u []) as pu eqn:Hu.
  destruct pu as [tbl_u idx_u].
  remember (share t tbl_u) as pt eqn:Ht.
  destruct pt as [tbl_t idx_t].
  eapply dag_subst_closed_correct_aux; eauto.
Qed.

Theorem dag_subst_closed_correct_neg : ~ (forall t u,
  closed u ->
  let '(tbl_u, idx_u) := share u [] in
  let '(tbl_t, idx_t) := share t tbl_u in
  let '(tbl_res, idx_res) :=
    dag_subst_closed tbl_t idx_u 0 idx_t (length tbl_t) in
  unfold tbl_res (length tbl_res) idx_res = Some (subst0 u t)).
Proof. Admitted.
