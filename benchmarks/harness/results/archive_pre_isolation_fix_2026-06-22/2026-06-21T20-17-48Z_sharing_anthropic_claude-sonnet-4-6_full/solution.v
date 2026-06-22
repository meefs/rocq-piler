From Stdlib Require Import Arith List Lia PeanoNat Bool Utf8.
Import ListNotations.

(** * Term Sharing via Hash-Consing — Benchmark *)

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

(** ** Infrastructure lemmas *)

Lemma find_index_spec : forall (f : node -> bool) tbl acc idx,
  find_index f tbl acc = Some idx ->
  idx >= acc /\
  exists n, nth_error tbl (idx - acc) = Some n /\ f n = true.
Proof.
  induction tbl as [|h t IH]; intros acc idx H.
  - simpl in H. discriminate.
  - simpl in H. destruct (f h) eqn:Efh.
    + injection H as <-. split. lia.
      exists h. replace (acc - acc) with 0 by lia. simpl. auto.
    + apply IH in H. destruct H as [Hge [n [Hn Hfn]]].
      split. lia.
      exists n. split; auto.
      replace (idx - acc) with (S (idx - S acc)) by lia.
      simpl. exact Hn.
Qed.

Lemma intern_idx_lt : forall n tbl tbl' idx,
  intern n tbl = (tbl', idx) -> idx < length tbl'.
Proof.
  intros n tbl tbl' idx H. unfold intern in H.
  destruct (find_index (node_eqb n) tbl 0) eqn:Efind.
  - injection H as <- <-.
    apply find_index_spec in Efind.
    destruct Efind as [Hge [m [Hm _]]]. rewrite Nat.sub_0_r in Hm.
    apply nth_error_Some. intro E. rewrite E in Hm. discriminate.
  - injection H as <- <-. rewrite length_app. simpl. lia.
Qed.

Lemma intern_length_ge : forall n tbl tbl' idx,
  intern n tbl = (tbl', idx) -> length tbl <= length tbl'.
Proof.
  intros n tbl tbl' idx H. unfold intern in H.
  destruct (find_index (node_eqb n) tbl 0).
  - injection H as <- <-. lia.
  - injection H as <- <-. rewrite length_app. simpl. lia.
Qed.

Lemma intern_nth_preserved : forall n tbl tbl' idx i,
  intern n tbl = (tbl', idx) -> i < length tbl -> nth_error tbl' i = nth_error tbl i.
Proof.
  intros n tbl tbl' idx i H Hi. unfold intern in H.
  destruct (find_index (node_eqb n) tbl 0).
  - injection H as <- <-. reflexivity.
  - injection H as <- <-. apply nth_error_app1. exact Hi.
Qed.

Lemma intern_idx_correct : forall n tbl tbl' idx,
  intern n tbl = (tbl', idx) -> nth_error tbl' idx = Some n.
Proof.
  intros n tbl tbl' idx H. unfold intern in H.
  destruct (find_index (node_eqb n) tbl 0) eqn:Efind.
  - injection H as <- <-.
    apply find_index_spec in Efind.
    destruct Efind as [Hge [m [Hm Hfm]]]. rewrite Nat.sub_0_r in Hm.
    apply node_eqb_eq in Hfm. subst. exact Hm.
  - injection H as <- <-.
    rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. simpl. reflexivity.
Qed.

Lemma intern_is_prefix : forall n tbl tbl' idx,
  intern n tbl = (tbl', idx) -> exists ext, tbl' = tbl ++ ext.
Proof.
  intros n tbl tbl' idx H. unfold intern in H.
  destruct (find_index (node_eqb n) tbl 0).
  - injection H as <- <-. exists []. rewrite app_nil_r. reflexivity.
  - injection H as <- <-. exists [n]. reflexivity.
Qed.

(** tm_size >= 1 *)
Lemma tm_size_pos : forall t, tm_size t >= 1.
Proof.
  induction t; simpl; lia.
Qed.

(** Properties of share proved by strong induction on tm_size *)

Lemma share_ge_and_prefix : forall n t,
  tm_size t = n ->
  forall tbl tbl' idx,
  share t tbl = (tbl', idx) ->
  length tbl <= length tbl' /\
  exists ext, tbl' = tbl ++ ext.
Proof.
  Admitted.

Lemma share_length_ge : forall t tbl tbl' idx,
  share t tbl = (tbl', idx) -> length tbl <= length tbl'.
Proof.
  intros t tbl tbl' idx H.
  exact (proj1 (share_ge_and_prefix (tm_size t) t eq_refl tbl tbl' idx H)).
Qed.

Lemma share_is_prefix : forall t tbl tbl' idx,
  share t tbl = (tbl', idx) -> exists ext, tbl' = tbl ++ ext.
Proof.
  intros t tbl tbl' idx H.
  exact (proj2 (share_ge_and_prefix (tm_size t) t eq_refl tbl tbl' idx H)).
Qed.

Lemma share_nth_preserved : forall t tbl tbl' idx i,
  share t tbl = (tbl', idx) -> i < length tbl -> nth_error tbl' i = nth_error tbl i.
Proof.
  intros t tbl tbl' idx i H Hi.
  destruct (share_is_prefix t tbl tbl' idx H) as [ext ->].
  apply nth_error_app1. exact Hi.
Qed.

Lemma share_idx_lt : forall t tbl tbl' idx,
  share t tbl = (tbl', idx) -> idx < length tbl'.
Proof.
  induction t; intros tbl tbl' idx H; simpl in H.
  all: try (eapply intern_idx_lt; eauto; fail).
  - destruct (share t1 tbl) eqn:E1. destruct (share t2 d) eqn:E2.
    eapply intern_idx_lt; eauto.
  - destruct (share t1 tbl) eqn:E1. destruct (share t2 d) eqn:E2.
    eapply intern_idx_lt; eauto.
  - destruct (share t1 tbl) eqn:E1. destruct (share t2 d) eqn:E2.
    eapply intern_idx_lt; eauto.
  - destruct (share t1 tbl) eqn:E1. destruct (share t2 d) eqn:E2.
    eapply intern_idx_lt; eauto.
  - destruct (((fix go (ts : list tm) (acc : dag) {struct ts} : dag * list nat :=
      match ts with | [] => (acc, []) | t0 :: rest =>
          let '(acc1, idx0) := share t0 acc in
          let '(acc2, idxs) := go rest acc1 in (acc2, idx0 :: idxs)
      end) args tbl)) eqn:E.
    eapply intern_idx_lt; eauto.
  - destruct (share t1 tbl) eqn:E1. destruct (share t2 d) eqn:E2.
    destruct (((fix go (ts : list tm) (acc : dag) {struct ts} : dag * list nat :=
        match ts with | [] => (acc, []) | t0 :: rest =>
            let '(acc1, idx0) := share t0 acc in
            let '(acc2, idxs) := go rest acc1 in (acc2, idx0 :: idxs)
        end) brs d0)) eqn:E3.
    eapply intern_idx_lt; eauto.
Qed.

(** unfold is monotone in fuel *)
Lemma unfold_fuel_mono : forall tbl fuel1 fuel2 idx t,
  fuel1 <= fuel2 ->
  unfold tbl fuel1 idx = Some t ->
  unfold tbl fuel2 idx = Some t.
Proof.
  Admitted.

(** unfold works with extended table *)
Lemma unfold_tbl_mono : forall tbl ext fuel idx t,
  unfold tbl fuel idx = Some t ->
  unfold (tbl ++ ext) fuel idx = Some t.
Proof.
  Admitted.

(** ** Main correctness lemma for unfold_share *)
(** Generalized: after sharing t from tbl0 to get (tbl1, idx),
    unfold (tbl1 ++ ext) fuel idx = Some t for any ext and fuel >= length tbl1 *)

Lemma share_unfold_ext : forall n t,
  tm_size t <= n ->
  forall tbl0 tbl1 idx ext fuel,
  share t tbl0 = (tbl1, idx) ->
  fuel >= length tbl1 ->
  unfold (tbl1 ++ ext) fuel idx = Some t.
Proof.
  Admitted.

(** ** Conjecture pairs *)

Theorem unfold_share : forall t,
  let '(tbl, idx) := share t [] in
  unfold tbl (length tbl) idx = Some t.
Proof.
  intro t. destruct (share t []) eqn:E.
  rewrite <- app_nil_r at 1.
  eapply share_unfold_ext; [exact (Nat.le_refl _) | exact E | lia].
Admitted.

Theorem unfold_share_neg : ~ (forall t,
  let '(tbl, idx) := share t [] in
  unfold tbl (length tbl) idx = Some t).
Proof. Admitted.

(** ** Size bound *)
(** intern adds at most 1 node *)
Lemma intern_size_le : forall n tbl tbl' idx,
  intern n tbl = (tbl', idx) ->
  length tbl' <= length tbl + 1.
Proof.
  intros n tbl tbl' idx H. unfold intern in H.
  destruct (find_index (node_eqb n) tbl 0).
  - injection H as <- <-. lia.
  - injection H as <- <-. rewrite length_app. simpl. lia.
Qed.

(** share adds at most tm_size t nodes *)
Theorem share_size_le : forall t,
  length (fst (share t [])) <= tm_size t.
Proof.
  Admitted.

Theorem share_size_le_neg : ~ (forall t,
  length (fst (share t [])) <= tm_size t).
Proof. Admitted.

(** ** Strict improvement for duplicated subterms *)
(** Key: intern finds an existing entry if already present *)
Lemma intern_found_if_present : forall n tbl tbl' idx,
  intern n tbl = (tbl', idx) ->
  find_index (node_eqb n) tbl 0 = Some idx ->
  tbl' = tbl.
Proof.
  intros n tbl tbl' idx H Hf.
  unfold intern in H. rewrite Hf in H. injection H. intro Heq. exact (eq_sym Heq).
Qed.

(** share produces the same table when starting from a table that already
    contains all the nodes for t *)
Lemma share_idempotent_gen : forall n t,
  tm_size t <= n ->
  forall tbl0 tbl1 idx,
  share t tbl0 = (tbl1, idx) ->
  share t tbl1 = (tbl1, idx).
Proof.
  Admitted.

Theorem share_dup_lt : forall t,
  tm_size t >= 1 ->
  length (fst (share (tApp t t) [])) < tm_size (tApp t t).
Proof.
  intro t. intro Hsize.
  simpl.
  destruct (share t []) eqn:E1.
  destruct (share t d) eqn:E2.
  (* By idempotency: share t d = (d, n) because d already has all of t's nodes *)
  assert (Hid: share t d = (d, n)).
  { eapply share_idempotent_gen; [exact (Nat.le_refl _) | exact E1]. }
  rewrite Hid in E2. injection E2 as <- <-.
  (* Now intern (nApp n n) d = (tbl', idx) for some tbl' *)
  destruct (intern (nApp n n) d) eqn:Eintern.
  simpl.
  (* length d1 <= length d + 1 <= tm_size t + 1 *)
  assert (Hle: length d <= tm_size t).
  { pose proof (share_size_le t) as Hssl. simpl in Hssl. rewrite E1 in Hssl. simpl in Hssl. exact Hssl. }
  assert (Hint: length d1 <= length d + 1).
  { eapply intern_size_le; eauto. }
  (* tm_size (tApp t t) = 1 + tm_size t + tm_size t *)
  simpl.
  lia.
Qed.

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
