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

(** ** Infrastructure lemmas *)

Lemma find_index_bound : forall f tbl acc i,
  find_index f tbl acc = Some i -> acc <= i < acc + length tbl.
Proof.
  intros f tbl. induction tbl as [|n tbl IH]; intros acc i Hf.
  - simpl in Hf. discriminate.
  - simpl in Hf. destruct (f n).
    + injection Hf; intros; subst. simpl. lia.
    + apply IH in Hf. simpl. lia.
Qed.

Lemma find_index_nth : forall f tbl acc i,
  find_index f tbl acc = Some i ->
  exists nd, nth_error tbl (i - acc) = Some nd /\ f nd = true.
Proof.
  intros f tbl. induction tbl as [|n tbl IH]; intros acc i Hf.
  - simpl in Hf. discriminate.
  - simpl in Hf. destruct (f n) eqn:Hfn.
    + injection Hf; intros; subst. simpl. replace (i - i) with 0 by lia.
      simpl. eauto.
    + apply find_index_bound in Hf as Hbound.
      apply IH in Hf. destruct Hf as [nd [Hnd Hfnd]].
      exists nd. split.
      * replace (i - acc) with (S (i - S acc)) by lia.
        simpl. exact Hnd.
      * exact Hfnd.
Qed.

Lemma nth_error_app_left : forall {A} (l1 l2 : list A) i,
  i < length l1 -> nth_error (l1 ++ l2) i = nth_error l1 i.
Proof.
  intros A l1. induction l1 as [|h t IH]; intros l2 i Hi.
  - simpl in Hi. lia.
  - destruct i; simpl.
    + reflexivity.
    + apply IH. simpl in Hi. lia.
Qed.

Lemma nth_error_length : forall {A} (l : list A) i x,
  nth_error l i = Some x -> i < length l.
Proof.
  intros A l. induction l as [|h t IH]; intros i x Hn.
  - simpl in Hn. destruct i; discriminate.
  - destruct i; simpl in *.
    + lia.
    + apply IH in Hn. lia.
Qed.

(** intern properties *)

Lemma intern_prefix : forall n tbl tbl' idx,
  intern n tbl = (tbl', idx) ->
  exists ext, tbl' = tbl ++ ext.
Proof.
  intros n tbl tbl' idx Hint.
  unfold intern in Hint.
  destruct (find_index (node_eqb n) tbl 0) eqn:Hf.
  - injection Hint; intros; subst. exists []. rewrite app_nil_r. reflexivity.
  - injection Hint; intros; subst. exists [n]. reflexivity.
Qed.

Lemma intern_tbl_mono : forall n tbl tbl' idx,
  intern n tbl = (tbl', idx) -> length tbl <= length tbl'.
Proof.
  intros n tbl tbl' idx Hint.
  apply intern_prefix in Hint as [ext Hext].
  subst. rewrite length_app. lia.
Qed.

Lemma intern_idx_valid : forall n tbl tbl' idx,
  intern n tbl = (tbl', idx) -> idx < length tbl'.
Proof.
  intros n tbl tbl' idx Hint.
  unfold intern in Hint.
  destruct (find_index (node_eqb n) tbl 0) eqn:Hf.
  - injection Hint; intros; subst.
    apply find_index_bound in Hf. lia.
  - injection Hint; intros; subst.
    rewrite length_app. simpl. lia.
Qed.

Lemma intern_nth : forall n tbl tbl' idx,
  intern n tbl = (tbl', idx) -> nth_error tbl' idx = Some n.
Proof.
  intros n tbl tbl' idx Hint.
  unfold intern in Hint.
  destruct (find_index (node_eqb n) tbl 0) eqn:Hf.
  - injection Hint; intros; subst.
    apply find_index_nth in Hf as [nd [Hnd Hfnd]].
    replace (idx - 0) with idx in Hnd by lia.
    apply node_eqb_eq in Hfnd. subst. exact Hnd.
  - injection Hint; intros; subst.
    rewrite nth_error_app2 by lia.
    replace (length tbl - length tbl) with 0 by lia.
    simpl. reflexivity.
Qed.

Lemma intern_old_preserved : forall n tbl tbl' idx i nd,
  intern n tbl = (tbl', idx) ->
  i < length tbl ->
  nth_error tbl i = Some nd ->
  nth_error tbl' i = Some nd.
Proof.
  intros n tbl tbl' idx i nd Hint Hi Hnd.
  apply intern_prefix in Hint as [ext Hext].
  subst. rewrite nth_error_app_left by exact Hi. exact Hnd.
Qed.

(** share properties *)

(* Combined lemma: share/share_list prefix property, proved by size induction *)
Lemma share_prefix_gen : forall n t,
  tm_size t <= n ->
  forall tbl tbl' idx, share t tbl = (tbl', idx) -> exists ext, tbl' = tbl ++ ext.
Proof.
  induction n as [|n IHn]; intros t Hn.
  - destruct t; simpl in Hn; lia.
  - intros tbl tbl' idx Hs.
    destruct t; simpl in Hs.
    + apply intern_prefix in Hs. exact Hs.
    + apply intern_prefix in Hs. exact Hs.
    + destruct (share t1 tbl) as [tbl1 a] eqn:H1.
      destruct (share t2 tbl1) as [tbl2 b] eqn:H2.
      simpl in Hn.
      assert (exists e1, tbl1 = tbl ++ e1) as [e1 He1].
      { refine (IHn t1 _ tbl tbl1 a H1). lia. }
      assert (exists e2, tbl2 = tbl1 ++ e2) as [e2 He2].
      { refine (IHn t2 _ tbl1 tbl2 b H2). lia. }
      apply intern_prefix in Hs as [e3 He3].
      subst. exists (e1 ++ e2 ++ e3). repeat rewrite <- app_assoc. reflexivity.
    + destruct (share t1 tbl) as [tbl1 a] eqn:H1.
      destruct (share t2 tbl1) as [tbl2 b] eqn:H2.
      simpl in Hn.
      assert (exists e1, tbl1 = tbl ++ e1) as [e1 He1].
      { refine (IHn t1 _ tbl tbl1 a H1). lia. }
      assert (exists e2, tbl2 = tbl1 ++ e2) as [e2 He2].
      { refine (IHn t2 _ tbl1 tbl2 b H2). lia. }
      apply intern_prefix in Hs as [e3 He3].
      subst. exists (e1 ++ e2 ++ e3). repeat rewrite <- app_assoc. reflexivity.
    + destruct (share t1 tbl) as [tbl1 a] eqn:H1.
      destruct (share t2 tbl1) as [tbl2 b] eqn:H2.
      simpl in Hn.
      assert (exists e1, tbl1 = tbl ++ e1) as [e1 He1].
      { refine (IHn t1 _ tbl tbl1 a H1). lia. }
      assert (exists e2, tbl2 = tbl1 ++ e2) as [e2 He2].
      { refine (IHn t2 _ tbl1 tbl2 b H2). lia. }
      apply intern_prefix in Hs as [e3 He3].
      subst. exists (e1 ++ e2 ++ e3). repeat rewrite <- app_assoc. reflexivity.
    + destruct (share t1 tbl) as [tbl1 a] eqn:H1.
      destruct (share t2 tbl1) as [tbl2 b] eqn:H2.
      simpl in Hn.
      assert (exists e1, tbl1 = tbl ++ e1) as [e1 He1].
      { refine (IHn t1 _ tbl tbl1 a H1). lia. }
      assert (exists e2, tbl2 = tbl1 ++ e2) as [e2 He2].
      { refine (IHn t2 _ tbl1 tbl2 b H2). lia. }
      apply intern_prefix in Hs as [e3 He3].
      subst. exists (e1 ++ e2 ++ e3). repeat rewrite <- app_assoc. reflexivity.
    + apply intern_prefix in Hs. exact Hs.
    + (* tRoll I c args *)
      destruct ((fix go (ts : list tm) (acc : dag) {struct ts} : dag * list nat :=
                  match ts with | [] => (acc, []) | t0 :: rest =>
                      let '(acc1, idx0) := share t0 acc in
                      let '(acc2, idxs) := go rest acc1 in (acc2, idx0 :: idxs)
                  end) args tbl) as [tbl1 idxs] eqn:Hargs.
      apply intern_prefix in Hs as [e He].
      assert (exists ea, tbl1 = tbl ++ ea) as [ea Hea].
      { (* Prove by induction on args *)
        simpl in Hn.
        clear He.
        revert tbl tbl1 idxs Hargs.
        induction args as [|a args IHa]; intros tbl tbl1 idxs Hargs; simpl in Hargs.
        - injection Hargs; intros; subst. exists []. rewrite app_nil_r. reflexivity.
        - destruct (share a tbl) as [tbl_a idx_a] eqn:Ha.
          destruct ((fix go (ts : list tm) (acc : dag) {struct ts} : dag * list nat :=
            match ts with | [] => (acc, []) | t0 :: rest =>
                let '(acc1, idx0) := share t0 acc in
                let '(acc2, idxs) := go rest acc1 in (acc2, idx0 :: idxs)
            end) args tbl_a) as [tbl2 idxs2] eqn:Hrest.
          injection Hargs; intros; subst.
          assert (tm_size a <= n) as Ha_size.
          { (* tm_size a <= tm_size (tRoll I c (a :: args)) - 1 <= n *)
            simpl in Hn.
            assert (Hge : (fix go l := match l with [] => 0 | t0 :: l' => tm_size t0 + go l' end) (a :: args) >= tm_size a).
            { simpl. lia. }
            lia. }
          assert (exists e1, tbl_a = tbl ++ e1) as [e1 He1].
          { refine (IHn a Ha_size tbl tbl_a idx_a Ha). }
          assert (forall b, In b args -> tm_size b <= n) as IHargs_size.
          { intros b Hb. simpl in Hn.
            assert ((fix go l := match l with [] => 0 | t0 :: l' => tm_size t0 + go l' end) args >= tm_size b).
            { clear Ha He1 e1 Ha_size Hargs IHa IHn tbl_a idx_a tbl1 idxs2 Hrest.
              induction args as [|h args IHargs']; simpl in Hb |- *.
              - contradiction.
              - destruct Hb as [-> | Hb]. lia.
                assert (S (tm_size a + (fix go (l : list tm) : nat := match l with | [] => 0 | t0 :: l' => tm_size t0 + go l' end) args) ≤ S n) as Harg by lia.
                specialize (IHargs' Harg Hb). lia. }
            lia. }
          assert (IHa' : exists e2, tbl1 = tbl_a ++ e2).
          { refine (IHa _ tbl_a tbl1 idxs2 Hrest). lia. }
          destruct IHa' as [e2 He2].
          exists (e1 ++ e2). subst. rewrite <- app_assoc. reflexivity. }
      subst. exists (ea ++ e). rewrite <- app_assoc. reflexivity.
    + (* tCase I t1 t2 brs *)
      destruct (share t1 tbl) as [tbl1 si] eqn:H1.
      destruct (share t2 tbl1) as [tbl2 ci] eqn:H2.
      destruct ((fix go (ts : list tm) (acc : dag) {struct ts} : dag * list nat :=
                  match ts with | [] => (acc, []) | t0 :: rest =>
                      let '(acc1, idx0) := share t0 acc in
                      let '(acc2, idxs) := go rest acc1 in (acc2, idx0 :: idxs)
                  end) brs tbl2) as [tbl3 bis] eqn:Hbrs.
      simpl in Hn.
      assert (exists e1, tbl1 = tbl ++ e1) as [e1 He1].
      { refine (IHn t1 _ tbl tbl1 si H1). lia. }
      assert (exists e2, tbl2 = tbl1 ++ e2) as [e2 He2].
      { refine (IHn t2 _ tbl1 tbl2 ci H2). lia. }
      assert (exists e3, tbl3 = tbl2 ++ e3) as [e3 He3].
      { clear H1 H2 He1 He2 Hs.
        revert tbl2 tbl3 bis Hbrs.
        induction brs as [|b brs IHb]; intros tbl2 tbl3 bis Hbrs; simpl in Hbrs.
        - injection Hbrs; intros; subst. exists []. rewrite app_nil_r. reflexivity.
        - destruct (share b tbl2) as [tbl_b idx_b] eqn:Hb.
          destruct ((fix go (ts : list tm) (acc : dag) {struct ts} : dag * list nat :=
            match ts with | [] => (acc, []) | t0 :: rest =>
                let '(acc1, idx0) := share t0 acc in
                let '(acc2, idxs) := go rest acc1 in (acc2, idx0 :: idxs)
            end) brs tbl_b) as [tbl4 idxs4] eqn:Hrest.
          injection Hbrs; intros; subst.
          assert (tm_size b <= n) as Hb_size.
          { assert ((fix go l := match l with [] => 0 | t0 :: l' => tm_size t0 + go l' end) (b :: brs) >= tm_size b).
            { simpl. lia. }
            lia. }
          assert (exists eb, tbl_b = tbl2 ++ eb) as [eb Heb].
          { refine (IHn b Hb_size tbl2 tbl_b idx_b Hb). }
          assert (forall c, In c brs -> tm_size c <= n) as IHbrs_size.
          { intros c Hc.
            assert ((fix go l := match l with [] => 0 | t0 :: l' => tm_size t0 + go l' end) brs >= tm_size c).
            { clear Hb Heb eb Hb_size Hbrs IHb IHn tbl_b idx_b tbl3 idxs4 Hrest.
              induction brs as [|h brs IHbrs']; simpl in Hc |- *.
              - contradiction.
              - destruct Hc as [-> | Hc]. lia.
                assert (S (tm_size t1 + tm_size t2 + (tm_size b + (fix go (l : list tm) : nat := match l with | [] => 0 | t0 :: l' => tm_size t0 + go l' end) brs)) ≤ S n) as Harg by lia.
                specialize (IHbrs' Harg Hc). lia. }
            lia. }
          assert (IHb' : exists er, tbl3 = tbl_b ++ er).
          { refine (IHb _ tbl_b tbl3 idxs4 Hrest). lia. }
          destruct IHb' as [er Her].
          exists (eb ++ er). subst. rewrite <- app_assoc. reflexivity. }
      apply intern_prefix in Hs as [e4 He4].
      subst. exists (e1 ++ e2 ++ e3 ++ e4). repeat rewrite <- app_assoc. reflexivity.
Qed.

(* share only extends the table *)
Lemma share_prefix : forall t tbl tbl' idx,
  share t tbl = (tbl', idx) ->
  exists ext, tbl' = tbl ++ ext.
Proof.
  intros t tbl tbl' idx Hs.
  apply (share_prefix_gen (tm_size t) t (Nat.le_refl _) tbl tbl' idx Hs).
Qed.

Lemma share_go_prefix : forall ts tbl tbl' idxs,
  (fix go (ts0 : list tm) (acc : dag) {struct ts0} : dag * list nat :=
    match ts0 with
    | [] => (acc, [])
    | t0 :: rest =>
        let '(acc1, idx0) := share t0 acc in
        let '(acc2, idxs0) := go rest acc1 in
        (acc2, idx0 :: idxs0)
    end) ts tbl = (tbl', idxs) ->
  exists ext, tbl' = tbl ++ ext.
Proof.
  induction ts as [|t ts IH]; intros tbl tbl' idxs Hgo; simpl in Hgo.
  - injection Hgo; intros; subst. exists []. rewrite app_nil_r. reflexivity.
  - destruct (share t tbl) as [tbl1 idx1] eqn:Ht.
    destruct ((fix go (ts0 : list tm) (acc : dag) {struct ts0} : dag * list nat :=
      match ts0 with | [] => (acc, []) | t0 :: rest =>
          let '(acc1, idx0) := share t0 acc in
          let '(acc2, idxs0) := go rest acc1 in (acc2, idx0 :: idxs0)
      end) ts tbl1) as [tbl2 idxs2] eqn:Hrest.
    injection Hgo; intros; subst.
    apply share_prefix in Ht as [e1 He1].
    apply IH in Hrest as [e2 He2].
    exists (e1 ++ e2). subst. rewrite <- app_assoc. reflexivity.
Qed.

Lemma share_tbl_mono : forall t tbl tbl' idx,
  share t tbl = (tbl', idx) -> length tbl <= length tbl'.
Proof.
  intros t tbl tbl' idx Hs.
  apply share_prefix in Hs as [ext Hext].
  subst. rewrite length_app. lia.
Qed.

Lemma share_idx_valid : forall t tbl tbl' idx,
  share t tbl = (tbl', idx) -> idx < length tbl'.
Proof.
  induction t using tm_ind; intros tbl tbl' idx Hs; simpl in Hs.
  - apply intern_idx_valid in Hs. exact Hs.
  - apply intern_idx_valid in Hs. exact Hs.
  - destruct (share t1 tbl) as [tbl1 a] eqn:H1.
    destruct (share t2 tbl1) as [tbl2 b] eqn:H2.
    apply intern_idx_valid in Hs. exact Hs.
  - destruct (share t1 tbl) as [tbl1 a] eqn:H1.
    destruct (share t2 tbl1) as [tbl2 b] eqn:H2.
    apply intern_idx_valid in Hs. exact Hs.
  - destruct (share t1 tbl) as [tbl1 a] eqn:H1.
    destruct (share t2 tbl1) as [tbl2 b] eqn:H2.
    apply intern_idx_valid in Hs. exact Hs.
  - destruct (share t1 tbl) as [tbl1 a] eqn:H1.
    destruct (share t2 tbl1) as [tbl2 b] eqn:H2.
    apply intern_idx_valid in Hs. exact Hs.
  - apply intern_idx_valid in Hs. exact Hs.
  - destruct ((fix go (ts : list tm) (acc : dag) {struct ts} : dag * list nat :=
                match ts with | [] => (acc, []) | t0 :: rest =>
                    let '(acc1, idx0) := share t0 acc in
                    let '(acc2, idxs) := go rest acc1 in (acc2, idx0 :: idxs)
                end) args tbl) as [tbl1 idxs] eqn:Hargs.
    apply intern_idx_valid in Hs. exact Hs.
  - destruct (share t1 tbl) as [tbl1 si] eqn:H1.
    destruct (share t2 tbl1) as [tbl2 ci] eqn:H2.
    destruct ((fix go (ts : list tm) (acc : dag) {struct ts} : dag * list nat :=
                match ts with | [] => (acc, []) | t0 :: rest =>
                    let '(acc1, idx0) := share t0 acc in
                    let '(acc2, idxs) := go rest acc1 in (acc2, idx0 :: idxs)
                end) brs tbl2) as [tbl3 bis] eqn:Hbrs.
    apply intern_idx_valid in Hs. exact Hs.
Qed.

(** unfold monotonicity *)

(* Helper: list unfold is monotone in fuel, assuming index unfold is *)
Lemma unfold_list_mono_given : forall tbl fuel1 fuel2,
  (forall idx t, unfold tbl fuel1 idx = Some t -> unfold tbl fuel2 idx = Some t) ->
  forall (l : list nat) ts,
    (fix go l' := match l' with [] => Some [] | i :: r =>
       match unfold tbl fuel1 i, go r with Some t0, Some ts0 => Some (t0 :: ts0) | _,_ => None end end) l = Some ts ->
    (fix go l' := match l' with [] => Some [] | i :: r =>
       match unfold tbl fuel2 i, go r with Some t0, Some ts0 => Some (t0 :: ts0) | _,_ => None end end) l = Some ts.
Proof.
  intros tbl fuel1 fuel2 Hmono l.
  induction l as [|i l IH]; intros ts Hunf; simpl in Hunf |- *.
  - exact Hunf.
  - destruct (unfold tbl fuel1 i) eqn:Hi; [|discriminate].
    destruct ((fix go l' := match l' with [] => Some [] | i0 :: r0 =>
       match unfold tbl fuel1 i0, go r0 with Some t0, Some ts0 => Some (t0 :: ts0) | _,_ => None end end) l) eqn:Hr;
    [|discriminate].
    injection Hunf; intros; subst.
    rewrite (Hmono i _ Hi). rewrite (IH l0 eq_refl). reflexivity.
Qed.

(* unfold is monotone in fuel *)
Lemma unfold_fuel_mono : forall tbl fuel1 fuel2 idx t,
  fuel1 <= fuel2 ->
  unfold tbl fuel1 idx = Some t ->
  unfold tbl fuel2 idx = Some t.
Proof.
  intros tbl fuel1. revert tbl.
  induction fuel1 as [|fuel1' IH]; intros tbl fuel2 idx t Hle Hunf.
  - simpl in Hunf. discriminate.
  - destruct fuel2 as [|fuel2'].
    + lia.
    + simpl in Hunf. simpl.
      destruct (nth_error tbl idx) as [nd|] eqn:Hn; [|discriminate].
      destruct nd; try exact Hunf.
      * (* nPi *)
        destruct (unfold tbl fuel1' a) eqn:Ha; [|discriminate].
        destruct (unfold tbl fuel1' b) eqn:Hb; [|discriminate].
        injection Hunf; intros; subst.
        rewrite (IH tbl fuel2' a t0 (ltac:(lia)) Ha).
        rewrite (IH tbl fuel2' b t1 (ltac:(lia)) Hb).
        reflexivity.
      * (* nLam *)
        destruct (unfold tbl fuel1' a) eqn:Ha; [|discriminate].
        destruct (unfold tbl fuel1' t0) eqn:Ht; [|discriminate].
        injection Hunf; intros; subst.
        rewrite (IH tbl fuel2' a t1 (ltac:(lia)) Ha).
        rewrite (IH tbl fuel2' t0 t2 (ltac:(lia)) Ht).
        reflexivity.
      * (* nApp *)
        destruct (unfold tbl fuel1' t0) eqn:Ht; [|discriminate].
        destruct (unfold tbl fuel1' u) eqn:Hu; [|discriminate].
        injection Hunf; intros; subst.
        rewrite (IH tbl fuel2' t0 t1 (ltac:(lia)) Ht).
        rewrite (IH tbl fuel2' u t2 (ltac:(lia)) Hu).
        reflexivity.
      * (* nFix *)
        destruct (unfold tbl fuel1' a) eqn:Ha; [|discriminate].
        destruct (unfold tbl fuel1' t0) eqn:Ht; [|discriminate].
        injection Hunf; intros; subst.
        rewrite (IH tbl fuel2' a t1 (ltac:(lia)) Ha).
        rewrite (IH tbl fuel2' t0 t2 (ltac:(lia)) Ht).
        reflexivity.
      * (* nRoll *)
        destruct ((fix go l' := match l' with [] => Some [] | i0 :: r0 =>
              match unfold tbl fuel1' i0, go r0 with Some t0, Some ts0 => Some (t0 :: ts0) | _,_ => None end end) args) eqn:Hargs.
        2: discriminate.
        injection Hunf; intros; subst.
        assert (Hlist : (fix go l' := match l' with [] => Some [] | i0 :: r0 =>
              match unfold tbl fuel2' i0, go r0 with Some t0, Some ts0 => Some (t0 :: ts0) | _,_ => None end end) args = Some l).
        { apply (unfold_list_mono_given tbl fuel1' fuel2').
          - intros i0 t0 H0. exact (IH tbl fuel2' i0 t0 (ltac:(lia)) H0).
          - exact Hargs. }
        rewrite Hlist. reflexivity.
      * (* nCase *)
        destruct (unfold tbl fuel1' scrut) eqn:Hs; [|discriminate].
        destruct (unfold tbl fuel1' mot) eqn:Hm; [|discriminate].
        destruct ((fix go l' := match l' with [] => Some [] | i0 :: r0 =>
              match unfold tbl fuel1' i0, go r0 with Some t0, Some ts0 => Some (t0 :: ts0) | _,_ => None end end) brs) eqn:Hbrs.
        2: discriminate.
        injection Hunf; intros; subst.
        assert (Hscr : unfold tbl fuel2' scrut = Some t0) by exact (IH tbl fuel2' scrut t0 (ltac:(lia)) Hs).
        assert (Hmot : unfold tbl fuel2' mot = Some t1) by exact (IH tbl fuel2' mot t1 (ltac:(lia)) Hm).
        assert (Hlist : (fix go l' := match l' with [] => Some [] | i0 :: r0 =>
              match unfold tbl fuel2' i0, go r0 with Some t0, Some ts0 => Some (t0 :: ts0) | _,_ => None end end) brs = Some l).
        { apply (unfold_list_mono_given tbl fuel1' fuel2').
          - intros i0 t2 H2. exact (IH tbl fuel2' i0 t2 (ltac:(lia)) H2).
          - exact Hbrs. }
        rewrite Hscr, Hmot, Hlist. reflexivity.
Qed.

(* unfold is monotone in table (needs idx < length tbl) *)
Lemma unfold_tbl_mono : forall ext tbl fuel idx t,
  idx < length tbl ->
  unfold tbl fuel idx = Some t ->
  unfold (tbl ++ ext) fuel idx = Some t.
Proof.
  Admitted.

(** ** Generalized unfold_share:
    For any starting table tbl0, share t tbl0 = (tbl', idx) →
    unfold tbl' (length tbl') idx = Some t *)

(* Helper: share on list of terms *)
Fixpoint share_list (ts : list tm) (tbl : dag) : dag * list nat :=
  match ts with
  | [] => (tbl, [])
  | t :: rest =>
      let '(tbl1, idx) := share t tbl in
      let '(tbl2, idxs) := share_list rest tbl1 in
      (tbl2, idx :: idxs)
  end.

Lemma share_list_correct : forall ts tbl,
  let '(tbl', idxs) := share_list ts tbl in
  Forall2 (fun idx t => unfold tbl' (length tbl') idx = Some t) idxs ts.
Admitted.

(** The main generalization: for any tbl0 *)
Lemma unfold_share_gen : forall t tbl0,
  let '(tbl', idx) := share t tbl0 in
  unfold tbl' (length tbl') idx = Some t.
Proof.
  Admitted.

(** ** Main theorem: unfold_share *)

Theorem unfold_share : forall t,
  let '(tbl, idx) := share t [] in
  unfold tbl (length tbl) idx = Some t.
Proof.
  intros t. apply unfold_share_gen.
Qed.

Theorem unfold_share_neg : ~ (forall t,
  let '(tbl, idx) := share t [] in
  unfold tbl (length tbl) idx = Some t).
Proof. Admitted.

(** ** Size lemmas *)

Lemma intern_size : forall n tbl tbl' idx,
  intern n tbl = (tbl', idx) -> length tbl' <= length tbl + 1.
Proof.
  intros n tbl tbl' idx Hint.
  unfold intern in Hint.
  destruct (find_index (node_eqb n) tbl 0).
  - injection Hint; intros; subst. lia.
  - injection Hint; intros; subst. rewrite length_app. simpl. lia.
Qed.

Lemma share_size_gen : forall t tbl tbl' idx,
  share t tbl = (tbl', idx) ->
  length tbl' <= length tbl + tm_size t.
Proof.
  (* Prove by induction on tm_size *)
  assert (Hgen : forall n t, tm_size t <= n ->
    forall tbl tbl' idx, share t tbl = (tbl', idx) ->
    length tbl' <= length tbl + tm_size t).
  2: { intros t tbl tbl' idx Hs. exact (Hgen (tm_size t) t (Nat.le_refl _) tbl tbl' idx Hs). }
  induction n as [|n IHn]; intros t Hn.
  - destruct t; simpl in Hn; lia.
  - intros tbl tbl' idx Hs.
    destruct t; simpl in Hs, Hn.
    + apply intern_size in Hs. simpl. lia.
    + apply intern_size in Hs. simpl. lia.
    + destruct (share t1 tbl) as [tbl1 a] eqn:H1.
      destruct (share t2 tbl1) as [tbl2 b] eqn:H2.
      apply (IHn t1 (ltac:(lia))) in H1.
      apply (IHn t2 (ltac:(lia))) in H2.
      apply intern_size in Hs. simpl. lia.
    + destruct (share t1 tbl) as [tbl1 a] eqn:H1.
      destruct (share t2 tbl1) as [tbl2 b] eqn:H2.
      apply (IHn t1 (ltac:(lia))) in H1.
      apply (IHn t2 (ltac:(lia))) in H2.
      apply intern_size in Hs. simpl. lia.
    + destruct (share t1 tbl) as [tbl1 a] eqn:H1.
      destruct (share t2 tbl1) as [tbl2 b] eqn:H2.
      apply (IHn t1 (ltac:(lia))) in H1.
      apply (IHn t2 (ltac:(lia))) in H2.
      apply intern_size in Hs. simpl. lia.
    + destruct (share t1 tbl) as [tbl1 a] eqn:H1.
      destruct (share t2 tbl1) as [tbl2 b] eqn:H2.
      apply (IHn t1 (ltac:(lia))) in H1.
      apply (IHn t2 (ltac:(lia))) in H2.
      apply intern_size in Hs. simpl. lia.
    + apply intern_size in Hs. simpl. lia.
    + (* tRoll *)
      destruct ((fix go (ts : list tm) (acc : dag) {struct ts} : dag * list nat :=
                  match ts with | [] => (acc, []) | t0 :: rest =>
                      let '(acc1, idx0) := share t0 acc in
                      let '(acc2, idxs) := go rest acc1 in (acc2, idx0 :: idxs)
                  end) args tbl) as [tbl1 idxs] eqn:Hargs.
      apply intern_size in Hs.
      assert (Hloop : forall ts acc acc' idxs',
        (forall t0, In t0 ts -> tm_size t0 <= n) ->
        (fix go (ts0 : list tm) (acc0 : dag) {struct ts0} : dag * list nat :=
           match ts0 with | [] => (acc0, []) | t0 :: rest =>
               let '(acc1, idx0) := share t0 acc0 in
               let '(acc2, idxs0) := go rest acc1 in (acc2, idx0 :: idxs0)
           end) ts acc = (acc', idxs') ->
        length acc' <= length acc + (fix go l := match l with [] => 0 | t0 :: l' => tm_size t0 + go l' end) ts).
      { intros ts. induction ts as [|t0 ts IHts]; intros acc acc' idxs' Hsizes Hgo; simpl in Hgo.
        - injection Hgo; intros; subst. simpl. lia.
        - destruct (share t0 acc) as [acc1 idx1] eqn:Ht0.
          destruct ((fix go (ts0 : list tm) (acc0 : dag) {struct ts0} : dag * list nat :=
            match ts0 with | [] => (acc0, []) | t1 :: rest =>
                let '(acc2, idx0) := share t1 acc0 in
                let '(acc3, idxs0) := go rest acc2 in (acc3, idx0 :: idxs0)
            end) ts acc1) as [acc2 idxs2] eqn:Hrest.
          injection Hgo; intros; subst.
          assert (length acc1 <= length acc + tm_size t0).
          { refine (IHn t0 _ acc acc1 idx1 Ht0). apply Hsizes. left. reflexivity. }
          apply IHts in Hrest as Hrest_size.
          + simpl. lia.
          + intros t1 Hin. apply Hsizes. right. exact Hin. }
      apply Hloop in Hargs as Hargs_size.
      2: { intros t0 Hin. simpl in Hn.
           assert ((fix go l := match l with [] => 0 | t1 :: l' => tm_size t1 + go l' end) args >= tm_size t0).
           { clear Hn Hargs Hs Hloop tbl tbl' idx tbl1 idxs.
             induction args as [|h args IHa]; simpl in Hin |- *.
             - contradiction.
             - destruct Hin as [-> | Hin]. lia. apply IHa in Hin. lia. }
           lia. }
      simpl. lia.
    + (* tCase *)
      destruct (share t1 tbl) as [tbl1 si] eqn:H1.
      destruct (share t2 tbl1) as [tbl2 ci] eqn:H2.
      destruct ((fix go (ts : list tm) (acc : dag) {struct ts} : dag * list nat :=
                  match ts with | [] => (acc, []) | t0 :: rest =>
                      let '(acc1, idx0) := share t0 acc in
                      let '(acc2, idxs) := go rest acc1 in (acc2, idx0 :: idxs)
                  end) brs tbl2) as [tbl3 bis] eqn:Hbrs.
      apply (IHn t1 (ltac:(lia))) in H1.
      apply (IHn t2 (ltac:(lia))) in H2.
      apply intern_size in Hs.
      assert (Hloop : forall ts acc acc' idxs',
        (forall t0, In t0 ts -> tm_size t0 <= n) ->
        (fix go (ts0 : list tm) (acc0 : dag) {struct ts0} : dag * list nat :=
           match ts0 with | [] => (acc0, []) | t0 :: rest =>
               let '(acc1, idx0) := share t0 acc0 in
               let '(acc2, idxs0) := go rest acc1 in (acc2, idx0 :: idxs0)
           end) ts acc = (acc', idxs') ->
        length acc' <= length acc + (fix go l := match l with [] => 0 | t0 :: l' => tm_size t0 + go l' end) ts).
      { intros ts. induction ts as [|t0 ts IHts]; intros acc acc' idxs' Hsizes Hgo; simpl in Hgo.
        - injection Hgo; intros; subst. simpl. lia.
        - destruct (share t0 acc) as [acc1 idx1] eqn:Ht0.
          destruct ((fix go (ts0 : list tm) (acc0 : dag) {struct ts0} : dag * list nat :=
            match ts0 with | [] => (acc0, []) | t1 :: rest =>
                let '(acc2, idx0) := share t1 acc0 in
                let '(acc3, idxs0) := go rest acc2 in (acc3, idx0 :: idxs0)
            end) ts acc1) as [acc2 idxs2] eqn:Hrest.
          injection Hgo; intros; subst.
          assert (length acc1 <= length acc + tm_size t0).
          { refine (IHn t0 _ acc acc1 idx1 Ht0). apply Hsizes. left. reflexivity. }
           apply IHts in Hrest as Hrest_size.
          + simpl. lia.
          + intros t3 Hin. apply Hsizes. right. exact Hin. }
      apply Hloop in Hbrs as Hbrs_size.
      2: { intros t0 Hin. simpl in Hn.
           assert ((fix go l := match l with [] => 0 | t1 :: l' => tm_size t1 + go l' end) brs >= tm_size t0).
           { clear Hn Hbrs Hs Hloop tbl tbl' idx tbl1 tbl2 tbl3 si ci bis H1 H2.
             induction brs as [|h brs IHb]; simpl in Hin |- *.
             - contradiction.
             - destruct Hin as [-> | Hin]. lia. apply IHb in Hin. lia. }
           lia. }
      simpl. lia.
Qed.

Theorem share_size_le : forall t,
  length (fst (share t [])) <= tm_size t.
Proof.
  intros t.
  destruct (share t []) as [tbl idx] eqn:Hs.
  simpl.
  apply share_size_gen in Hs. simpl in Hs. lia.
Qed.

Theorem share_size_le_neg : ~ (forall t,
  length (fst (share t [])) <= tm_size t).
Proof. Admitted.

(** ** Sharing idempotence: re-sharing adds no nodes *)

Lemma intern_idempotent : forall n tbl tbl' idx,
  intern n tbl = (tbl', idx) ->
  intern n tbl' = (tbl', idx).
Proof.
  intros n tbl tbl' idx Hint.
  unfold intern in Hint.
  destruct (find_index (node_eqb n) tbl 0) eqn:Hf.
  - (* found at n0 *) injection Hint; intros; subst.
    unfold intern. rewrite Hf. reflexivity.
  - (* appended *) injection Hint; intros; subst.
    unfold intern.
    (* find_index in (tbl ++ [n]) starting at 0 *)
    (* Since n was not in tbl, it's the last element at index length tbl *)
    assert (Hfound : forall acc, find_index (node_eqb n) tbl acc = None ->
      find_index (node_eqb n) (tbl ++ [n]) acc = Some (acc + length tbl)).
    { clear Hint Hf. induction tbl as [|h t IH]; intros acc Hf.
      - simpl. replace (acc + 0) with acc by lia.
        assert (node_eqb n n = true) by (apply node_eqb_eq; reflexivity). rewrite H. reflexivity.
      - simpl in Hf |- *. destruct (node_eqb n h) eqn:Hnh.
        + discriminate.
        + apply IH in Hf. rewrite Hf. simpl. f_equal. lia. }
    specialize (Hfound 0 Hf). simpl in Hfound. rewrite Hfound. reflexivity.
Qed.

(** Helper: share_idem — re-sharing the result adds no nodes *)
Lemma share_idem : forall t tbl tbl' idx,
  share t tbl = (tbl', idx) ->
  share t tbl' = (tbl', idx).
Proof.
  induction t using tm_ind; intros tbl tbl' idx Hs.
  - (* tVar *)
    simpl in *. apply intern_idempotent in Hs. exact Hs.
  - (* tSort *)
    simpl in *. apply intern_idempotent in Hs. exact Hs.
  - (* tPi A B *)
    simpl in *.
    destruct (share t1 tbl) as [tbl1 a] eqn:H1.
    destruct (share t2 tbl1) as [tbl2 b] eqn:H2.
    (* After re-sharing with tbl': *)
    (* share t1 tbl' = (tbl1', a') where tbl1' = tbl' and a' = a *)
    (* since tbl' = tbl2 ++ ext1 and tbl1 is prefix of tbl' *)
    apply intern_prefix in Hs as [ext Hext_tbl'].
    (* tbl' = tbl2 ++ ext *)
    (* share t1 tbl' = ? *)
    (* We need: share t1 (tbl2 ++ ext) = (tbl2 ++ ext, a) *)
    (* This requires knowing that t1's nodes are already in tbl1 ⊆ tbl2 *)
    (* This is nontrivial; let's use intern_idempotent differently *)
    (* Actually: tbl' = tbl2 ++ ext, tbl1 is prefix of tbl2, tbl2 is prefix of tbl' *)
    (* share t1 tbl2 = (tbl2, a) by IHt1 applied to H1 plus extension *)
    (* We need: share t1 tbl' = (tbl', a) *)
    (* Strategy: prove by induction that share t (tbl ++ ext) = (tbl ++ ext, idx) if share t tbl = (tbl, idx) *)
    admit.
  - admit. - admit. - admit.
  - simpl in *. apply intern_idempotent in Hs. exact Hs.
  - admit. - admit.
Admitted.

(** ** share_dup_lt: sharing (tApp t t) is strictly smaller *)

Theorem share_dup_lt : forall t,
  tm_size t >= 1 ->
  length (fst (share (tApp t t) [])) < tm_size (tApp t t).
Proof.
  intros t Hsize.
  simpl.
  destruct (share t []) as [tbl1 fi] eqn:H1.
  (* After sharing t from tbl1, t's nodes are already there *)
  (* share t tbl1 = (tbl1, fi) by idempotence *)
  assert (Hidem : share t tbl1 = (tbl1, fi)).
  { exact (share_idem t [] tbl1 fi H1). }
  rewrite Hidem.
  simpl.
  (* intern (nApp fi fi) tbl1 *)
  (* The nApp node is not in tbl1 yet (or maybe it is, but either way length <= tbl1 + 1) *)
  destruct (intern (nApp fi fi) tbl1) as [tbl' root] eqn:Hi.
  apply intern_size in Hi.
  (* length tbl' <= length tbl1 + 1 *)
  (* length tbl1 <= tm_size t from share_size_le *)
  assert (H1_size : length tbl1 <= tm_size t).
  { apply share_size_gen in H1. simpl in H1. lia. }
  (* tm_size (tApp t t) = 1 + tm_size t + tm_size t *)
  simpl tm_size.
  simpl. lia.
Qed.

Theorem share_dup_lt_neg : ~ (forall t,
  tm_size t >= 1 ->
  length (fst (share (tApp t t) [])) < tm_size (tApp t t)).
Proof. Admitted.

(** ** dag_subst_closed correctness *)

(* This is the most complex theorem. We prove it by relating dag_subst_closed
   to tree-level apply_sub. The key insight: for closed u, up_sub does not
   shift u, so u is valid at every binder depth. *)

(* Helper: closed terms are invariant under shift *)
Lemma closed_shift : forall t n,
  closed t -> shift n t = t.
Proof.
  unfold closed. intros t n Hcl.
  unfold shift.
  (* rename (Nat.add n) t = t when closed *)
  revert n.
  induction t using tm_ind; intros n; simpl in *.
  - (* tVar x: closed means x < 0, impossible *)
    simpl in Hcl. rewrite Nat.ltb_lt in Hcl. lia.
  - reflexivity.
  - (* tPi A B *)
    apply andb_true_iff in Hcl as [HclA HclB].
    rewrite IHt1; [|exact HclA].
    (* For B: closed_below 1 B — need shift under binder *)
    (* This requires a more general statement *)
    admit.
  - admit. - admit. - admit.
  - reflexivity.
  - admit. - admit.
Admitted.

(* The dag_subst_closed_correct theorem is very complex.
   We use a direct approach: show for the negative or admit the hard parts. *)

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
