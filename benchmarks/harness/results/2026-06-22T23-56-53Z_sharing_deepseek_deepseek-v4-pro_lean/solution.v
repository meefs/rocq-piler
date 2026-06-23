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

(** ** Auxiliary lemmas *)

Lemma nth_error_app_L : forall A (l1 l2 : list A) i x,
  nth_error l1 i = Some x -> nth_error (l1 ++ l2) i = Some x.
Proof.
  induction l1; intros; simpl in *.
  - destruct i; discriminate.
  - destruct i; simpl in *; auto.
Qed.

Lemma nth_error_app_singleton : forall A (l : list A) (x : A),
  nth_error (l ++ [x]) (length l) = Some x.
Proof.
  induction l; intros; simpl; auto.
Qed.

Lemma find_index_ge : forall f l acc idx,
    find_index f l acc = Some idx -> acc <= idx.
Proof.
  induction l as [|a l IHl]; intros acc idx H; simpl in H.
  - discriminate.
  - destruct (f a).
    + inversion H; subst; lia.
    + apply IHl in H; lia.
Qed.

Lemma find_index_nth : forall n tbl acc idx,
  find_index (node_eqb n) tbl acc = Some idx ->
  exists a, nth_error tbl (idx - acc) = Some a /\ node_eqb n a = true.
Proof.
  induction tbl as [|a tbl IHtbl]; intros acc idx H; simpl in H.
  - discriminate.
  - destruct (node_eqb n a) eqn:E; simpl in H;
      [ inversion H; subst; exists a; split; auto
      | assert (Hge: S acc <= idx) by (apply find_index_ge with (f:=node_eqb n) (l:=tbl); exact H);
        apply IHtbl in H;
        destruct H as [a' H'];
        destruct H' as [Hnth Heq];
        exists a'; split;
          [ replace (idx - acc) with (S (idx - S acc)) by lia; simpl; exact Hnth
          | exact Heq ] ].
Qed.

Lemma intern_nth : forall n tbl tbl' idx,
  intern n tbl = (tbl', idx) ->
  nth_error tbl' idx = Some n.
Proof.
  unfold intern; intros.
  destruct (find_index (node_eqb n) tbl 0) eqn:E.
  - injection H as -> ->.
    apply find_index_nth in E. destruct E as [a [Hnth Heq]].
    apply node_eqb_eq in Heq; subst.
    rewrite Nat.sub_0_r in Hnth. exact Hnth.
  - injection H as -> ->.
    apply nth_error_app_singleton.
Qed.

Lemma intern_length_ge : forall n tbl tbl' idx,
  intern n tbl = (tbl', idx) -> length tbl' >= length tbl.
Proof.
  unfold intern; intros.
  destruct (find_index (node_eqb n) tbl 0) eqn:E.
  - injection H as -> ->; lia.
  - injection H as -> ->; rewrite app_length; simpl; lia.
Qed.

Fixpoint unfold_list (tbl : dag) (fuel : nat) (args : list nat) : option (list tm) :=
  match args with
  | [] => Some []
  | i :: args' =>
      match unfold tbl fuel i, unfold_list tbl fuel args' with
      | Some t, Some ts => Some (t :: ts)
      | _, _ => None
      end
  end.

Lemma unfold_go_eq : forall tbl fuel args,
  (fix go (l : list nat) :=
     match l with
     | [] => Some []
     | i :: l' => match unfold tbl fuel i, go l' with Some t, Some ts => Some (t :: ts) | _, _ => None end
     end) args = unfold_list tbl fuel args.
Proof.
  induction args; simpl; auto.
  rewrite IHargs. reflexivity.
Qed.

Lemma unfold_fuel_mono : forall tbl fuel fuel' idx t,
  fuel <= fuel' ->
  unfold tbl fuel idx = Some t ->
  unfold tbl fuel' idx = Some t.
Proof.
  induction fuel as [|fuel IHfuel]; intros fuel' idx t Hle Hu.
  - simpl in Hu; discriminate.
  - simpl in Hu.
    destruct fuel' as [|fuel'].
    { lia. }
    { simpl.
      destruct (nth_error tbl idx) eqn:Enth; try discriminate.
      destruct n0; simpl in *;
      try (injection Hu as ->; auto).
      (* nPi a b *)
      { destruct (unfold tbl fuel n1) eqn:Ea; try discriminate.
        destruct (unfold tbl fuel n2) eqn:Eb; try discriminate.
        injection Hu as ->.
        apply IHfuel with (fuel' := fuel') in Ea; [|lia].
        apply IHfuel with (fuel' := fuel') in Eb; [|lia].
        rewrite Ea, Eb. auto. }
      (* nLam a t0 *)
      { destruct (unfold tbl fuel n1) eqn:Ea; try discriminate.
        destruct (unfold tbl fuel n2) eqn:Et; try discriminate.
        injection Hu as ->.
        apply IHfuel with (fuel' := fuel') in Ea; [|lia].
        apply IHfuel with (fuel' := fuel') in Et; [|lia].
        rewrite Ea, Et. auto. }
      (* nApp t0 u *)
      { destruct (unfold tbl fuel n1) eqn:Ef; try discriminate.
        destruct (unfold tbl fuel n2) eqn:Ea; try discriminate.
        injection Hu as ->.
        apply IHfuel with (fuel' := fuel') in Ef; [|lia].
        apply IHfuel with (fuel' := fuel') in Ea; [|lia].
        rewrite Ef, Ea. auto. }
      (* nFix a t0 *)
      { destruct (unfold tbl fuel n1) eqn:Ea; try discriminate.
        destruct (unfold tbl fuel n2) eqn:Et; try discriminate.
        injection Hu as ->.
        apply IHfuel with (fuel' := fuel') in Ea; [|lia].
        apply IHfuel with (fuel' := fuel') in Et; [|lia].
        rewrite Ea, Et. auto. }
      (* nRoll Ix c args *)
      { destruct ((fix go (l : list nat) :=
                    match l with
                    | [] => Some []
                    | i :: l' => match unfold tbl fuel i, go l' with Some t0, Some ts => Some (t0 :: ts) | _, _ => None end
                    end) args) eqn:Eargs; try discriminate.
        injection Hu as ->.
        rewrite (unfold_go_eq tbl fuel args) in Eargs.
        rewrite (unfold_go_eq tbl fuel' args).
        revert Eargs.
        induction args as [|a args' IHargs]; intros; simpl in *.
        { auto. }
        { destruct (unfold tbl fuel a) eqn:Ea; try discriminate.
          destruct (unfold_list tbl fuel args') eqn:El; try discriminate.
          injection Eargs as ->.
          apply IHfuel with (fuel' := fuel') in Ea; [|lia].
          rewrite Ea.
          apply IHargs. simpl. rewrite El. reflexivity. } }
      (* nCase Ix s m brs *)
      { destruct (unfold tbl fuel n1) eqn:Es; try discriminate.
        destruct (unfold tbl fuel n2) eqn:Em; try discriminate.
        destruct ((fix go (l : list nat) :=
                    match l with
                    | [] => Some []
                    | i :: l' => match unfold tbl fuel i, go l' with Some t0, Some ts => Some (t0 :: ts) | _, _ => None end
                    end) n3) eqn:Ebrs; try discriminate.
        injection Hu as ->.
        apply IHfuel with (fuel' := fuel') in Es; [|lia].
        apply IHfuel with (fuel' := fuel') in Em; [|lia].
        rewrite Es, Em.
        rewrite (unfold_go_eq tbl fuel n3) in Ebrs.
        rewrite (unfold_go_eq tbl fuel' n3).
        revert Ebrs.
        induction n3 as [|b brs' IHbrs]; intros; simpl in *.
        { auto. }
        { destruct (unfold tbl fuel b) eqn:Eb; try discriminate.
          destruct (unfold_list tbl fuel brs') eqn:El; try discriminate.
          injection Ebrs as ->.
          apply IHfuel with (fuel' := fuel') in Eb; [|lia].
          rewrite Eb.
          apply IHbrs. simpl. rewrite El. reflexivity. } } }
Qed.

Lemma intern_preserves_unfold : forall n tbl tbl' idx fuel i t,
  intern n tbl = (tbl', idx) ->
  unfold tbl fuel i = Some t ->
  unfold tbl' fuel i = Some t.
Proof.
  unfold intern; intros n tbl tbl' idx fuel i t Hi Hu.
  destruct (find_index (node_eqb n) tbl 0) eqn:E.
  - injection Hi as -> ->. exact Hu.
  - injection Hi as -> ->.
    revert i t Hu.
    induction fuel as [|fuel' IHfuel]; intros i t Hu; simpl in Hu.
    { discriminate. }
    { simpl.
      destruct (nth_error tbl i) eqn:Enth; try discriminate.
      rewrite nth_error_app_L with (x := n); auto.
      destruct n0; simpl in *;
      try (injection Hu as ->; auto).
      (* nPi a b *)
      { destruct (unfold tbl fuel' n1) eqn:Ea; try discriminate.
        destruct (unfold tbl fuel' n2) eqn:Eb; try discriminate.
        injection Hu as ->.
        rewrite (IHfuel n1 t0 Ea).
        rewrite (IHfuel n2 t1 Eb).
        auto. }
      (* nLam a t0 *)
      { destruct (unfold tbl fuel' n1) eqn:Ea; try discriminate.
        destruct (unfold tbl fuel' n2) eqn:Et; try discriminate.
        injection Hu as ->.
        rewrite (IHfuel n1 t0 Ea).
        rewrite (IHfuel n2 t1 Et).
        auto. }
      (* nApp t0 u *)
      { destruct (unfold tbl fuel' n1) eqn:Ef; try discriminate.
        destruct (unfold tbl fuel' n2) eqn:Ea; try discriminate.
        injection Hu as ->.
        rewrite (IHfuel n1 t0 Ef).
        rewrite (IHfuel n2 t1 Ea).
        auto. }
      (* nFix a t0 *)
      { destruct (unfold tbl fuel' n1) eqn:Ea; try discriminate.
        destruct (unfold tbl fuel' n2) eqn:Et; try discriminate.
        injection Hu as ->.
        rewrite (IHfuel n1 t0 Ea).
        rewrite (IHfuel n2 t1 Et).
        auto. }
      (* nRoll Ix c args *)
      { destruct ((fix go (l : list nat) :=
                    match l with
                    | [] => Some []
                    | i0 :: l' => match unfold tbl fuel' i0, go l' with Some t1, Some ts => Some (t1 :: ts) | _, _ => None end
                    end) n0) eqn:Eargs; try discriminate.
        injection Hu as ->.
        rewrite (unfold_go_eq tbl fuel' n0) in Eargs.
        rewrite (unfold_go_eq (tbl ++ [n]) fuel' n0).
        revert Eargs.
        induction n0 as [|a args' IHargs]; intros; simpl in *.
        { auto. }
        { destruct (unfold tbl fuel' a) eqn:Ea; try discriminate.
          destruct (unfold_list tbl fuel' args') eqn:El; try discriminate.
          injection Eargs as ->.
          simpl.
          rewrite (IHfuel a t0 Ea).
          apply IHargs. simpl. rewrite El. reflexivity. } }
      (* nCase Ix s m brs *)
      { destruct (unfold tbl fuel' n1) eqn:Es; try discriminate.
        destruct (unfold tbl fuel' n2) eqn:Em; try discriminate.
        destruct ((fix go (l : list nat) :=
                    match l with
                    | [] => Some []
                    | i0 :: l' => match unfold tbl fuel' i0, go l' with Some t1, Some ts => Some (t1 :: ts) | _, _ => None end
                    end) n3) eqn:Ebrs; try discriminate.
        injection Hu as ->.
        simpl.
        rewrite (IHfuel n1 t0 Es).
        rewrite (IHfuel n2 t1 Em).
        rewrite (unfold_go_eq tbl fuel' n3) in Ebrs.
        rewrite (unfold_go_eq (tbl ++ [n]) fuel' n3).
        revert Ebrs.
        induction n3 as [|b brs' IHbrs]; intros; simpl in *.
        { auto. }
        { destruct (unfold tbl fuel' b) eqn:Eb; try discriminate.
          destruct (unfold_list tbl fuel' brs') eqn:El; try discriminate.
          injection Ebrs as ->.
          simpl.
          rewrite (IHfuel b t0 Eb).
          apply IHbrs. simpl. rewrite El. reflexivity. } } }
Qed.

Lemma share_unfold_ok : forall t tbl tbl' idx,
  share t tbl = (tbl', idx) ->
  unfold tbl' (length tbl') idx = Some t.
Proof.
  induction t; simpl; intros tbl tbl' idx Hsh.
  - (* tVar *)
    apply intern_nth in Hsh.
    simpl. rewrite Hsh. auto.
  - (* tSort *)
    apply intern_nth in Hsh.
    simpl. rewrite Hsh. auto.
  - (* tPi *)
    destruct (share t1 tbl) as [tbl1 a] eqn:E1.
    destruct (share t2 tbl1) as [tbl2 b] eqn:E2.
    unfold intern in Hsh.
    destruct (find_index (node_eqb (nPi a b)) tbl2 0) eqn:E3;
    injection Hsh as -> ->.
    apply IHt1 in E1. apply IHt2 in E2.
    pose proof (intern_nth (nPi a b) tbl2) as Hnth.
    unfold intern in Hnth. rewrite E3 in Hnth.
    simpl. rewrite Hnth.
    pose proof (intern_length_ge (nPi a b) tbl2) as Hlen.
    unfold intern in Hlen. rewrite E3 in Hlen.
    destruct (find_index (node_eqb (nPi a b)) tbl2 0); simpl in *.
    { apply unfold_fuel_mono with (fuel := length tbl2).
      { destruct (node_eqb (nPi a b) n) eqn:E4; simpl; lia. }
      simpl. rewrite E2.
      apply unfold_fuel_mono with (fuel := length tbl1); [lia|].
      apply intern_preserves_unfold with (tbl := tbl1) (n := nPi a b).
      { unfold intern. rewrite E3. reflexivity. }
      exact E1. }
    { apply unfold_fuel_mono with (fuel := length tbl2).
      { rewrite app_length; simpl; lia. }
      simpl. rewrite E2.
      apply unfold_fuel_mono with (fuel := length tbl1); [lia|].
      apply intern_preserves_unfold with (tbl := tbl1) (n := nPi a b).
      { unfold intern. rewrite E3. reflexivity. }
      exact E1. }
  - (* tLam *)
    destruct (share t1 tbl) as [tbl1 a] eqn:E1.
    destruct (share t2 tbl1) as [tbl2 ti] eqn:E2.
    unfold intern in Hsh.
    destruct (find_index (node_eqb (nLam a ti)) tbl2 0) eqn:E3;
    injection Hsh as -> ->.
    apply IHt1 in E1. apply IHt2 in E2.
    pose proof (intern_nth (nLam a ti) tbl2) as Hnth.
    unfold intern in Hnth. rewrite E3 in Hnth.
    simpl. rewrite Hnth.
    destruct (find_index (node_eqb (nLam a ti)) tbl2 0); simpl.
    { apply unfold_fuel_mono with (fuel := length tbl2); [lia|].
      simpl. rewrite E2.
      apply unfold_fuel_mono with (fuel := length tbl1); [lia|].
      apply intern_preserves_unfold with (tbl := tbl1) (n := nLam a ti).
      { unfold intern. rewrite E3. reflexivity. }
      exact E1. }
    { apply unfold_fuel_mono with (fuel := length tbl2); [rewrite app_length; simpl; lia|].
      simpl. rewrite E2.
      apply unfold_fuel_mono with (fuel := length tbl1); [lia|].
      apply intern_preserves_unfold with (tbl := tbl1) (n := nLam a ti).
      { unfold intern. rewrite E3. reflexivity. }
      exact E1. }
  - (* tApp *)
    destruct (share t1 tbl) as [tbl1 fi] eqn:E1.
    destruct (share t2 tbl1) as [tbl2 ai] eqn:E2.
    unfold intern in Hsh.
    destruct (find_index (node_eqb (nApp fi ai)) tbl2 0) eqn:E3;
    injection Hsh as -> ->.
    apply IHt1 in E1. apply IHt2 in E2.
    pose proof (intern_nth (nApp fi ai) tbl2) as Hnth.
    unfold intern in Hnth. rewrite E3 in Hnth.
    simpl. rewrite Hnth.
    destruct (find_index (node_eqb (nApp fi ai)) tbl2 0); simpl.
    { apply unfold_fuel_mono with (fuel := length tbl2); [lia|].
      simpl. rewrite E2, E1. auto. }
    { apply unfold_fuel_mono with (fuel := length tbl2); [rewrite app_length; simpl; lia|].
      simpl. rewrite E2, E1. auto. }
  - (* tFix *)
    destruct (share t1 tbl) as [tbl1 a] eqn:E1.
    destruct (share t2 tbl1) as [tbl2 ti] eqn:E2.
    unfold intern in Hsh.
    destruct (find_index (node_eqb (nFix a ti)) tbl2 0) eqn:E3;
    injection Hsh as -> ->.
    apply IHt1 in E1. apply IHt2 in E2.
    pose proof (intern_nth (nFix a ti) tbl2) as Hnth.
    unfold intern in Hnth. rewrite E3 in Hnth.
    simpl. rewrite Hnth.
    destruct (find_index (node_eqb (nFix a ti)) tbl2 0); simpl.
    { apply unfold_fuel_mono with (fuel := length tbl2); [lia|].
      simpl. rewrite E2.
      apply unfold_fuel_mono with (fuel := length tbl1); [lia|].
      apply intern_preserves_unfold with (tbl := tbl1) (n := nFix a ti).
      { unfold intern. rewrite E3. reflexivity. }
      exact E1. }
    { apply unfold_fuel_mono with (fuel := length tbl2); [rewrite app_length; simpl; lia|].
      simpl. rewrite E2.
      apply unfold_fuel_mono with (fuel := length tbl1); [lia|].
      apply intern_preserves_unfold with (tbl := tbl1) (n := nFix a ti).
      { unfold intern. rewrite E3. reflexivity. }
      exact E1. }
  - (* tInd *)
    apply intern_nth in Hsh.
    simpl. rewrite Hsh. auto.
  - (* tRoll *)
    destruct ((fix go (ts : list tm) (acc : dag) {struct ts} : dag * list nat :=
                match ts with
                | [] => (acc, [])
                | t0 :: rest =>
                    let '(acc1, idx0) := share t0 acc in
                    let '(acc2, idxs) := go rest acc1 in
                    (acc2, idx0 :: idxs)
                end) l tbl) as [tbl1 idxs] eqn:Ego.
    unfold intern in Hsh.
    destruct (find_index (node_eqb (nRoll n n0 idxs)) tbl1 0) eqn:E3;
    injection Hsh as -> ->.
    pose proof (intern_nth (nRoll n n0 idxs) tbl1) as Hnth.
    unfold intern in Hnth. rewrite E3 in Hnth.
    simpl. rewrite Hnth.
    destruct (find_index (node_eqb (nRoll n n0 idxs)) tbl1 0); simpl.
    { apply unfold_fuel_mono with (fuel := length tbl1); [lia|].
      simpl.
      rewrite (unfold_go_eq tbl1 (length tbl1 - 1) idxs).
      revert tbl tbl1 idxs Ego.
      induction l as [|t0 ts IHts]; intros tbl tbl1 idxs Ego; simpl in Ego.
      { injection Ego as -> ->. simpl. auto. }
      { destruct (share t0 tbl) as [tbl_int idx0] eqn:Es.
        destruct ((fix go (ts0 : list tm) (acc : dag) : dag * list nat :=
                    match ts0 with
                    | [] => (acc, [])
                    | t1 :: rest =>
                        let '(acc1, idx1) := share t1 acc in
                        let '(acc2, idxs0) := go rest acc1 in
                        (acc2, idx1 :: idxs0)
                    end) ts tbl_int) as [tbl_rest idxs_rest] eqn:Erest.
        injection Ego as -> ->.
        simpl.
        rewrite (IHt t0 tbl tbl_int idx0 Es).
        apply IHts with (tbl := tbl_int) (tbl1 := tbl_rest) (idxs := idxs_rest); auto. } }
    { apply unfold_fuel_mono with (fuel := length tbl1); [rewrite app_length; simpl; lia|].
      simpl.
      rewrite (unfold_go_eq tbl1 (length tbl1 - 1) idxs).
      revert tbl tbl1 idxs Ego.
      induction l as [|t0 ts IHts]; intros tbl tbl1 idxs Ego; simpl in Ego.
      { injection Ego as -> ->. simpl. auto. }
      { destruct (share t0 tbl) as [tbl_int idx0] eqn:Es.
        destruct ((fix go (ts0 : list tm) (acc : dag) : dag * list nat :=
                    match ts0 with
                    | [] => (acc, [])
                    | t1 :: rest =>
                        let '(acc1, idx1) := share t1 acc in
                        let '(acc2, idxs0) := go rest acc1 in
                        (acc2, idx1 :: idxs0)
                    end) ts tbl_int) as [tbl_rest idxs_rest] eqn:Erest.
        injection Ego as -> ->.
        simpl.
        rewrite (IHt t0 tbl tbl_int idx0 Es).
        apply IHts with (tbl := tbl_int) (tbl1 := tbl_rest) (idxs := idxs_rest); auto. } }
  - (* tCase *)
    destruct (share t1 tbl) as [tbl1 si] eqn:E1.
    destruct (share t2 tbl1) as [tbl2 ci] eqn:E2.
    destruct ((fix go (ts : list tm) (acc : dag) {struct ts} : dag * list nat :=
                match ts with
                | [] => (acc, [])
                | t0 :: rest =>
                    let '(acc1, idx0) := share t0 acc in
                    let '(acc2, idxs) := go rest acc1 in
                    (acc2, idx0 :: idxs)
                end) l tbl2) as [tbl3 bis] eqn:Ego.
    unfold intern in Hsh.
    destruct (find_index (node_eqb (nCase n si ci bis)) tbl3 0) eqn:E3;
    injection Hsh as -> ->.
    apply IHt1 in E1. apply IHt2 in E2.
    pose proof (intern_nth (nCase n si ci bis) tbl3) as Hnth.
    unfold intern in Hnth. rewrite E3 in Hnth.
    simpl. rewrite Hnth.
    destruct (find_index (node_eqb (nCase n si ci bis)) tbl3 0); simpl.
    { apply unfold_fuel_mono with (fuel := length tbl3); [lia|].
      simpl.
      apply unfold_fuel_mono with (fuel := length tbl1); [lia|].
      apply intern_preserves_unfold with (tbl := tbl1) (n := nCase n si ci bis).
      { unfold intern. rewrite E3. reflexivity. }
      apply intern_preserves_unfold with (tbl := tbl2) (n := nCase n si ci bis).
      { unfold intern. rewrite E3. reflexivity. }
      rewrite E2.
      rewrite (unfold_go_eq tbl3 (length tbl3 - 1) bis).
      revert tbl2 tbl3 bis Ego.
      induction l as [|t0 ts IHts]; intros tbl2 tbl3 bis Ego; simpl in Ego.
      { injection Ego as -> ->. simpl. rewrite E1. auto. }
      { destruct (share t0 tbl2) as [tbl_int idx0] eqn:Es.
        destruct ((fix go (ts0 : list tm) (acc : dag) : dag * list nat :=
                    match ts0 with
                    | [] => (acc, [])
                    | t1 :: rest =>
                        let '(acc1, idx1) := share t1 acc in
                        let '(acc2, idxs0) := go rest acc1 in
                        (acc2, idx1 :: idxs0)
                    end) ts tbl_int) as [tbl_rest idxs_rest] eqn:Erest.
        injection Ego as -> ->.
        simpl.
        rewrite (IHt t0 tbl2 tbl_int idx0 Es).
        apply IHts with (tbl2 := tbl_int) (tbl3 := tbl_rest) (bis := idxs_rest); auto. } }
    { apply unfold_fuel_mono with (fuel := length tbl3); [rewrite app_length; simpl; lia|].
      simpl.
      apply unfold_fuel_mono with (fuel := length tbl1); [lia|].
      apply intern_preserves_unfold with (tbl := tbl1) (n := nCase n si ci bis).
      { unfold intern. rewrite E3. reflexivity. }
      apply intern_preserves_unfold with (tbl := tbl2) (n := nCase n si ci bis).
      { unfold intern. rewrite E3. reflexivity. }
      rewrite E2.
      rewrite (unfold_go_eq tbl3 (length tbl3 - 1) bis).
      revert tbl2 tbl3 bis Ego.
      induction l as [|t0 ts IHts]; intros tbl2 tbl3 bis Ego; simpl in Ego.
      { injection Ego as -> ->. simpl. rewrite E1. auto. }
      { destruct (share t0 tbl2) as [tbl_int idx0] eqn:Es.
        destruct ((fix go (ts0 : list tm) (acc : dag) : dag * list nat :=
                    match ts0 with
                    | [] => (acc, [])
                    | t1 :: rest =>
                        let '(acc1, idx1) := share t1 acc in
                        let '(acc2, idxs0) := go rest acc1 in
                        (acc2, idx1 :: idxs0)
                    end) ts tbl_int) as [tbl_rest idxs_rest] eqn:Erest.
        injection Ego as -> ->.
        simpl.
        rewrite (IHt t0 tbl2 tbl_int idx0 Es).
        apply IHts with (tbl2 := tbl_int) (tbl3 := tbl_rest) (bis := idxs_rest); auto. } }
Qed.

Lemma share_fst_length : forall t tbl tbl' idx,
  share t tbl = (tbl', idx) ->
  length tbl' <= length tbl + tm_size t.
Proof.
  induction t; simpl; intros tbl tbl' idx Hsh.
  - (* tVar *)
    unfold intern in Hsh.
    destruct (find_index (node_eqb (nVar n)) tbl 0) eqn:E;
    injection Hsh as -> ->; simpl; try rewrite app_length; simpl; lia.
  - (* tSort *)
    unfold intern in Hsh.
    destruct (find_index (node_eqb (nSort n)) tbl 0) eqn:E;
    injection Hsh as -> ->; simpl; try rewrite app_length; simpl; lia.
  - (* tPi *)
    destruct (share t1 tbl) as [tbl1 a] eqn:E1.
    destruct (share t2 tbl1) as [tbl2 b] eqn:E2.
    unfold intern in Hsh.
    destruct (find_index (node_eqb (nPi a b)) tbl2 0) eqn:E3;
    injection Hsh as -> ->;
    apply IHt1 in E1; apply IHt2 in E2;
    simpl; try rewrite app_length; simpl; lia.
  - (* tLam *)
    destruct (share t1 tbl) as [tbl1 a] eqn:E1.
    destruct (share t2 tbl1) as [tbl2 ti] eqn:E2.
    unfold intern in Hsh.
    destruct (find_index (node_eqb (nLam a ti)) tbl2 0) eqn:E3;
    injection Hsh as -> ->;
    apply IHt1 in E1; apply IHt2 in E2;
    simpl; try rewrite app_length; simpl; lia.
  - (* tApp *)
    destruct (share t1 tbl) as [tbl1 fi] eqn:E1.
    destruct (share t2 tbl1) as [tbl2 ai] eqn:E2.
    unfold intern in Hsh.
    destruct (find_index (node_eqb (nApp fi ai)) tbl2 0) eqn:E3;
    injection Hsh as -> ->;
    apply IHt1 in E1; apply IHt2 in E2;
    simpl; try rewrite app_length; simpl; lia.
  - (* tFix *)
    destruct (share t1 tbl) as [tbl1 a] eqn:E1.
    destruct (share t2 tbl1) as [tbl2 ti] eqn:E2.
    unfold intern in Hsh.
    destruct (find_index (node_eqb (nFix a ti)) tbl2 0) eqn:E3;
    injection Hsh as -> ->;
    apply IHt1 in E1; apply IHt2 in E2;
    simpl; try rewrite app_length; simpl; lia.
  - (* tInd *)
    unfold intern in Hsh.
    destruct (find_index (node_eqb (nInd n)) tbl 0) eqn:E;
    injection Hsh as -> ->; simpl; try rewrite app_length; simpl; lia.
  - (* tRoll *)
    destruct ((fix go (ts : list tm) (acc : dag) {struct ts} : dag * list nat :=
                match ts with
                | [] => (acc, [])
                | t0 :: rest =>
                    let '(acc1, idx0) := share t0 acc in
                    let '(acc2, idxs) := go rest acc1 in
                    (acc2, idx0 :: idxs)
                end) l tbl) as [tbl1 idxs] eqn:Ego.
    unfold intern in Hsh.
    destruct (find_index (node_eqb (nRoll n n0 idxs)) tbl1 0) eqn:E3;
    injection Hsh as -> ->.
    simpl. rewrite app_length. simpl.
    assert (Hlen : length tbl1 <= length tbl +
      (fix go (l0 : list tm) : nat :=
         match l0 with
         | [] => 0
         | t0 :: l' => tm_size t0 + go l'
         end) l).
    { revert tbl tbl1 idxs Ego.
      induction l as [|t0 ts IHts]; intros tbl tbl1 idxs Ego; simpl in Ego.
      - injection Ego as -> ->. simpl. lia.
      - destruct (share t0 tbl) as [tbl_int idx0] eqn:Es.
        destruct ((fix go (ts0 : list tm) (acc : dag) : dag * list nat :=
                    match ts0 with
                    | [] => (acc, [])
                    | t1 :: rest =>
                        let '(acc1, idx1) := share t1 acc in
                        let '(acc2, idxs0) := go rest acc1 in
                        (acc2, idx1 :: idxs0)
                    end) ts tbl_int) as [tbl_rest idxs_rest] eqn:Erest.
        injection Ego as -> ->.
        apply IHt in Es.
        apply IHts with (idxs := idxs_rest) in Erest; [|reflexivity].
        simpl. lia. }
    lia.
  - (* tCase *)
    destruct (share t1 tbl) as [tbl1 si] eqn:E1.
    destruct (share t2 tbl1) as [tbl2 ci] eqn:E2.
    destruct ((fix go (ts : list tm) (acc : dag) {struct ts} : dag * list nat :=
                match ts with
                | [] => (acc, [])
                | t0 :: rest =>
                    let '(acc1, idx0) := share t0 acc in
                    let '(acc2, idxs) := go rest acc1 in
                    (acc2, idx0 :: idxs)
                end) l tbl2) as [tbl3 bis] eqn:Ego.
    unfold intern in Hsh.
    destruct (find_index (node_eqb (nCase n si ci bis)) tbl3 0) eqn:E3;
    injection Hsh as -> ->.
    apply IHt1 in E1. apply IHt2 in E2.
    simpl. rewrite app_length. simpl.
    assert (Hlen : length tbl3 <= length tbl +
      tm_size t1 + tm_size t2 +
      (fix go (l0 : list tm) : nat :=
         match l0 with
         | [] => 0
         | t0 :: l' => tm_size t0 + go l'
         end) l).
    { revert tbl2 tbl3 bis Ego.
      induction l as [|t0 ts IHts]; intros tbl2 tbl3 bis Ego; simpl in Ego.
      - injection Ego as -> ->. simpl. lia.
      - destruct (share t0 tbl2) as [tbl_int idx0] eqn:Es.
        destruct ((fix go (ts0 : list tm) (acc : dag) : dag * list nat :=
                    match ts0 with
                    | [] => (acc, [])
                    | t1 :: rest =>
                        let '(acc1, idx1) := share t1 acc in
                        let '(acc2, idxs0) := go rest acc1 in
                        (acc2, idx1 :: idxs0)
                    end) ts tbl_int) as [tbl_rest idxs_rest] eqn:Erest.
        injection Ego as -> ->.
        apply IHt in Es.
        apply IHts with (bis := idxs_rest) in Erest; [|reflexivity].
        simpl. lia. }
    lia.
Qed.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Theorem unfold_share : forall t,
  let '(tbl, idx) := share t [] in
  unfold tbl (length tbl) idx = Some t.
Proof.
  intros t. destruct (share t []) as [tbl idx] eqn:E.
  apply share_unfold_ok in E. exact E.
Qed.

Theorem unfold_share_neg : ~ (forall t,
  let '(tbl, idx) := share t [] in
  unfold tbl (length tbl) idx = Some t).
Proof. Admitted.

Theorem share_size_le : forall t,
  length (fst (share t [])) <= tm_size t.
Proof.
  intros t. destruct (share t []) as [tbl idx] eqn:E.
  apply share_fst_length in E. simpl in E. exact E.
Qed.

Theorem share_size_le_neg : ~ (forall t,
  length (fst (share t [])) <= tm_size t).
Proof. Admitted.

Theorem share_dup_lt : forall t,
  tm_size t >= 1 ->
  length (fst (share (tApp t t) [])) < tm_size (tApp t t).
Proof.
  intros t Hsz.
  destruct (share (tApp t t) []) as [tbl idx] eqn:E.
  simpl (fst (tbl, idx)).
  simpl in E.
  (* share (tApp t t) [] = 
     let '(tbl1, fi) := share t [] in
     let '(tbl2, ai) := share t tbl1 in
     intern (nApp fi ai) tbl2 *)
  destruct (share t []) as [tbl1 fi] eqn:E1.
  destruct (share t tbl1) as [tbl2 ai] eqn:E2.
  unfold intern in E.
  destruct (find_index (node_eqb (nApp fi ai)) tbl2 0) eqn:E3;
  injection E as -> ->.
  - (* node found, table unchanged *)
    simpl.
    apply share_fst_length in E1.
    apply share_fst_length in E2.
    simpl in E1.
    simpl in E2.
    pose proof (share_fst_length t [] tbl1 fi E1) as H1.
    pose proof (share_fst_length t tbl1 tbl2 ai E2) as H2.
    simpl in H1.
    assert (length tbl2 <= tm_size t + tm_size t).
    { lia. }
    assert (tm_size t + tm_size t + 1 = tm_size (tApp t t)).
    { simpl. lia. }
    assert (length tbl2 < tm_size (tApp t t)).
    { simpl. lia. }
    exact H5.
  - (* node not found, appended *)
    simpl. rewrite app_length. simpl.
    apply share_fst_length in E1.
    apply share_fst_length in E2.
    simpl in E1.
    assert (length tbl2 <= tm_size t + tm_size t). { lia. }
    assert (S (length tbl2) <= 1 + tm_size t + tm_size t). { lia. }
    simpl (tm_size (tApp t t)).
    simpl.
    destruct (tm_size t) eqn:Esz.
    - assert (tm_size t = 0) by lia. lia.
    - lia.
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
Proof.
  unfold not. intros H.
  pose proof (H (tVar 1) (tSort 0) eq_refl) as Hc.
  simpl in Hc.
  (* share (tSort 0) [] = ([nSort 0], 0) *)
  (* share (tVar 1) [nSort 0] = intern (nVar 1) [nSort 0]
     = ([nSort 0; nVar 1], 1) *)
  (* dag_subst_closed [nSort 0; nVar 1] 0 0 1 2:
     fuel=2, idx=1, nth_error ... 1 = Some (nVar 1)
     eqb 1 0 = false, 0 <? 1 = true
     intern (nVar 0) [nSort 0; nVar 1] = ([... nVar 0], 2)
     tbl_res = [nSort 0; nVar 1; nVar 0], idx_res = 2
     unfold ... 3 2 = Some (tVar 0) *)
  (* subst0 (tSort 0) (tVar 1) = tVar 1 *)
  assert (tVar 0 <> tVar 1) by (inversion 1).
  apply H0.
  (* Now we need to show Hc actually simplifies to Some (tVar 0) = Some (tVar 1) *)
  injection Hc. auto.
Qed.
