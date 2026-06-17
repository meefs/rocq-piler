From Stdlib Require Import Arith List Lia.
Import ListNotations.

(** Standalone reproduction of the shift_at_typing Lam-case seal-on-apply bug. *)

Inductive ty : Type := TyNat | TyBool | TyArrow : ty -> ty -> ty.

Inductive tm : Type :=
  | Var : nat -> tm | Num : nat -> tm | Lam : ty -> tm -> tm.

Definition ctx := list ty.
Definition store_ty := list ty.

Inductive has_type : ctx -> store_ty -> tm -> ty -> Prop :=
  | T_Var : forall G S x T, nth_error G x = Some T -> has_type G S (Var x) T
  | T_Num : forall G S n, has_type G S (Num n) TyNat
  | T_Lam : forall G S T1 T2 t, has_type (T1 :: G) S t T2 -> has_type G S (Lam T1 t) (TyArrow T1 T2).

Fixpoint shift_at (d : nat) (t : tm) : tm :=
  match t with
  | Var x => if x <? d then Var x else Var (x + 1)
  | Num n => Num n
  | Lam T t1 => Lam T (shift_at (S d) t1)
  end.

(** The buggy lemma: apply (IHhas_type INS (S d)) fails to close the Lam case
    because Coq's conversion cannot reduce firstn/skipn/++ during apply unification. *)
Lemma shift_at_typing : forall d G S t T INS,
  has_type G S t T ->
  has_type (firstn d G ++ INS :: skipn d G) S (shift_at d t) T.
Proof.
  intros d G S t T INS H; generalize dependent d; generalize dependent INS; induction H; intros INS d; simpl; try (constructor; eauto); try (econstructor; eauto).
  { (* case_1:fbaa7224 *) admit. }
  { (* case_2:a76b7a39 *) admit. }
Admitted.
