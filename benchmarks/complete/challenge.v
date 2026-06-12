From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants cancelable_invariants.
From iris.algebra Require Import excl.

(* In my solution, aux = gset gname, and join and subset are pointwise. These
 * definitions can be changed. *)
Definition aux : Type := unit.
Instance aux_empty : Empty aux := ().
Instance aux_sqsubseteq : SqSubsetEq aux := λ _ _, True.
Instance aux_join : Join aux := λ _ _, ().
Instance aux_sqsubseted_preorder : PreOrder (⊑@{aux}).
Proof.
  constructor.
  - done.
  - done.
Qed.

Lemma aux_join_sqsubseteq_l (x y : aux) : x ⊑ x ⊔ y.
Proof. done. Qed.
Lemma aux_join_sqsubseteq_r (x y : aux) : y ⊑ x ⊔ y.
Proof. done. Qed.

(* These definitions should stay the same *)
Definition world : Type := aux * gset gname.
Global Instance world_join : Join (world) := λ w1 w2,
  (w1.1 ⊔ w2.1, w1.2 ∪ w2.2).
Global Instance world_sqsubseteq : SqSubsetEq (world) := λ w1 w2,
  w1.1 ⊑ w2.1 ∧ w1.2 ⊆ w2.2.

Lemma world_join_sqsubseteq_l (w1 w2 : world) : w1 ⊑ w1 ⊔ w2.
Proof.
  split.
  - apply aux_join_sqsubseteq_l.
  - set_solver.
Qed.
Lemma world_join_sqsubseteq_r (w1 w2 : world) : w2 ⊑ w1 ⊔ w2.
Proof.
  split.
  - apply aux_join_sqsubseteq_r.
  - set_solver.
Qed.

Definition localN := nroot .@ "linv".

(* You may add more ghost state *)
Class theGpreS (Σ : gFunctors) := TheGpreS {
  theGS_excl_inG :: cinvG Σ;
}.
Class theGS (Σ : gFunctors) := TheGS {
  theGpreS_inG :: theGpreS Σ;
}.

Section definitions.
  Context `{theGS Σ} `{invGS Σ}.
  (* These definitions should be changed, but the signatures must stay the same *)
  #[using="All"]
  Definition global_inv : iProp Σ := inv localN True.

  #[using="All"]
  Definition interp_local_world (w : world) (E : coPset) : iProp Σ :=
    [∗ set] γ ∈ w.2, cinv_own γ 1%Qp.
End definitions.


(* These lemmas need to be proven for the above definitions *)
Section init.
  Context `{GpreS : theGpreS Σ} `{invGS Σ}.

  Lemma global_inv_init F :
    ⊢ |={F}=> ∃ _ : theGS Σ, global_inv.
  Proof.
    iIntros.
    iMod (inv_alloc localN ⊤ with "[//]") as "#Hinv".
    iModIntro.
    unshelve iExists (TheGS Σ GpreS).
    iFrame "#".
  Qed.
End init.

Section local_world.
  Context `{theGS Σ} `{invGS Σ}.

  Global Instance interp_local_world_timeless w E :
    Timeless (interp_local_world w E).
  Proof.
    rewrite /interp_local_world.
    apply big_sepS_timeless'.
    - apply _.
    - intros. apply cinv_own_timeless.
  Qed.

  (* The existential ι here is important: Allocating a local world at a
   * constant empty world ∅ is actually inconsistent wrt the other laws. ι
   * ensures that a closing wand from _acc cannot be used on another world. *)
  Lemma interp_local_world_alloc F :
    ↑localN ⊆ F →
    global_inv ={F}=∗ ∃ ι, interp_local_world (ι, ∅) ⊤.
  Proof.
    iIntros (Hsub) "#Hinv".
    iInv "Hinv" as ">Htrue" "Hclose".
    iModIntro.
    iExists (() : aux).
    rewrite /interp_local_world /= big_sepS_empty.
    iSplitR; [done|].
    iIntros "!>". by iApply "Hclose".
  Qed.

  (* It is important for soundness that only worlds at top mask can be merged *)
  Lemma interp_local_world_merge w1 w2 F :
    ↑localN ⊆ F →
    global_inv -∗
    interp_local_world w1 ⊤ -∗
    interp_local_world w2 ⊤ ={F}=∗
    interp_local_world (w1 ⊔ w2) ⊤.
  Proof.
    iIntros (Hsub) "#Hinv H1 H2".
    iInv "Hinv" as ">Htrue" "Hclose".
    rewrite /interp_local_world /=.
    iCombine "H1 H2" as "H12".
    iDestruct (big_sepS_union_2 with "H12") as "H".
    { intros x. rewrite /Absorbing. iIntros. done. }
    rewrite /world_join /= /fst /snd /=.
    iFrame "H". iIntros "!>". by iApply "Hclose".
  Qed.

  (* This is where the restriction that worlds can only be allocated at the
   * full masks comes up: It would be very interesting if there was a model
   * that instead of ⊤ had an arbitrary mask E *)
  Lemma interp_local_world_insert w γ F :
    ↑localN ⊆ F →
    global_inv -∗
    interp_local_world w ⊤ -∗
    cinv_own γ 1%Qp ={F}=∗
      interp_local_world (w.1, {[γ]} ∪ w.2) ⊤.
  Proof.
    iIntros (Hsub) "#Hinv Hw Hγ".
    iInv "Hinv" as ">Htrue" "Hclose".
    rewrite /interp_local_world /=.
    iCombine "Hw Hγ" as "Hwg".
    iDestruct (big_sepS_insert_2' with "Hwg") as "H".
    { rewrite /Absorbing /Affine. left. apply _. }
    iFrame "H". iIntros "!>". by iApply "Hclose".
  Qed.

  (* Strong version of this lemma I'd really like to have *)
  (*Lemma interp_local_world_insert w γ F E :*)
  (*  ↑localN ⊆ F →*)
  (*  global_inv -∗*)
  (*  interp_local_world w E -∗*)
  (*  cinv_own γ 1%Qp ={F}=∗*)
  (*    interp_local_world (w.1, {[γ]} ∪ w.2) E.*)
  (*Proof. Admitted.*)

  Lemma interp_local_world_extract γ w F :
    γ ∈ w.2 →
    ↑localN ⊆ F →
    global_inv -∗
    interp_local_world w ⊤ ={F}=∗ interp_local_world (w.1, w.2 ∖ {[γ]}) ⊤ ∗ cinv_own γ 1%Qp.
  Proof.
    iIntros (Hin Hsub) "#Hinv Hw".
    iInv "Hinv" as ">Htrue" "Hclose".
    rewrite /interp_local_world /=.
    iDestruct (big_sepS_delete _ _ γ with "Hw") as "[Hγ Hw_rest]"; first done.
    iFrame "Hγ Hw_rest". iIntros "!>". by iApply "Hclose".
  Qed.

  Lemma interp_local_world_acc w E1 E2 F :
    E1 ⊆ E2 →
    ↑localN ⊆ F →
    global_inv -∗
    interp_local_world w E2 ={F}=∗
      interp_local_world w E1 ∗
      (∀ w' F', ⌜w ⊑ w'⌝ -∗
        ⌜↑localN ⊆ F'⌝ -∗
        interp_local_world w' E1 ={F'}=∗
        interp_local_world w' E2).
  Proof.
    iIntros (HEsub Hsub) "#Hinv Hw".
    iInv "Hinv" as ">Htrue" "Hclose".
    iModIntro. iFrame "Hw".
    iSplitL; [done|].
    iIntros (w' F' %Hwsub %HFsub) "Hw'".
    iMod ("Hclose" with "[//]") as "_".
    iModIntro. iFrame "Hw'".
  Qed.

  Lemma interp_local_world_lease w E_ E γ F :
    E_ ⊆ E →
    γ ∈ w.2 →
    γ ∈ E_ →
    ↑localN ⊆ F →
    global_inv -∗
    interp_local_world w E ={F}=∗
      cinv_own γ 1%Qp ∗ interp_local_world w (E ∖ E_) ∗
      (∀ w' E' F', ⌜w ⊑ w'⌝ -∗
        ⌜↑localN ⊆ F'⌝ -∗
        cinv_own γ 1%Qp -∗
        interp_local_world w' E' ={F'}=∗
        interp_local_world w' (E' ∪ E_)).
  Proof.
    iIntros (HEsub Hin HinE Hsub) "#Hinv Hw".
    iInv "Hinv" as ">Htrue" "Hclose".
    rewrite /interp_local_world /=.
    iDestruct (big_sepS_delete _ _ γ with "Hw") as "[Hγ Hw_rest]"; first done.
    iFrame "Hγ Hw_rest".
    iSplitL; [done|].
    iIntros (w' E' F' %Hwsub %HFsub) "Hγ2 Hw'".
    iCombine "Hγ2 Hw'" as "Hw'γ".
    iDestruct (big_sepS_insert_2' with "Hw'γ") as "H".
    { rewrite /Absorbing /Affine. left. apply _. }
    iMod ("Hclose" with "[//]") as "_".
    iModIntro. iFrame "H".
  Qed.

End local_world.
