From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import lifting.
Require Import SnakeletLang.

#[global] Instance snakelet_inhabited_state : Inhabited SnakeletLang.state.
Proof. apply _. Qed.

Lemma reducible_pure_step e e' σ :
  SnakeletLang.pure_step e e' →
  @reducible SnakeletLang.snakelet_lang e σ.
Proof.
  intros Hpure. eexists [], e', σ, [].
  eapply (SnakeletLang.PrimPureStep _ σ). exact Hpure.
Qed.

Lemma reducible_no_obs_pure_step e e' σ :
  SnakeletLang.pure_step e e' →
  @reducible_no_obs SnakeletLang.snakelet_lang e σ.
Proof.
  intros Hpure. eexists e', σ, [].
  eapply (SnakeletLang.PrimPureStep _ σ). exact Hpure.
Qed.

Section wp.
  Context `{!irisGS_gen hlc SnakeletLang.snakelet_lang Σ}.
  Implicit Types v : SnakeletLang.val.
  Implicit Types e : SnakeletLang.expr.
  Implicit Types Φ : SnakeletLang.val → iProp Σ.

  Lemma wp_binop s E op v1 v2 Φ :
    ▷ Φ (SnakeletLang.binop_eval op v1 v2) -∗
    WP SnakeletLang.BinOp op (SnakeletLang.Val v1) (SnakeletLang.Val v2) @ s; E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply wp_lift_pure_step_no_fork; [ | | ].
    - intros σ.
      destruct s.
      + pose proof (reducible_no_obs_pure_step
            (SnakeletLang.BinOp op (SnakeletLang.Val v1) (SnakeletLang.Val v2))
            (SnakeletLang.Val (SnakeletLang.binop_eval op v1 v2)) σ
            (SnakeletLang.PureBinOp op v1 v2)) as Hred.
        apply reducible_no_obs_reducible, Hred.
      + simpl. reflexivity.
    - intros κ σ1 e2 σ2 efs Hprim.
      inversion Hprim as [e0 σ0 e0' Hpure | e0 σ0 e0' σ0' efs0 Hhead]; subst; try inversion Hhead.
      inversion Hpure; subst. split; [done|]. split; [done|]. done.
    - iModIntro. iNext. iModIntro. iIntros (κ e2 efs σ Hprim) "Hcred".
      inversion Hprim as [e0 σ0 e0' Hpure | e0 σ0 e0' σ0' efs0 Hhead]; subst; try inversion Hhead.
      inversion Hpure; subst.
      iDestruct (lc_weaken 1 with "Hcred") as "Hcred"; first done.
      done.
  Qed.

  Lemma wp_let s E x v e2 Φ :
    ▷ WP SnakeletLang.subst x v e2 @ s; E {{ Φ }} -∗
    WP SnakeletLang.Let x (SnakeletLang.Val v) e2 @ s; E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply wp_lift_pure_step_no_fork; [ | | ].
    - intros σ.
      destruct s.
      + pose proof (reducible_no_obs_pure_step
            (SnakeletLang.Let x (SnakeletLang.Val v) e2)
            (SnakeletLang.subst x v e2) σ
            (SnakeletLang.PureLet v x e2)) as Hred.
        apply reducible_no_obs_reducible, Hred.
      + simpl. reflexivity.
    - intros κ σ1 e2' σ2 efs Hprim.
      inversion Hprim as [e0 σ0 e0' Hpure | e0 σ0 e0' σ0' efs0 Hhead]; subst; try inversion Hhead.
      inversion Hpure; subst. split; [done|]. split; [done|]. done.
    - iIntros (κ e2' efs σ Hprim) "Hcred".
      inversion Hprim as [e0 σ0 e0' Hpure | e0 σ0 e0' σ0' efs0 Hhead]; subst; try inversion Hhead.
      inversion Hpure; subst.
      iDestruct (lc_weaken 1 with "Hcred") as "Hcred"; first done.
      iModIntro. iFrame "HΦ".
  Qed.

  Lemma wp_if_true s E e1 e2 Φ :
    ▷ WP e1 @ s; E {{ Φ }} -∗
    WP SnakeletLang.If (SnakeletLang.Val (SnakeletLang.LitBool true)) e1 e2 @ s; E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply wp_lift_pure_step_no_fork; [ | | ].
    - intros σ.
      destruct s.
      + pose proof (reducible_no_obs_pure_step
            (SnakeletLang.If (SnakeletLang.Val (SnakeletLang.LitBool true)) e1 e2)
            e1 σ
            (SnakeletLang.PureIfTrue e1 e2)) as Hred.
        apply reducible_no_obs_reducible, Hred.
      + simpl. reflexivity.
    - intros κ σ1 e2' σ2 efs Hprim.
      inversion Hprim as [e0 σ0 e0' Hpure | e0 σ0 e0' σ0' efs0 Hhead]; subst; try inversion Hhead.
      inversion Hpure; subst. split; [done|]. split; [done|]. done.
    - iIntros (κ e2' efs σ Hprim) "Hcred".
      inversion Hprim as [e0 σ0 e0' Hpure | e0 σ0 e0' σ0' efs0 Hhead]; subst; try inversion Hhead.
      inversion Hpure; subst.
      iDestruct (lc_weaken 1 with "Hcred") as "Hcred"; first done.
      iModIntro. iFrame "HΦ".
  Qed.

  Lemma wp_if_false s E e1 e2 Φ :
    ▷ WP e2 @ s; E {{ Φ }} -∗
    WP SnakeletLang.If (SnakeletLang.Val (SnakeletLang.LitBool false)) e1 e2 @ s; E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply wp_lift_pure_step_no_fork; [ | | ].
    - intros σ.
      destruct s.
      + pose proof (reducible_no_obs_pure_step
            (SnakeletLang.If (SnakeletLang.Val (SnakeletLang.LitBool false)) e1 e2)
            e2 σ
            (SnakeletLang.PureIfFalse e1 e2)) as Hred.
        apply reducible_no_obs_reducible, Hred.
      + simpl. reflexivity.
    - intros κ σ1 e2' σ2 efs Hprim.
      inversion Hprim as [e0 σ0 e0' Hpure | e0 σ0 e0' σ0' efs0 Hhead]; subst; try inversion Hhead.
      inversion Hpure; subst. split; [done|]. split; [done|]. done.
    - iIntros (κ e2' efs σ Hprim) "Hcred".
      inversion Hprim as [e0 σ0 e0' Hpure | e0 σ0 e0' σ0' efs0 Hhead]; subst; try inversion Hhead.
      inversion Hpure; subst.
      iDestruct (lc_weaken 1 with "Hcred") as "Hcred"; first done.
      iModIntro. iFrame "HΦ".
  Qed.

End wp.
