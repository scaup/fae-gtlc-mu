From iris.program_logic Require Export weakestpre.
From fae_gtlc_mu.stlc_mu Require Export lang.

Class implG Σ := ImplG {
  implG_invG : invG Σ;
}.

Instance implG_irisG `{implG Σ} : irisG lang Σ := {
  iris_invG := implG_invG;
  state_interp σ κs _ := True%I;
  fork_post _ := True%I;
}.
Global Opaque iris_invG.

From fae_gtlc_mu.stlc_mu Require Export lang_lemmas.
From fae_gtlc_mu.backtranslation Require Import extract.
From iris.program_logic Require Export ectx_lifting.
From iris.proofmode Require Export tactics.

Section wp_omega.

  Context `{!implG Σ}.

  Lemma wp_Ω Φ : ⊢ (True -∗ (WP Ω {{ Φ }}))%I.
  Proof.
    iIntros.
    iLöb as "IH".
    iApply wp_pure_step_later; auto; iNext; asimpl.
    iApply (wp_bind $ stlc_mu.lang.fill_item $ stlc_mu.lang.AppLCtx _).
    iApply wp_pure_step_later; auto.
    iNext.
    iApply wp_value.
    fold Ω. done.
  Qed.

End wp_omega.

Ltac wp_head := iApply wp_pure_step_later; auto; iNext.
Ltac wp_value := iApply wp_value.
