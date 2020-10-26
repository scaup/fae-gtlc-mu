From iris.program_logic Require Export weakestpre.
From fae_gtlc_mu.cast_calculus Require Export lang lang_lemmas.
From fae_gtlc_mu.cast_calculus Require Import types_notations.

(* Iris resources for invariants *)
Class implG Σ := ImplG {
  implG_invG : invG Σ;
}.

(* Iris resources gradual side for weakest preconditions... *)
Instance implG_irisG `{implG Σ} : irisG lang Σ := {
  iris_invG := implG_invG;
  state_interp σ κs _ := True%I;
  fork_post _ := True%I;
}.
Global Opaque iris_invG.

From iris.program_logic Require Export ectx_lifting.
From iris.proofmode Require Export tactics.
From fae_gtlc_mu.cast_calculus Require Export lang_lemmas.

(* some WP lemmas *)
Section wps.
  Context `{implG Σ}.

  Lemma wp_CastError' E Φ :
    ⊢ WP CastError @ MaybeStuck; E {{Φ}}.
  Proof. simpl. iApply wp_lift_pure_stuck. intro σ. destruct σ. exact CastError_stuck. done. Qed.

  Lemma wp_CastError (K : ectx) E Φ :
    ⊢ WP fill K CastError @ MaybeStuck; E {{Φ}}.
  Proof.
    destruct K.
    - by iApply wp_CastError'.
    - iApply (wp_pure_step_later MaybeStuck _ _ CastError True 1 _).
      intros _. apply nsteps_once. by apply cast_error_step. done.
      iApply wp_lift_pure_stuck. intro σ. destruct σ. exact CastError_stuck. done.
  Qed.

  (* a bind lemma for WP *)
  Lemma wp_bind (K : ectx) E e Φ :
    WP e @ MaybeStuck; E {{ v, WP fill K (of_val v) @ MaybeStuck; E {{ Φ }} }} ⊢ WP fill K e @ MaybeStuck; E {{ Φ }}.
  Proof.
    destruct (decide (e = CastError)) as [-> | eNeqCE].
    { iIntros "_". iApply wp_CastError. }
    iIntros "H". iLöb as "IH" forall (E e eNeqCE Φ). rewrite wp_unfold /wp_pre.
    assert (language.to_val e = to_val e) as ->; first done.
    destruct (to_val e) as [v|] eqn:He.
    { apply of_to_val in He as <-. by iApply fupd_wp. }
    rewrite wp_unfold /wp_pre.
    assert (language.to_val (fill K  e) = to_val (fill K e)) as ->; first done.
    rewrite fill_not_val //.
    iIntros (σ1 κ κs n) "Hσ". iMod ("H" $! tt [] [] 0 with "[$]") as "[% H]". iModIntro; iSplit.
    { eauto using reducible_fill. }
    iIntros (e2 σ2 efs Hstep).
    destruct (decide (e2 = CastError)).
    - rewrite e0.
      iMod ("H" $! CastError σ2 efs with "[]") as "H".
      simpl. iPureIntro. cut (prim_step e [] CastError []). inversion Hstep; done.
      { assert (prim_step (fill K e) [] e2 []). inversion Hstep; simplify_eq; by econstructor. eapply fill_step_CastError_inv; eauto. by simplify_eq. }
      iIntros "!>!>".
      iMod "H" as "(Hσ' & H & Hefs)".
      iModIntro. iFrame "Hσ Hefs". assert (CastError = fill [] CastError) as ->. done. iApply wp_CastError.
    - destruct (fill_step_inv K e κ e2 efs) as (e2'&->&?); auto.
      iMod ("H" $! e2' σ2 efs with "[]") as "H".
      simpl. inversion H1; by simplify_eq.
      iIntros "!>!>".
      iMod "H" as "(Hσ' & H & Hefs)".
      iModIntro. iFrame "Hσ Hefs".
      destruct K as [|Ki K]. simpl. iApply wp_fupd. iApply (wp_wand with "H"). iIntros (v) "Hwpv". iMod (wp_value_inv with "Hwpv"). by iModIntro.
      destruct (decide (e2' = CastError)) as [-> | neq]. iApply wp_CastError.
      by iApply "IH".
  Qed.

End wps.

Ltac wp_head := iApply wp_pure_step_later; auto; iNext.
Ltac wp_value := iApply wp_value.
