From iris.program_logic Require Export weakestpre.
From fae_gtlc_mu.cast_calculus Require Export lang.

Class implG Σ := ImplG {
  implG_invG : invG Σ;
}.

Instance implG_irisG `{implG Σ} : irisG lang Σ := {
  iris_invG := implG_invG;
  state_interp σ κs _ := True%I;
  fork_post _ := True%I;
}.
Global Opaque iris_invG.

From iris.program_logic Require Export ectx_lifting.
From iris.proofmode Require Export tactics.
From fae_gtlc_mu.cast_calculus Require Export lang_lemmas.

Section wps.
  Context `{implG Σ}.
  Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _, _; simpl : core.

  Local Hint Constructors head_step : core.
  Local Hint Resolve to_of_val : core.

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



  Global Instance pure_lam e1 e2 `{!AsVal e2} :
    PureExec True 1 (App (Lam e1) e2) e1.[e2 /].
  Proof.
    intros _. apply nsteps_once. apply prim_step_pure.
    destruct AsVal0 as [??];subst.
    eapply (Ectx_step []); eauto.
  Qed.

  Global Instance pure_fold e `{!AsVal e}:
    PureExec True 1 (Unfold (Fold e)) e.
  Proof.
    intros _. apply nsteps_once. apply prim_step_pure.
    destruct AsVal0 as [??];subst.
    eapply (Ectx_step []); eauto.
  Qed.

  Global Instance pure_fst e1 e2 `{!AsVal e1, !AsVal e2} :
    PureExec True 1 (Fst (Pair e1 e2)) e1.
  Proof.
    intros _. apply nsteps_once. apply prim_step_pure.
    destruct AsVal0 as [??];subst.
    destruct AsVal1 as [??];subst.
    eapply (Ectx_step []); eauto.
  Qed.
  Proof.

  Global Instance pure_snd e1 e2 `{!AsVal e1, !AsVal e2} :
    PureExec True 1 (Snd (Pair e1 e2)) e2.
  Proof.
    intros _. apply nsteps_once. apply prim_step_pure.
    destruct AsVal0 as [??];subst.
    destruct AsVal1 as [??];subst.
    eapply (Ectx_step []); eauto.
  Qed.

  Global Instance pure_case_inl e0 e1 e2 `{!AsVal e0}:
    PureExec True 1 (Case (InjL e0) e1 e2) e1.[e0/].
  Proof.
    intros _. apply nsteps_once. apply prim_step_pure.
    destruct AsVal0 as [??];subst.
    eapply (Ectx_step []); eauto.
  Qed.

  Global Instance pure_case_inr e0 e1 e2 `{!AsVal e0}:
    PureExec True 1 (Case (InjR e0) e1 e2) e2.[e0/].
  Proof.
    intros _. apply nsteps_once. apply prim_step_pure.
    destruct AsVal0 as [??];subst.
    eapply (Ectx_step []); eauto.
  Qed.

  Global Instance pure_cast_between_sum1 e1 τ1 τ2 τ1' τ2' `{!AsVal e1}:
    PureExec True 1 (Cast (InjL e1) (TSum τ1 τ2) (TSum τ1' τ2')) (InjL (Cast e1 τ1 τ1')).
  Proof.
    intros _. apply nsteps_once. apply prim_step_pure.
    destruct AsVal0 as [??];subst.
    eapply (Ectx_step []); eauto.
  Qed.

  Global Instance pure_cast_between_sum2 e2 τ1 τ2 τ1' τ2' `{!AsVal e2}:
    PureExec True 1 (Cast (InjR e2) (TSum τ1 τ2) (TSum τ1' τ2')) (InjR (Cast e2 τ2 τ2')).
  Proof.
    intros _. apply nsteps_once. apply prim_step_pure.
    destruct AsVal0 as [??];subst.
    eapply (Ectx_step []); eauto.
  Qed.

  Global Instance pure_cast_between_rec e τl τr `{!AsVal e}:
    PureExec True 1 (Cast (Fold e) (TRec τl) (TRec τr))
             (Fold (Cast e τl.[TRec τl/] τr.[TRec τr/])).
  Proof.
    intros _. apply nsteps_once. apply prim_step_pure.
    destruct AsVal0 as [??];subst.
    eapply (Ectx_step []); eauto.
  Qed.

  Global Instance pure_app_cast f e2 τ1 τ2 τ1' τ2' `{!AsVal f,!AsVal e2} :
    PureExec True 1 (App (Cast f (TArrow τ1 τ2) (TArrow τ1' τ2')) e2) (Cast (App f (Cast e2 τ1' τ1)) τ2 τ2').
  Proof.
    intros _. apply nsteps_once. apply prim_step_pure.
    destruct AsVal0 as [??];subst.
    destruct AsVal1 as [??];subst.
    eapply (Ectx_step []); eauto.
  Qed.

  Global Instance pure_same_ground e τ `{!AsVal e, !Ground τ} :
    PureExec True 1 (Cast (Cast e τ ⋆) ⋆ τ) e.
  Proof.
    intros _. apply nsteps_once. apply prim_step_pure.
    destruct AsVal0 as [??];subst.
    eapply (Ectx_step []); eauto.
  Qed.

  Global Instance pure_different_ground e τ τ' (neq : τ ≠ τ') `{!AsVal e, !Ground τ, !Ground τ'} :
    PureExec True 1 (Cast (Cast e τ ⋆) ⋆ τ') CastError.
  Proof.
    intros _. apply nsteps_once. apply prim_step_pure.
    destruct AsVal0 as [??];subst.
    eapply (Ectx_step []); eauto.
  Qed.

  Lemma pure_fact_up e τ τG (neq : τ ≠ ⋆) (nG : Ground τ → False) (G : get_shape τ = Some τG) `{!AsVal e} :
    PureExec True 1 (Cast e τ ⋆) (Cast (Cast e τ τG) τG ⋆).
  Proof.
    intros _. apply nsteps_once. apply prim_step_pure.
    destruct AsVal0 as [??];subst.
    eapply (Ectx_step []); eauto.
  Qed.

  Lemma pure_fact_down e τ τG (neq : τ ≠ ⋆) (nG : Ground τ → False) (G : get_shape τ = Some τG) `{!AsVal e} :
    PureExec True 1 (Cast e ⋆ τ) (Cast (Cast e ⋆ τG) τG τ).
  Proof.
    intros _. apply nsteps_once. apply prim_step_pure.
    destruct AsVal0 as [??];subst.
    eapply (Ectx_step []); eauto.
  Qed.

  Global Instance pure_cast_pair e1 e2 τ1 τ2 τ1' τ2' `{!AsVal e1, !AsVal e2} :
    PureExec True 1 (Cast (Pair e1 e2) (TProd τ1 τ2) (TProd τ1' τ2')) (Pair (Cast e1 τ1 τ1') (Cast e2 τ2 τ2')).
  Proof.
    intros _. apply nsteps_once. apply prim_step_pure.
    destruct AsVal0 as [??];subst.
    destruct AsVal1 as [??];subst.
    eapply (Ectx_step []); eauto.
  Qed.

  Global Instance pure_cast_tunit_tunit e  `{!AsVal e} :
    PureExec True 1 (Cast e TUnit TUnit) e.
  Proof.
    intros _. apply nsteps_once. apply prim_step_pure.
    destruct AsVal0 as [??];subst.
    eapply (Ectx_step []); eauto.
  Qed.

  Global Instance pure_cast_tunk_tunk e  `{!AsVal e} :
    PureExec True 1 (Cast e ⋆ ⋆) e.
  Proof.
    intros _. apply nsteps_once. apply prim_step_pure.
    destruct AsVal0 as [??];subst.
    eapply (Ectx_step []); eauto.
  Qed.

End wps.

Ltac wp_head := iApply wp_pure_step_later; auto; iNext.
Ltac wp_value := iApply wp_value.

