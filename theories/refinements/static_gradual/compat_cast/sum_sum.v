From fae_gtlc_mu.refinements.static_gradual Require Export compat_cast.defs.
From fae_gtlc_mu.cast_calculus Require Export lang.

Section compat_cast_sum_sum.
  Context `{!implG Σ,!specG Σ}.

  Local Hint Resolve to_of_val : core.

  Lemma back_cast_ar_sum_sum:
    ∀ (A : list (type * type)) (τ1 τ1' τ2 τ2' : type) (pC1 : alternative_consistency A τ1 τ1') (pC2 : alternative_consistency A τ2 τ2')
      (IHpC1 : back_cast_ar pC1) (IHpC2 : back_cast_ar pC2),
      back_cast_ar (throughSum A τ1 τ1' τ2 τ2' pC1 pC2).
  Proof.
    intros A τ1 τ1' τ2 τ2' pC1 pC2 IHpC1 IHpC2.
    rewrite /back_cast_ar. iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    iDestruct "Hfs" as "[% Hfs']"; iAssert (rel_cast_functions A fs) with "[Hfs']" as "Hfs". iSplit; done. iClear "Hfs'".
    rewrite /𝓕c /𝓕. fold (𝓕 pC1) (𝓕 pC2). rewrite between_TSum_subst_rewrite.
    wp_head.
    asimpl.
    rewrite interp_rw_TSum.
    iDestruct "Hvv'" as "[H1 | H2]".
    + iDestruct "H1" as ((v1 , v1')) "[% Hv1v1']". inversion H0. clear H0 H2 H3 v v'.
      iMod (step_pure _ ei' K' _ (InjL (Cast v1' τ1 τ1')) with "[Hv']") as "Hv'". eapply SumCast1. eauto. eauto. eauto.
      wp_head. asimpl. fold (stlc_mu.lang.of_val v1).
      iApply (wp_bind (stlc_mu.lang.fill_item stlc_mu.lang.InjLCtx)).
      iApply (wp_wand with "[-]").
      iApply (IHpC1 ei' (InjLCtx :: K') with "[Hv']").
      eauto.
      iIntros (v1f) "HHH". iDestruct "HHH" as (v1f') "[Hv1f' Hv1fv1f']".
      iApply wp_value.
      iExists (InjLV v1f').
      iSplitL "Hv1f'". done.
      rewrite interp_rw_TSum.
      iLeft. iExists (v1f , v1f'). by iFrame.
    + iDestruct "H2" as ((v2 , v2')) "[% Hv2v2']". inversion H0. clear H0 H2 H3 v v'.
      iMod (step_pure _ ei' K' _ (InjR (Cast v2' τ2 τ2')) with "[Hv']") as "Hv'". by eapply SumCast2; eauto. eauto. eauto.
      wp_head. asimpl. fold (stlc_mu.lang.of_val v2).
      iApply (wp_bind (stlc_mu.lang.fill_item stlc_mu.lang.InjRCtx)).
      iApply (wp_wand with "[-]").
      iApply (IHpC2 ei' (InjRCtx :: K') with "[Hv']").
      eauto.
      iIntros (v1f) "HHH". iDestruct "HHH" as (v1f') "[Hv1f' Hv1fv1f']".
      iApply wp_value.
      iExists (InjRV v1f').
      iSplitL "Hv1f'". done.
      rewrite interp_rw_TSum.
      iRight. iExists (v1f , v1f'). eauto.
  Qed.

End compat_cast_sum_sum.
