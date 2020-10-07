From fae_gtlc_mu.refinements.gradual_static Require Export logical_relation compat_cast.defs compat_easy.
From fae_gtlc_mu.refinements.gradual_static.compat_cast Require Export
     between_rec prod_prod sum_sum arrow_arrow identity tau_star ground_star tau_star star_tau star_ground.

Section compat_cast_all.
  Context `{!implG Σ,!specG Σ}.

  Lemma back_cast_ar_all {A} {τi τf} (pC : alternative_consistency A τi τf) : back_cast_ar pC.
  Proof.
    induction pC; eauto using back_cast_ar_star_ground, back_cast_ar_ground_star, back_cast_ar_tau_star, back_cast_ar_star_tau, back_cast_ar_base_base, back_cast_ar_star_star, back_cast_ar_sum_sum, back_cast_ar_prod_prod, back_cast_ar_arrow_arrow, back_cast_ar_trec_trec_expose, back_cast_ar_trec_trec_use.
  Qed.

  Notation "'` H" := (bin_log_related_alt H) (at level 8).

  Lemma bin_log_related_back_cast Γ e e' τi τf (pC : alternative_consistency [] τi τf)
      (IHHtyped : Γ ⊨ e ≤log≤ e' : τi) :
    Γ ⊨ Cast e τi τf ≤log≤ 𝓕c pC [] e' : τf.
  Proof.
    iIntros (vvs ei) "#[Hρ HΓ]"; iIntros (K) "Hj /=".
    rewrite 𝓕c_closed; try auto.
    rewrite 𝓕c_rewrite.
    iApply (wp_bind [CastCtx _ _]). iApply (wp_wand with "[-]").
    iApply ('`IHHtyped _ _ (AppRCtx _ :: K)). auto.
    iIntros (v). iDestruct 1 as (v') "[Hv' Hvv']". simpl.
    rewrite -𝓕c_rewrite.
    iApply (wp_wand with "[-]").
    iApply ((back_cast_ar_all pC) with "[-]").
    iSplitR; auto. unfold rel_cast_functions. by iSplit; auto.
    clear v v'.
    iIntros (v). iDestruct 1 as (v') "[Hv' Hvv']".
    iExists v'.
    auto.
  Qed.

  Lemma bin_log_related_omega Γ e' τ :
    Γ ⊨ CastError ≤log≤ e' : τ.
  Proof.
    iIntros (vvs ρ) "#[Hρ HΓ]"; iIntros (K) "Hj /=".
    by iApply wp_CastError'.
  Qed.

End compat_cast_all.
