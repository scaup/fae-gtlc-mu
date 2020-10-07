From fae_gtlc_mu.refinements.static_gradual Require Export compat_cast.defs.
From fae_gtlc_mu.backtranslation Require Export general_def_lemmas.
From fae_gtlc_mu.cast_calculus Require Export lang.

Section compat_cast_tau_star.
  Context `{!implG Σ,!specG Σ}.
  Local Hint Resolve to_of_val : core.

  Lemma back_cast_ar_tau_star:
    ∀ (A : list (type * type)) (τ τG : type) (pτnG : Ground τ → False) (pτnStar : τ ≠ ⋆) (pτSτG : get_shape τ = Some τG) (pC1 : alternative_consistency A τ τG) (pC2 : alternative_consistency A τG ⋆),
      back_cast_ar pC1 → back_cast_ar pC2 → back_cast_ar (factorUp_Ground A τ τG pτnG pτnStar pτSτG pC1 pC2).
  Proof.
    intros A τ τG pτnG pτnStar pτSτG pC1 pC2 IHpC1 IHpC2.
    rewrite /back_cast_ar /𝓕c /𝓕. fold (𝓕 pC1). fold (𝓕 pC2).
    iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    iDestruct "Hfs" as "[% Hfs']"; iAssert (rel_cast_functions A fs) with "[Hfs']" as "Hfs". iSplit; done. iClear "Hfs'".
    wp_head. asimpl.
    fold (𝓕c pC1 fs). fold (𝓕c pC2 fs). do 2 rewrite 𝓕c_rewrite.
    iApply (wp_bind (ectx_language.fill $ [stlc_mu.lang.AppRCtx _])).
    iApply (wp_wand with "[-]").
    iMod (step_pure _ ei' K'
                    (Cast (# v') τ ⋆)
                    (Cast (Cast (# v') τ τG) τG ⋆) with "[Hv']") as "Hv'"; auto.
    { eapply UpFactorization; auto. }
    rewrite -𝓕c_rewrite.
    iApply (IHpC1 ei' (CastCtx τG ⋆ :: K') with "[Hv']"); auto.
    iIntros (w) "blaa".  iDestruct "blaa" as (w') "[Hw' #Hww']".
    simpl.
    rewrite -𝓕c_rewrite.
    iApply (IHpC2 ei' K' with "[Hw']"); auto.
  Qed.

End compat_cast_tau_star.
