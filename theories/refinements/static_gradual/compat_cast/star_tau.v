From fae_gtlc_mu.refinements.static_gradual Require Export compat_cast.defs.
From fae_gtlc_mu.backtranslation Require Export general_def_lemmas.
From fae_gtlc_mu.cast_calculus Require Export lang.

Section compat_cast_star_tau.
  Context `{!implG Σ,!specG Σ}.
  Local Hint Resolve to_of_val : core.

  Lemma back_cast_ar_star_tau:
    ∀ (A : list (type * type)) (τ τG : type) (pτnG : Ground τ → False) (pτnStar : τ ≠ ⋆) (pτSτG : get_shape τ = Some τG) (pC1 : alternative_consistency A ⋆ τG) (pC2 : alternative_consistency A τG τ),
      back_cast_ar pC1 → back_cast_ar pC2 → back_cast_ar (factorDown_Ground A τ τG pτnG pτnStar pτSτG pC1 pC2).
  Proof.
    intros A τ τG pτnG pτnStar pτSτG pC1 pC2 IHpC1 IHpC2.
    rewrite /back_cast_ar /𝓕c /𝓕. fold (𝓕 pC1). fold (𝓕 pC2).
    iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    (* get small lemma about length fs *)
    iDestruct "Hfs" as "[% Hfs']"; iAssert (rel_cast_functions A fs) with "[Hfs']" as "Hfs". iSplit; done. iClear "Hfs'".
    (* step in wp *)
    wp_head. asimpl.
    fold (𝓕c pC1 fs). fold (𝓕c pC2 fs). do 2 rewrite 𝓕c_rewrite.
    (* step in gradual side *)
    iMod (step_pure _ ei' K'
                    (Cast v' ⋆ τ)
                    (Cast (Cast v' ⋆ τG) τG τ) with "[Hv']") as "Hv'"; auto.
    { eapply DownFactorization; auto. }
    (* apply first IH *)
    iApply (wp_bind (ectx_language.fill $ [stlc_mu.lang.AppRCtx _])).
    iApply (wp_wand with "[-]").
    rewrite -𝓕c_rewrite.
    iApply (IHpC1 ei' (CastCtx τG τ :: K') with "[Hv']"); auto.
    iIntros (w) "blaa". iDestruct "blaa" as (w') "[Hw' #Hww']".
    simpl.
    rewrite -𝓕c_rewrite.
    (* apply second IH *)
    iApply (IHpC2 ei' K' with "[Hw']"); auto.
  Qed.

End compat_cast_star_tau.
