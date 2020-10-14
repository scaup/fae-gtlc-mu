From fae_gtlc_mu.refinements.gradual_static Require Export compat_cast.defs.
From fae_gtlc_mu.backtranslation Require Export general_def_lemmas.
From fae_gtlc_mu.cast_calculus Require Import types_notations.
From fae_gtlc_mu.cast_calculus Require Export types.
From fae_gtlc_mu.stlc_mu Require Export lang.


Section compat_cast_tau_star.
  Context `{!implG Σ,!specG Σ}.

  Hint Extern 5 (AsVal _) => eexists; simpl; try done; eapply cast_calculus.lang.of_to_val; fast_done : typeclass_instances.

  Lemma back_cast_ar_tau_star:
    ∀ (A : list (type * type)) (τ τG : type) (pτnG : Ground τ → False) (pτnStar : τ ≠ ⋆) (pτSτG : get_shape τ = Some τG) (pC1 : alternative_consistency A τ τG) (pC2 : alternative_consistency A τG ⋆),
      back_cast_ar pC1 → back_cast_ar pC2 → back_cast_ar (factorUp_Ground A τ τG pτnG pτnStar pτSτG pC1 pC2).
  Proof.
    intros A τ τG pτnG pτnStar pτSτG pC1 pC2 IHpC1 IHpC2.
    iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    rewrite /back_cast_ar /𝓕c /𝓕. rewrite factorization_subst_rewrite. fold (𝓕 pC1). fold (𝓕 pC2).
    fold (𝓕c pC1 fs). fold (𝓕c pC2 fs). rewrite /factorization.
    iDestruct "Hfs" as "[% Hfs']"; iAssert (rel_cast_functions A fs) with "[Hfs']" as "Hfs". iSplit; done. iClear "Hfs'".
    (** implementation *)
    iApply wp_pure_step_later; try auto. apply pure_fact_up; auto. done. by eauto; eexists. simpl. done. iNext.
    (** specification *)
    iMod ((step_lam _ ei' K') with "[Hv']") as "Hv'"; auto. asimpl.
    (** first IH *)
    rewrite 𝓕c_rewrite.
    iApply (wp_bind [CastCtx _ _]). iApply (wp_wand with "[-]").
    iApply (IHpC1 ei' (AppRCtx _ :: K') with "[Hv']"); auto.
    (** .... *)
    iIntros (w) "blaa".  iDestruct "blaa" as (w') "[Hw' #Hww']".
    simpl. rewrite -𝓕c_rewrite.
    (** second IH *)
    iApply (wp_wand with "[-]").
    iApply (IHpC2 ei' K' with "[Hw']"); auto.
    auto.
  Qed.

End compat_cast_tau_star.
