From fae_gtlc_mu.refinements.gradual_static Require Export compat_cast.defs.
From fae_gtlc_mu.backtranslation Require Export general_def_lemmas.
From fae_gtlc_mu.stlc_mu Require Export lang.
From fae_gtlc_mu.cast_calculus Require Export types.

Section compat_cast_prod_prod.
  Context `{!implG Σ,!specG Σ}.
  Local Hint Resolve to_of_val : core.

  Hint Extern 5 (AsVal _) => eexists; simpl; try done; eapply cast_calculus.lang.of_to_val; fast_done : typeclass_instances.

  Lemma back_cast_ar_prod_prod:
    ∀ (A : list (type * type)) (τ1 τ1' τ2 τ2' : type) (pC1 : alternative_consistency A τ1 τ1') (pC2 : alternative_consistency A τ2 τ2')
      (IHpC1 : back_cast_ar pC1) (IHpC2 : back_cast_ar pC2),
      back_cast_ar (throughProd A τ1 τ1' τ2 τ2' pC1 pC2).
  Proof.
    intros A τ1 τ1' τ2 τ2' pC1 pC2 IHpC1 IHpC2.
    rewrite /back_cast_ar. iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    iDestruct "Hfs" as "[% Hfs']"; iAssert (rel_cast_functions A fs) with "[Hfs']" as "Hfs". iSplit; done. iClear "Hfs'".
    rewrite /𝓕c /𝓕. fold (𝓕 pC1) (𝓕 pC2). rewrite between_TProd_subst_rewrite. fold (𝓕c pC1 fs) (𝓕c pC2 fs).
    rewrite interp_rw_TProd.
    iDestruct "Hvv'" as ((v1, v1') (v2, v2')) "(% & #H1 & #H2)". simpl in H0. inversion H0. clear H0 H2 H3 v v'.
    (** impl side *)
    wp_head. fold (cast_calculus.lang.of_val v1). fold (cast_calculus.lang.of_val v2).
    iApply (wp_bind [CastCtx _ _ ; cast_calculus.lang.PairLCtx _]). wp_value. simpl.
    (** spec side *)
    rewrite /between_TProd.
    assert (Pair (of_val v1') (of_val v2') = of_val (PairV v1' v2')) as ->. by simpl.
    iMod ((step_lam _ ei' K') with "[Hv']") as "Hv'"; auto. asimpl.
    rewrite 𝓕c_rewrite.
    iMod ((step_fst _ ei' (AppRCtx _ :: PairLCtx _ :: K')) with "[Hv']") as "Hv'"; auto. simpl.
    rewrite -𝓕c_rewrite.
    (** first IH *)
    iApply (wp_bind [cast_calculus.lang.PairLCtx _ ]). iApply (wp_wand with "[-]").
    iApply (IHpC1 ei' (PairLCtx _ :: K') with "[Hv' Hfs]"). auto.
    (** .... *)
    iIntros (v1f) "HHH". iDestruct "HHH" as (v1f') "[Hv2' #Hv1fv1f']". simpl.
    (** impl side *)
    iApply (wp_bind [CastCtx _ _ ; cast_calculus.lang.PairRCtx _]). wp_value. simpl.
    (** spec side *)
    rewrite 𝓕c_rewrite.
    iMod ((step_snd _ ei' (AppRCtx _ :: PairRCtx _ :: K')) with "[Hv2']") as "Hv2'"; auto. simpl.
    rewrite -𝓕c_rewrite.
    (** second IH *)
    iApply (wp_bind [cast_calculus.lang.PairRCtx _]). iApply (wp_wand with "[-]").
    iApply (IHpC2 ei' (PairRCtx _ :: K') with "[Hv2' Hfs]"). auto.
    (** .... *)
    iIntros (v2f) "HHH". iDestruct "HHH" as (v2f') "[Hvf #Hv2fv2f']". simpl.
    wp_value.
    iExists (PairV v1f' v2f'). iSplitL. done.
    rewrite interp_rw_TProd.
    iExists (v1f , v1f') , (v2f , v2f') . auto.
Qed.

End compat_cast_prod_prod.
