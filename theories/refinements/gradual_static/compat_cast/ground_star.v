From fae_gtlc_mu.refinements.gradual_static Require Export compat_cast.defs.
From fae_gtlc_mu.backtranslation Require Export general_def_lemmas.
From fae_gtlc_mu.stlc_mu Require Export lang.
From fae_gtlc_mu.cast_calculus Require Import types_notations.
From fae_gtlc_mu.cast_calculus Require Export types.

Section ground_star.
  Context `{!implG Σ,!specG Σ}.

  Hint Extern 5 (AsVal _) => eexists; simpl; try done; eapply cast_calculus.lang.of_to_val; fast_done : typeclass_instances.

  Lemma back_cast_ar_ground_star:
    ∀ (A : list (type * type)) (τG : type) (G : Ground τG), back_cast_ar (atomic_Ground_Unknown A τG G).
  Proof.
    intros A τG G.
    rewrite /back_cast_ar /𝓕c /𝓕. iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')". rewrite embed_no_subs.
    destruct G; rewrite /𝓕c /𝓕.
    + iMod ((step_lam _ ei' K') with "[Hv']") as "Hv'"; auto. simpl.
      wp_value. iExists (embedV_TUnit v'); iFrame.
      rewrite interp_rw_TUnknown.
      iExists _  , _.
      iModIntro. iLeft; auto.
    + iMod ((step_lam _ ei' K') with "[Hv']") as "Hv'"; auto. simpl.
      iApply (wp_value _ _ _ _ (CastV v (TProd ⋆ ⋆) ⋆ (TGround_TUnknown_icp (Ground_TProd)))); try by simpl.
      iExists (embedV_Ground_TProd v'); iFrame.
      rewrite interp_rw_TUnknown.
      iExists _ , _.
      iModIntro. iRight. iLeft. iSplit; done.
    + iMod ((step_lam _ ei' K') with "[Hv']") as "Hv'"; auto. simpl.
      iApply (wp_value _ _ _ _ (CastV v (TSum ⋆ ⋆) ⋆ (TGround_TUnknown_icp (Ground_TSum)))); try by simpl.
      iExists (embedV_Ground_TSum v'); iFrame.
      rewrite interp_rw_TUnknown.
      iExists _ , _.
      iModIntro. iRight. iRight. iLeft.
      iSplit; auto.
    + iMod ((step_lam _ ei' K') with "[Hv']") as "Hv'"; auto. simpl.
      iApply (wp_value _ _ _ _ (CastV v (TArrow ⋆ ⋆) ⋆ (TGround_TUnknown_icp (Ground_TArrow)))); try by simpl.
      iExists (embedV_Ground_TArrow v'); iFrame.
      rewrite interp_rw_TUnknown.
      iExists _ , _.
      iModIntro. iRight. iRight. iRight. iLeft. iSplitL; done.
    + iMod ((step_lam _ ei' K') with "[Hv']") as "Hv'"; auto. simpl.
      rewrite interp_rw_TRec.
      iDestruct "Hvv'" as (u u') "#[% Huu']". inversion H. clear v v' H H1 H2. simpl.
      iMod ((step_Fold _ ei' (InjRCtx :: FoldCtx :: K')) with "[Hv']") as "Hv'"; auto.
      iApply (wp_value _ _ _ _ (CastV (cast_calculus.lang.FoldV u) (TRec ⋆) ⋆ (TGround_TUnknown_icp (Ground_TRec)))); try by simpl.
      iExists (embedV_TUnknown u'). iFrame "Hv'".
      rewrite (interp_rw_TUnknown (CastV (cast_calculus.lang.FoldV u) (TRec ⋆) ⋆ (TGround_TUnknown_icp Ground_TRec), embedV_TUnknown u')).
      iExists _ , _.
      iModIntro. iRight. iRight. iRight. iRight. iSplit; done.
  Qed.

End ground_star.
