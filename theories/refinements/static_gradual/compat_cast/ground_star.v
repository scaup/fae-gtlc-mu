From fae_gtlc_mu.refinements.static_gradual Require Export compat_cast.defs.
From fae_gtlc_mu.cast_calculus Require Export lang.

Section ground_star.
  Context `{!implG Σ,!specG Σ}.

  Lemma back_cast_ar_ground_star:
    ∀ (A : list (type * type)) (τG : type) (G : Ground τG), back_cast_ar (atomic_Ground_Unknown A τG G).
  Proof.
    intros A τG G.
    rewrite /back_cast_ar /𝓕c /𝓕. iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')". rewrite embed_no_subs.
    destruct G; rewrite /𝓕c /𝓕.
      + wp_head. asimpl. wp_value.
        iExists (CastV v' _ _ (TGround_TUnknown_icp Ground_TUnit)). iSplitL. done.
        rewrite interp_rw_TUnknown. iExists _, _.
        iLeft. iModIntro. iSplit; done.
      + wp_head. asimpl. wp_value.
        iExists (CastV v' _ _ (TGround_TUnknown_icp Ground_TProd)). iSplitL. done.
        rewrite interp_rw_TUnknown.
        iExists _  , _.
        iModIntro. iRight. iLeft. iSplit; done.
      + wp_head. asimpl. wp_value.
        iExists (CastV v' _ _ (TGround_TUnknown_icp Ground_TSum)).
        iSplitL. done.
        (* rewrite unfold_fixpoint_interp_unknown1'. *)
        rewrite interp_rw_TUnknown.
        iExists v, v'.
        iModIntro. iRight. iRight. iLeft.
        iSplit; auto.
      + wp_head. asimpl. wp_value.
        iExists (CastV v' _ _ (TGround_TUnknown_icp Ground_TArrow)). iSplitL. done.
        rewrite interp_rw_TUnknown.
        iExists _ , _.
        iModIntro. iRight. iRight. iRight. iLeft. iSplitL; done.
      + wp_head. asimpl.
        (** rewriting value relation for v and v' *)
        rewrite interp_rw_TRec.
        iDestruct "Hvv'" as (u u') "#[% Huu']". inversion H. clear v v' H H1 H2.
        iApply (wp_bind (ectx_language.fill $ [stlc_mu.lang.InjRCtx ; stlc_mu.lang.FoldCtx])).
        wp_head. wp_value. simpl. wp_value.
        iExists (CastV (FoldV u') _ _ (TGround_TUnknown_icp Ground_TRec)).
        iSplitL. done.
        rewrite (interp_rw_TUnknown (stlc_mu.lang.FoldV _ , _)).
        iExists _ , _.
        iModIntro. iRight. iRight. iRight. iRight. iSplit; done.
  Qed.


End ground_star.
