From fae_gtlc_mu.refinements.static_gradual Require Export compat_cast.defs.
From fae_gtlc_mu.backtranslation Require Export cast_help.props.extract_embed.
From fae_gtlc_mu.cast_calculus Require Export lang.

Section star_ground.
  Context `{!implG Σ,!specG Σ}.
  Local Hint Resolve to_of_val : core.

  Lemma back_cast_ar_star_ground (A : list (type * type)) (τG : type) (G : Ground τG) : back_cast_ar (atomic_Unknown_Ground A τG G).
  Proof.
    rewrite /back_cast_ar /𝓕c /𝓕. iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')". rewrite extract_no_subs.
    destruct G; rewrite interp_rw_TUnknown.
    - (iDestruct "Hvv'" as (w w') "#[[% Hww]|[[% Hww]|[[% Hww]|[[% Hww]|[% Hww]]]]]"; inversion H; clear H H1 H2 v v');
      try by (wp_head; iApply (wp_bind (stlc_mu.lang.fill_item $ stlc_mu.lang.CaseCtx _ _)); wp_head; wp_value; repeat ((by rewrite Ω_closed; by iApply wp_Ω) || wp_head)).
      iApply (wp_pure_step_later _ _ _ (stlc_mu.lang.of_val w) True); auto.
      intros _. apply extract_TUnit_embed_TUnit. repeat iModIntro.
      iMod (step_pure _ ei' K'
                      (Cast (# castupV_TUnit w') ⋆ TUnit)
                      w' with "[Hv']") as "Hv'".
      eapply Same_Ground. auto. constructor. auto. auto. wp_value.
      iExists _. auto.
    - (iDestruct "Hvv'" as (w w') "#[[% Hww]|[[% Hww]|[[% Hww]|[[% Hww]|[% Hww]]]]]"; inversion H; clear H H1 H2 v v');
      try by (wp_head; iApply (wp_bind (stlc_mu.lang.fill_item $ stlc_mu.lang.CaseCtx _ _)); wp_head; wp_value; repeat ((by rewrite Ω_closed; by iApply wp_Ω) || wp_head)).
      iApply (wp_pure_step_later _ _ _ (stlc_mu.lang.of_val w) True); auto.
      intros _. apply extract_TProd_embed_TProd. repeat iModIntro.
      iMod (step_pure _ ei' K'
                      (Cast (# castupV_TProd w') ⋆ (TProd ⋆ ⋆))
                      w' with "[Hv']") as "Hv'".
      eapply Same_Ground. auto. constructor. auto. auto. wp_value.
      iExists _. auto.
    - (iDestruct "Hvv'" as (w w') "#[[% Hww]|[[% Hww]|[[% Hww]|[[% Hww]|[% Hww]]]]]"; inversion H; clear H H1 H2 v v');
      try by (wp_head; iApply (wp_bind (stlc_mu.lang.fill_item $ stlc_mu.lang.CaseCtx _ _)); wp_head; wp_value; repeat ((by rewrite Ω_closed; by iApply wp_Ω) || wp_head)).
      iApply (wp_pure_step_later _ _ _ (stlc_mu.lang.of_val w) True); auto.
      intros _. apply extract_TSum_embed_TSum. repeat iModIntro.
      iMod (step_pure _ ei' K'
                      (Cast (# castupV_TSum w') ⋆ (TSum ⋆ ⋆))
                      w' with "[Hv']") as "Hv'".
      eapply Same_Ground. auto. constructor. auto. auto. wp_value.
      iExists _. auto.
    - (iDestruct "Hvv'" as (w w') "#[[% Hww]|[[% Hww]|[[% Hww]|[[% Hww]|[% Hww]]]]]"; inversion H; clear H H1 H2 v v');
      try by (wp_head; iApply (wp_bind (stlc_mu.lang.fill_item $ stlc_mu.lang.CaseCtx _ _)); wp_head; wp_value; repeat ((by rewrite Ω_closed; by iApply wp_Ω) || wp_head)).
      iApply (wp_pure_step_later _ _ _ (stlc_mu.lang.of_val w) True); auto.
      intros _. apply extract_TArrow_embed_TArrow. repeat iModIntro.
      iMod (step_pure _ ei' K'
                      (Cast (# castupV_TArrow w') ⋆ (TArrow ⋆ ⋆))
                      w' with "[Hv']") as "Hv'".
      eapply Same_Ground. auto. constructor. auto. auto. wp_value.
      iExists _. auto.
    - (iDestruct "Hvv'" as (w w') "#[[% Hww]|[[% Hww]|[[% Hww]|[[% Hww]|[% Hww]]]]]"; inversion H; clear H H1 H2 v v');
      try by  (wp_head; iApply (wp_bind (stlc_mu.lang.fill_item $ stlc_mu.lang.CaseCtx _ _)); wp_head; wp_value; wp_head; by iApply wp_Ω).

      iApply (wp_pure_step_later _ _ _ (stlc_mu.lang.Fold (stlc_mu.lang.of_val w)) True); auto.
      intros _. apply extract_TRec_embed_TUnknown. repeat iModIntro.
      iMod (step_pure _ ei' K'
                      (Cast (# castupV_TRec (FoldV w')) ⋆ (TRec ⋆))
                      (FoldV w') with "[Hv']") as "Hv'".
      eapply Same_Ground. auto. constructor. auto. auto. wp_value.
      iExists _. rewrite interp_rw_TRec. asimpl. iSplit; auto. by simpl.
  Qed.

End star_ground.
