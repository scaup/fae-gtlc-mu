From fae_gtlc_mu.refinements.static_gradual Require Export logical_relation compat_cast.defs compat_easy.
From fae_gtlc_mu.refinements.static_gradual.compat_cast Require Export
     between_rec prod_prod sum_sum arrow_arrow identity tau_star ground_star tau_star star_tau star_ground.

Section compat_cast_all.
  Context `{!implG Σ,!specG Σ}.

  (* Proof of back_cast_ar (the slightly modified version of lemma 4.7 in the paper defined in defs.v) *)
  Lemma back_cast_ar_all {A} {τi τf} (pC : alternative_consistency A τi τf) : back_cast_ar pC.
  Proof.
    (* By induction on the alternative consistency relation *)
    induction pC; (* the different inductive cases are proven in the other files in this directory *)
      eauto using back_cast_ar_star_ground,
      back_cast_ar_ground_star, back_cast_ar_tau_star,
      back_cast_ar_star_tau,
      back_cast_ar_base_base,
      back_cast_ar_star_star,
      back_cast_ar_sum_sum,
      back_cast_ar_prod_prod,
      back_cast_ar_arrow_arrow,
      back_cast_ar_trec_trec_expose,
      back_cast_ar_trec_trec_use.
  Qed.

  Notation "'` H" := (bin_log_related_alt H) (at level 8).

  (* Proof of the actual compatibility lemma of casts (lemma 4.7 in paper) *)
  Lemma bin_log_related_back_cast Γ e e' τi τf (pC : alternative_consistency [] τi τf)
      (IHHtyped : Γ ⊨ e ≤log≤ e' : τi) :
    Γ ⊨ 𝓕c pC [] e ≤log≤ Cast e' τi τf : τf.
  Proof.
    iIntros (vvs ei) "#[Hρ HΓ]"; iIntros (K) "Hj /=".
    rewrite 𝓕c_closed; try auto. rewrite 𝓕c_rewrite.
    (** bringing e and e' to related values v and v' *)
    iApply (wp_bind (ectx_language.fill [stlc_mu.lang.AppRCtx _])).
    iApply (wp_wand with "[Hj]"). iApply ('`IHHtyped _ _ (CastCtx τi τf :: K)). iFrame. auto.
    iIntros (v). iDestruct 1 as (v') "[Hv' Hvv']". simpl.
    rewrite -𝓕c_rewrite.
    (** applying back_cast_ar_all *)
    iApply (wp_wand with "[-]").
    iApply ((back_cast_ar_all pC) with "[-]").
    iSplitR. unfold rel_cast_functions. iSplit; auto.
    iSplitL "Hvv'". auto. auto.
    clear v v'.
    iIntros (v). iDestruct 1 as (v') "[Hv' Hvv']".
    iExists v'.
    auto.
  Qed.

  (** Proof that divergence is related to everything *)
  Lemma bin_log_related_omega Γ e' τ :
    Γ ⊨ Ω ≤log≤ e' : τ.
  Proof.
    iIntros (vvs ρ) "#[Hρ HΓ]"; iIntros (K) "Hj /=".
    by iApply wp_Ω.
  Qed.

End compat_cast_all.
