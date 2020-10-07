From fae_gtlc_mu.refinements.static_gradual Require Export compat_cast.defs.
From fae_gtlc_mu.cast_calculus Require Export lang.

Section compat_cast_identity.
  Context `{!implG Σ,!specG Σ}.
  Local Hint Resolve to_of_val : core.

  Lemma back_cast_ar_base_base:
    ∀ A : list (type * type), back_cast_ar (atomic_Base A).
  Proof.
    intros A.
    rewrite /back_cast_ar. iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    rewrite interp_rw_TUnit.
    iDestruct "Hvv'" as "%"; inversion H. simpl in *. rewrite H0 H1. clear v v' H H0 H1.
    asimpl. wp_head.
    iMod (step_pure _ ei' K'
                    (Cast Unit TUnit TUnit)
                    Unit with "[Hv']") as "Hv'". intros. eapply IdBase. by simpl. auto.
    iSplitR. done. done. asimpl. wp_value. iExists UnitV. iSplitL. done. rewrite interp_rw_TUnit. done.
  Qed.

  Lemma back_cast_ar_star_star:
    ∀ A : list (type * type), back_cast_ar (consStarStar A).
  Proof.
    intros A.
    rewrite /back_cast_ar. iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    asimpl. wp_head.
    iMod (step_pure _ ei' K'
                    (Cast (# v') ⋆ ⋆)
                    (# v') with "[Hv']") as "Hv'". intros. eapply IdStar. by simpl. auto.
    iSplitR. done. done. asimpl. wp_value. iExists v'. iSplitL. done. done.
  Qed.

End compat_cast_identity.
