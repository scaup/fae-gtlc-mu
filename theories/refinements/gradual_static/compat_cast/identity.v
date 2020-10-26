From fae_gtlc_mu.refinements.gradual_static Require Export compat_cast.defs.
From fae_gtlc_mu.cast_calculus Require Export lang.

Section compat_cast_identity.
  Context `{!implG Σ,!specG Σ}.

  Hint Extern 5 (AsVal _) => eexists; simpl; try done; eapply cast_calculus.lang.of_to_val; fast_done : typeclass_instances.

  Lemma back_cast_ar_base_base:
    ∀ A : list (type * type), back_cast_ar (atomic_Base A).
  Proof.
    intros A.
    rewrite /back_cast_ar. iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    rewrite /𝓕c /𝓕. asimpl.
    iMod ((step_lam _ ei' K') with "[Hv']") as "Hv'"; auto; simpl.
    wp_head. wp_value. iExists v'. auto.
  Qed.

  Lemma back_cast_ar_star_star:
    ∀ A : list (type * type), back_cast_ar (atomic_Unknown A).
  Proof.
    intros A.
    rewrite /back_cast_ar. iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    rewrite /𝓕c /𝓕. asimpl.
    iMod ((step_lam _ ei' K') with "[Hv']") as "Hv'"; auto; simpl.
    wp_head. wp_value. iExists v'. auto.
  Qed.

End compat_cast_identity.
