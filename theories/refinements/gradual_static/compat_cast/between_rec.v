From fae_gtlc_mu.refinements.gradual_static Require Export compat_cast.defs.
From fae_gtlc_mu.backtranslation.cast_help Require Export between_rec_fix.
From fae_gtlc_mu.stlc_mu Require Export lang.

Section between_rec.
  Context `{!implG Σ,!specG Σ}.

  Lemma back_cast_ar_trec_trec_use:
    ∀ (A : list (type * type)) (τl τr : {bind type}) (i : nat) (pμτlμtrinA : A !! i = Some (TRec τl, TRec τr)),
      back_cast_ar (atomic_UseRecursion A τl τr i pμτlμtrinA).
  Proof.
    intros A τl τr i pμτlμtr.
    rewrite /𝓕c /𝓕 /back_cast_ar; iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    rewrite /𝓕c /𝓕. asimpl.
    (** getting the information about the length of the list *)
    iDestruct "Hfs" as "[% Hfs']".
    destruct (fs !! i) as [f | ] eqn:Hf.
    rewrite (stlc_mu.typing_lemmas.env_subst_lookup _ i f); try done.
    {
      iDestruct (big_sepL2_lookup with "Hfs'") as "#Hf". exact pμτlμtr. exact Hf.
      iApply ("Hf" $! v v' with "Hvv'"). done.
    }
    { (* trivially impossible case *)
      assert (Hi : i < length fs). rewrite -H. by eapply lookup_lt_Some.
      assert (Hi' : i >= length fs). by apply lookup_ge_None_1. exfalso. lia.
    }
  Qed.

  Lemma back_cast_ar_trec_trec_expose:
    ∀ (A : list (type * type)) (τl τr : {bind type}) (pμτlμτrnotA : (TRec τl, TRec τr) ∉ A)
      (pC : alternative_consistency ((TRec τl, TRec τr) :: A) τl.[TRec τl/] τr.[TRec τr/]) (IHpC : back_cast_ar pC),
      back_cast_ar (exposeRecursiveCAll A τl τr pμτlμτrnotA pC).
  Proof.
    intros A τl τr pμτlμτrnotA pC IHpC.
    rewrite /𝓕c /𝓕 /back_cast_ar; iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    iDestruct "Hfs" as "[% Hfs']"; iAssert (rel_cast_functions A fs) with "[Hfs']" as "Hfs". iSplit; done. rename H into Hl.
    (** setting up iLöb *)
    iLöb as "IHlob" forall (v v' ei' K') "Hvv' Hei'".
    (** ... *)
    rewrite {2}/𝓕c. rewrite /𝓕.
    fold (𝓕 pC).
    (** rewriting value relation for v and v' *)
    rewrite interp_rw_TRec.
    iDestruct "Hvv'" as (w w') "#[% Hww']".
    inversion H; clear v v' H H1 H2.
    (** implementation side *)
    wp_head. fold (cast_calculus.lang.of_val w).
    iApply (wp_bind [CastCtx _ _; cast_calculus.lang.FoldCtx]). wp_value. simpl (lang.fill _ _).
    (** specification side *)
    iMod (steps_pure _ ei' K' _ _ _ (between_TRec_steps pC fs Hl pμτlμτrnotA w') with "[Hv']") as "Hv'"; auto.
    (** IH *)
    iApply (wp_bind [cast_calculus.lang.FoldCtx]).
    iApply (wp_wand with "[-]").
    iApply (IHpC ei' (FoldCtx :: K') w w' (𝓕cV (exposeRecursiveCAll A τl τr pμτlμτrnotA pC) fs Hl :: fs)).
    iFrame "Hei' Hww' Hv'". iSplit; first by (simpl; iPureIntro; lia). iSplit; try done.
    (** iLob *)
    iModIntro. iIntros (v v') "#Hvv'".
    clear K'. iIntros (K') "Hv'". iSimpl in "Hv'".
    iApply ("IHlob" $! v v' with "Hv' Hvv' Hei'").
    (** ... *)
    iIntros (v) "H".
    iDestruct "H" as (v') "[Hv' #Hvv']".
    iApply wp_value.
    iExists (FoldV v').
    iFrame.
    rewrite interp_rw_TRec.
    simpl. iModIntro.
    iExists v , v'; auto.
  Qed.

End between_rec.
