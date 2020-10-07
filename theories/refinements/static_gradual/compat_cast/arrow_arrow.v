From fae_gtlc_mu.refinements.static_gradual Require Export compat_cast.defs.
From fae_gtlc_mu.backtranslation Require Export general_def_lemmas.
From fae_gtlc_mu.cast_calculus Require Export lang.

Section compat_cast_arrow_arrow.
  Context `{!implG Σ,!specG Σ}.

  Lemma back_cast_ar_arrow_arrow:
    ∀ (A : list (type * type)) (τ1 τ1' τ2 τ2' : type) (pC1 : alternative_consistency A τ1' τ1) (pC2 : alternative_consistency A τ2 τ2')
      (IHpC1 : back_cast_ar pC1) (IHpC2 : back_cast_ar pC2),
      back_cast_ar (throughArrow A τ1 τ1' τ2 τ2' pC1 pC2).
  Proof.
    intros A τ1 τ1' τ2 τ2' pC1 pC2 IHpC1 IHpC2.
    rewrite /back_cast_ar. iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    fold interp.
    iDestruct "Hfs" as "[% Hfs']"; iAssert (rel_cast_functions A fs) with "[Hfs']" as "Hfs". iSplit; done. iClear "Hfs'".
    rewrite /𝓕c /𝓕. fold (𝓕 pC1) (𝓕 pC2). rewrite between_TArrow_subst_rewrite.
    rename v into f. rename v' into f'. iDestruct "Hv'" as "Hf'". iDestruct "Hvv'" as "Hff'".
    (* iClear "Hvv'". *)
    fold (𝓕c pC1 fs) (𝓕c pC2 fs).
    iDestruct "Hfs" as "[% Hfs']"; iAssert (rel_cast_functions A fs) with "[Hfs']" as "Hfs". iSplit; done. iClear "Hfs'".
    do 2 rewrite 𝓕c_rewrite.
    unfold between_TArrow.
    wp_head.
    asimpl.
    iApply wp_value.
    iExists (CastV f' (TArrow τ1 τ2) (TArrow τ1' τ2') (TArrow_TArrow_icp τ1 τ2 τ1' τ2')).
    rewrite interp_rw_TArrow.
    iSplitL "Hf'"; auto.
    rewrite interp_rw_TArrow.
    iModIntro.
    (** actual thing to prove *)
    (** ===================== *)
    iIntros ((a , a')) "#Haa'".
    simpl. clear K'.
    iIntros (K') "Hf'".
    simpl in *.
    (** implementation *)
    wp_head. asimpl.
    (** specification *)
    iMod (step_pure _ ei' K'
                    (App (Cast (# f') (TArrow τ1 τ2) (TArrow τ1' τ2')) (# a'))
                    (Cast (App (# f') (Cast (# a') τ1' τ1)) τ2 τ2') with "[Hf']") as "Hf'".
    intros. eapply AppCast; try by rewrite -to_of_val. auto. by iFrame.
    (** first IH for the arguments *)
    iApply (wp_bind (ectx_language.fill $ [stlc_mu.lang.AppRCtx _ ; stlc_mu.lang.AppRCtx _])).
    iApply (wp_wand with "[-]").
    rewrite -𝓕c_rewrite.
    iApply (IHpC1 ei' (AppRCtx f' :: CastCtx τ2 τ2' :: K') with "[Hf']").
    (* iApply (IHpC1 ei' (CastCtx τ2 τ4 :: AppRCtx f' :: K') with "[Hf']"). *)
    iSplitR. done.
    iSplitR. done.
    iSplitR. done.
    simpl. done.
    iIntros (b) "HHH".
    iDestruct "HHH" as (b') "[Hb' #Hbb']".
    simpl.
    iClear "Haa'". clear a a'.
    (** using the relatedness of functions *)
    iApply (wp_bind (ectx_language.fill $ [stlc_mu.lang.AppRCtx _ ])).
    iApply (wp_wand with "[-]").
    iDestruct ("Hff'" with "Hbb'") as "Hfbf'b' /=".
    iApply ("Hfbf'b'" $! (CastCtx τ2 τ2' :: K')).
    simpl.
    iExact "Hb'".
    iIntros (r) "HHH". iDestruct "HHH" as (r') "[Hr' Hrr']".
    simpl.
    iClear "Hbb'". clear b b'.
    (** second IH for the results *)
    iApply (wp_wand with "[-]").
    rewrite -𝓕c_rewrite.
    iApply (IHpC2 ei' K' r r' with "[-]").
    iSplitR. done.
    iSplitL "Hrr'"; try done.
    iSplitR. done.
    done.
    iIntros (s) "HHH". done.
  Qed.

End compat_cast_arrow_arrow.
