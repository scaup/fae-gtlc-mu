From fae_gtlc_mu.stlc_mu Require Export types typing.
From fae_gtlc_mu.cast_calculus Require Export lang.
From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import lifting.
From fae_gtlc_mu.backtranslation Require Export cast_help.general cast_help.extract cast_help.embed props.extract_embed.
From fae_gtlc_mu.stlc_mu Require Export lang.
From fae_gtlc_mu.refinements.gradual_static Require Export logical_relation resources_left resources_right compat_easy compat_cast.defs.
From fae_gtlc_mu.cast_calculus Require Export consistency.structural types.

Section ground_star.
  Context `{!implG Σ,!specG Σ}.
  Notation D := (prodO cast_calculus.lang.valO stlc_mu.lang.valO -n> iPropO Σ).
  (* Implicit Types e : cast_calculus.lang.expr. *)
  (* Implicit Types e : cast_calculus.lang.expr. *)
  Implicit Types fs : list cast_calculus.lang.val.
  (* Implicit Types f : cast_calculus.lang.val. *)
  Implicit Types A : list (stlc_mu.types.type * stlc_mu.types.type).
  (* Implicit Types a : (stlc_mu.types.type * stlc_mu.types.type). *)
  Local Hint Resolve to_of_val : core.
  Local Hint Resolve cast_calculus.lang.to_of_val : core.

  Hint Resolve to_of_val : core.

  Hint Extern 5 (AsVal _) => eexists; simpl; try done; eapply cast_calculus.lang.of_to_val; fast_done : typeclass_instances.
  Hint Extern 10 (AsVal _) =>
  eexists; rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.


  Hint Extern 5 (IntoVal _ _) => eapply of_to_val; fast_done : typeclass_instances.
  Hint Extern 10 (IntoVal _ _) =>
    rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

  Lemma back_cast_ar_ground_star:
    ∀ (A : list (type * type)) (τG : type) (G : Ground τG), back_cast_ar (consTGroundStar A τG G).
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
      rewrite (interp_rw_TUnknown (CastV (lang.FoldV u) (TRec ⋆) ⋆ (TGround_TUnknown_icp Ground_TRec), embedV_TUnknown u')).
      iExists _ , _.
      iModIntro. iRight. iRight. iRight. iRight. iSplit; done.
  Qed.


End ground_star.

