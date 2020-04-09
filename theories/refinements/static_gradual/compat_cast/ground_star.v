From fae_gtlc_mu.refinements.static_gradual Require Export logical_relation resources_right compat_easy help_left compat_cast.defs compat_cast.extract_embed.
From fae_gtlc_mu.stlc_mu Require Export lang.
From fae_gtlc_mu.cast_calculus Require Export lang.
From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import lifting.
From fae_gtlc_mu.cast_calculus Require Export types.
From fae_gtlc_mu.cast_calculus Require Export consistency.structural.definition.
From fae_gtlc_mu.backtranslation Require Export cast_help.general cast_help.extract cast_help.embed.
From fae_gtlc_mu.refinements.static_gradual Require Export tactics_left.
From fae_gtlc_mu.cast_calculus Require Export types typing.

Section ground_star.
  Context `{!heapG Σ,!gradRN Σ}.
  Notation D := (prodO stlc_mu.lang.valO cast_calculus.lang.valO -n> iPropO Σ).
  (* Implicit Types e : stlc_mu.lang.expr. *)
  (* Implicit Types e : stlc_mu.lang.expr. *)
  Implicit Types fs : list stlc_mu.lang.val.
  (* Implicit Types f : stlc_mu.lang.val. *)
  Implicit Types A : list (cast_calculus.types.type * cast_calculus.types.type).
  (* Implicit Types a : (cast_calculus.types.type * cast_calculus.types.type). *)
  Local Hint Resolve to_of_val : core.
  Local Hint Resolve stlc_mu.lang.to_of_val : core.

  Lemma refold_interp_unknown' vv' : fixpoint interp_unknown1' vv' ≡ interp TUnknown [] vv'.
  Proof.
    auto.
  Qed.


  Lemma back_cast_ar_ground_star:
    ∀ (A : list (type * type)) (τG : type) (G : Ground τG), back_cast_ar (consTGroundStar A τG G).
  Proof.
    intros A τG G.
    rewrite /back_cast_ar /𝓕c /𝓕. iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')". rewrite embed_no_subs.
    destruct G; rewrite /𝓕c /𝓕.
      + iDestruct "Hvv'" as "%". simpl in H. inversion H. rewrite H0 H1. clear v v' H H0 H1.
        wp_head. asimpl. wp_value.
        iExists (CastV UnitV _ _ (From_ground_to_unknown _ Ground_TUnit)). iSplitL. done.
        rewrite unfold_fixpoint_interp_unknown1'. simpl. iModIntro.
        iLeft. done. constructor.
      + iDestruct "Hvv'" as ((v1 , v1') (v2 , v2')) "[% [H1 H2]]". simpl in H; inversion H; clear H H1 H2 v v'.
        wp_head. asimpl. wp_value.
        iExists (CastV (PairV v1' v2') _ _ (From_ground_to_unknown _ Ground_TProd)). iSplitL. done.
        rewrite (unfold_fixpoint_interp_unknown1' [] (stlc_mu.lang.FoldV (stlc_mu.lang.InjLV (stlc_mu.lang.InjLV (stlc_mu.lang.InjRV (stlc_mu.lang.PairV v1 v2)))),
    CastV (PairV v1' v2') (⋆ × ⋆) ⋆ (From_ground_to_unknown (⋆ × ⋆) Ground_TProd))).
        iModIntro. iRight. iLeft.
        iExists v1 , v1' , v2 , v2'. iSplit. done. iSplit; done.
      + wp_head. asimpl. wp_value.
        iExists (CastV v' _ _ (From_ground_to_unknown _ Ground_TSum)).
        iSplitL. done. rewrite unfold_fixpoint_interp_unknown1'.
        iModIntro. iRight. iRight. iLeft.
        iDestruct "Hvv'" as "[H1 | H2]".
        * iDestruct "H1" as ((v1 , v1')) "[% H1]".
          simpl in H; inversion H; clear H H1 H2 v v'.
          iLeft. iExists v1 , v1'. iSplit. done. auto.
        * iDestruct "H2" as ((v2 , v2')) "[% H2]".
          simpl in H; inversion H; clear H H1 H2 v v'.
          iRight. iExists v2 , v2'. iSplit. done. auto.
        * constructor.
      + iDestruct "Hvv'" as "#Hvv'". wp_head. asimpl. wp_value.
        iExists (CastV v' _ _ (From_ground_to_unknown _ Ground_TArrow)). iSplitL. done.
        rewrite unfold_fixpoint_interp_unknown1'.
        iModIntro. iRight. iRight. iRight. iLeft.
        iExists v , v'. iSplit. done. iModIntro. iModIntro.
        iIntros (a a').
        fold (interp_unknown_pre').
        fold (interp_unknown' [] (a , a')).
        fold (interp ⋆).
        iIntros "#Haa'".
        clear K'. iIntros (K') "Hv'a'".
        iApply ("Hvv'" $! (a , a') with "Haa' Hv'a'"). constructor.
      + wp_head. asimpl.
        (** rewriting value relation for v and v' *)
        rewrite fixpoint_interp_rec1_eq.
        iDestruct "Hvv'" as ([u u']) "#[% Huu']". inversion H. clear v v' H H1 H2.
        (** boring steps *)
        iApply (wp_bind (fill $ [stlc_mu.lang.InjRCtx ; stlc_mu.lang.FoldCtx])).
        wp_head. wp_value. simpl. wp_value.
        iExists (CastV (FoldV u') _ _ (From_ground_to_unknown _ Ground_TRec)).
        iSplitL. done.
        rewrite (unfold_fixpoint_interp_unknown1' [] (stlc_mu.lang.FoldV (stlc_mu.lang.InjRV u), CastV (FoldV u') (TRec ⋆) ⋆ (From_ground_to_unknown (TRec ⋆) Ground_TRec))).
        iModIntro. iRight. iRight. iRight. iRight.
        iExists u , u'. iSplit; done.
  Admitted.


End ground_star.

