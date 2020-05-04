From fae_gtlc_mu.refinements.static_gradual Require Export logical_relation resources_right compat_easy help_left compat_cast.defs.
From fae_gtlc_mu.stlc_mu Require Export lang.
From fae_gtlc_mu.cast_calculus Require Export lang.
From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import lifting.
From fae_gtlc_mu.cast_calculus Require Export types.
From fae_gtlc_mu.cast_calculus Require Export consistency.structural.
From fae_gtlc_mu.backtranslation Require Export cast_help.general cast_help.extract cast_help.embed.
From fae_gtlc_mu.cast_calculus Require Export types typing.

Section star_ground.
  Context `{!implG Σ,!specG Σ}.
  Notation D := (prodO stlc_mu.lang.valO cast_calculus.lang.valO -n> iPropO Σ).
  (* Implicit Types e : stlc_mu.lang.expr. *)
  (* Implicit Types e : stlc_mu.lang.expr. *)
  Implicit Types fs : list stlc_mu.lang.val.
  (* Implicit Types f : stlc_mu.lang.val. *)
  Implicit Types A : list (cast_calculus.types.type * cast_calculus.types.type).
  (* Implicit Types a : (cast_calculus.types.type * cast_calculus.types.type). *)
  Local Hint Resolve to_of_val : core.
  Local Hint Resolve stlc_mu.lang.to_of_val : core.

  (* Lemma refold_interp_unknown' vv' : fixpoint interp_unknown1' vv' ≡ interp TUnknown [] vv'. *)
  (* Proof. *)
  (*   auto. *)
  (* Qed. *)


  Lemma back_cast_ar_star_ground (A : list (type * type)) (τG : type) (G : Ground τG) : back_cast_ar (consStarTGround A τG G).
  Proof.
    rewrite /back_cast_ar /𝓕c /𝓕. iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')". rewrite extract_no_subs.
    destruct G; rewrite interp_rw_TUnknown.
    - (iDestruct "Hvv'" as (w w') "#[[% Hww]|[[% Hww]|[[% Hww]|[[% Hww]|[% Hww]]]]]"; inversion H; clear H H1 H2 v v').
      + admit.
      + admit.
      + admit.
      + admit.
      + admit.
    - (iDestruct "Hvv'" as (w w') "#[[% Hww]|[[% Hww]|[[% Hww]|[[% Hww]|[% Hww]]]]]"; inversion H; clear H H1 H2 v v').
      + admit.
      + admit.
      + admit.
      + admit.
      + admit.
    - (iDestruct "Hvv'" as (w w') "#[[% Hww]|[[% Hww]|[[% Hww]|[[% Hww]|[% Hww]]]]]"; inversion H; clear H H1 H2 v v').
      + admit.
      + admit.
      + admit.
      + admit.
      + admit.
    - (iDestruct "Hvv'" as (w w') "#[[% Hww]|[[% Hww]|[[% Hww]|[[% Hww]|[% Hww]]]]]"; inversion H; clear H H1 H2 v v').
      + admit.
      + admit.
      + admit.
      + admit.
      + admit.
    - (iDestruct "Hvv'" as (w w') "#[[% Hww]|[[% Hww]|[[% Hww]|[[% Hww]|[% Hww]]]]]"; inversion H; clear H H1 H2 v v').
      + admit.
      + admit.
      + admit.
      + admit.
      + admit.
      + admit.
  Admitted.


  (* Lemma back_cast_ar_star_ground (A : list (type * type)) (τG : type) (G : Ground τG) : back_cast_ar (consStarTGround A τG G). *)
  (* Proof. *)
  (*   rewrite /back_cast_ar /𝓕c /𝓕. iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')". rewrite extract_no_subs. *)
  (*   destruct G. *)
  (*   - (** TUnit *) rewrite unfold_fixpoint_interp_unknown1'; try by constructor. *)
  (*     iDestruct "Hvv'" as "[Hvv'Unit|[Hpp'|[Hss'|[Hff'|Huu']]]]". *)
  (*     * iDestruct "Hvv'Unit" as "%"; inversion H; clear v v' H H1 H2. *)
  (*       (** easy case; delegate to extract_embed file with good tactics *) *)
  (*       admit. *)

  (*       (* iApply wp_pure_step_later; auto; iNext; asimpl. *) *)
  (*       (* iApply (wp_bind (stlc_mu.lang.fill_item $ stlc_mu.lang.CaseCtx _ _)). *) *)
  (*       (* iApply wp_pure_step_later; auto; iNext. *) *)
  (*       (* iApply wp_value. *) *)
  (*       (* iApply wp_pure_step_later; auto; iNext. *) *)
  (*       (* iApply wp_pure_step_later; auto; iNext. asimpl. *) *)
  (*       (* iApply wp_pure_step_later; auto; iNext. *) *)
  (*       (* iApply wp_pure_step_later; auto; iNext. asimpl. *) *)
  (*       (* iMod (step_pure _ ei' K' (Cast (Cast Unit TUnit ⋆) ⋆ TUnit) (# UnitV) with "[Hv']") as "HHHH"; intros; auto. *) *)
  (*       (* apply Same_Ground with (v := UnitV ); auto; constructor. *) *)
  (*       (* iApply wp_value. *) *)
  (*       (* iExists UnitV. *) *)
  (*       (* by repeat iFrame. *) *)


  (*     * iDestruct "Hpp'" as (v1 v1' v2 v2') "(% & #H1 & #H2)". simpl in H; inversion H; clear H H1 H2 v v'. *)
  (*       repeat rewrite (refold_interp_unknown'). *)
  (*       (** diverging case *) *)
  (*       admit. *)

  (*         (* asimpl. *) *)
  (*         (* iApply wp_pure_step_later; auto; iNext; asimpl. *) *)
  (*         (* iApply (wp_bind (stlc_mu.lang.fill_item $ stlc_mu.lang.CaseCtx _ _)). *) *)
  (*         (* iApply wp_pure_step_later; auto; iNext. *) *)
  (*         (* iApply wp_value. *) *)
  (*         (* iApply wp_pure_step_later; auto; iNext; asimpl. *) *)
  (*         (* iApply wp_pure_step_later; auto; iNext; asimpl. *) *)
  (*         (* iApply wp_pure_step_later; auto; iNext. asimpl. *) *)
  (*         (* by iApply wp_Ω. *) *)



  (*     * iDestruct "Hss'" as "[H1 | H2]". *)
  (*       -- iDestruct "H1" as (v1 v1') "[% Hv1v1']"; rewrite (refold_interp_unknown'); inversion H; clear H H1 H2 v v'. *)
  (*          (** diverging case *) admit. *)
  (*         -- iDestruct "H2" as (v2 v2') "[% Hv2v2']"; rewrite (refold_interp_unknown'); inversion H; clear H H1 H2 v v'. *)
  (*          (** diverging case *) admit. *)
  (*     * iDestruct "Hff'" as (f f') "[% Hff']". inversion H. clear H H1 H2 v v'. *)
  (*       (** diverging case *) admit. *)
  (*     * iDestruct "Huu'" as (u u') "[% H]"; rewrite (refold_interp_unknown'); inversion H; clear H H1 H2 v v'. *)
  (*       (** diverging case *) admit. *)
  (*   - (** TProd *) *)
  (*     admit. *)
  (*   - (** TSum *) admit. *)
  (*   - (** TArrow *) rewrite unfold_fixpoint_interp_unknown1'. *)
  (*     iDestruct "Hvv'" as "[Hvv'Unit|[Hpp'|[Hss'|[Hff'|Huu']]] ]". *)
  (*     * iDestruct "Hvv'Unit" as "%"; inversion H; clear v v' H H1 H2. *)
  (*       (** diverging case *) admit. *)
  (*     * iDestruct "Hpp'" as (v1 v1' v2 v2') "(% & #H1 & #H2)". simpl in H; inversion H; clear H H1 H2 v v'. *)
  (*       repeat rewrite (refold_interp_unknown'). *)
  (*       (** diverging case *) admit. *)
  (*     * iDestruct "Hss'" as "[H1 | H2]". *)
  (*       -- iDestruct "H1" as (v1 v1') "[% Hv1v1']"; rewrite (refold_interp_unknown'); inversion H; clear H H1 H2 v v'. *)
  (*           (** diverging case *) admit. *)
  (*       -- iDestruct "H2" as (v2 v2') "[% Hv2v2']"; rewrite (refold_interp_unknown'); inversion H; clear H H1 H2 v v'. *)
  (*           (** diverging case *) admit. *)
  (*     * iDestruct "Hff'" as (f f') "[% Hff']". inversion H. clear H H1 H2 v v'. *)
  (*       (** easy case *) admit. *)
  (*     * iDestruct "Huu'" as (u u') "[% H]"; rewrite (refold_interp_unknown'); inversion H; clear H H1 H2 v v'. *)
  (*       (** diverging case *) admit. *)
  (*     * constructor. *)
  (*   - (** TRec *) rewrite unfold_fixpoint_interp_unknown1'. *)
  (*     iDestruct "Hvv'" as "[Hvv'Unit|[Hpp'|[Hss'|[Hff'|Huu']]] ]". *)
  (*     * iDestruct "Hvv'Unit" as "%"; inversion H; clear v v' H H1 H2. *)
  (*       (** diverging case *) admit. *)
  (*     * iDestruct "Hpp'" as (v1 v1' v2 v2') "(% & #H1 & #H2)". simpl in H; inversion H; clear H H1 H2 v v'. *)
  (*       repeat rewrite (refold_interp_unknown'). *)
  (*       (** diverging case *) admit. *)
  (*     * iDestruct "Hss'" as "[H1 | H2]". *)
  (*       -- iDestruct "H1" as (v1 v1') "[% Hv1v1']"; rewrite (refold_interp_unknown'); inversion H; clear H H1 H2 v v'. *)
  (*          (** diverging case *) admit. *)
  (*       -- iDestruct "H2" as (v2 v2') "[% Hv2v2']"; rewrite (refold_interp_unknown'); inversion H; clear H H1 H2 v v'. *)
  (*          (** diverging case *) admit. *)
  (*     * iDestruct "Hff'" as (f f') "[% Hff']". inversion H. clear H H1 H2 v v'. *)
  (*       (** diverging case *) admit. *)
  (*     * iDestruct "Huu'" as (u u') "[% #H]"; rewrite (refold_interp_unknown'); inversion H; clear H H1 H2 v v'. *)
  (*       (** easy case*) *)
  (*       rewrite /embedV_TUnknown /castupV_TRec. *)
  (*       iMod (step_pure _ ei' K' *)
  (*                         (Cast (# castupV_TRec (FoldV u')) ⋆ (TRec ⋆)) *)
  (*                         (# (FoldV u')) *)
  (*                 with "[Hv']") as "HHHH"; auto. *)
  (*       eapply Same_Ground. apply to_of_val. constructor. *)
  (*       iApply wp_pure_step_later; auto; iNext; asimpl. *)
  (*       iApply (wp_bind (stlc_mu.lang.fill_item $ stlc_mu.lang.CaseCtx _ _)). *)
  (*       iApply wp_pure_step_later; auto. *)
  (*       iApply wp_value. simpl. *)
  (*       iApply wp_pure_step_later; auto. asimpl. *)
  (*       iApply wp_value. *)
  (*       repeat iNext. *)
  (*       iExists (FoldV u'). iSplitL. done. *)
  (*       rewrite fixpoint_interp_rec1_eq. *)
  (*       iModIntro. *)
  (*       iExists (u, u'). *)
  (*       iSplitL; done. *)
  (*     * constructor. *)
  (* Admitted. *)


End star_ground.
