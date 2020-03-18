From fae_gtlc_mu.refinements.static_gradual Require Export logical_relation resources_right compat_easy help_left compat_cast.defs.
From fae_gtlc_mu.cast_calculus Require Export types typing.
From fae_gtlc_mu.stlc_mu Require Export lang.
From fae_gtlc_mu.cast_calculus Require Export lang.
From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import lifting.
From fae_gtlc_mu.cast_calculus Require Export types.
From fae_gtlc_mu.cast_calculus Require Export consistency.structural.definition.
From fae_gtlc_mu.backtranslation Require Export cast_help.general cast_help.extract cast_help.embed.

(* Coercion stlc_mu.lang.of_val : stlc_mu.lang.val >-> stlc_mu.lang.expr. *)
(* Coercion cast_calculus.lang.of_val : cast_calculus.lang.val >-> cast_calculus.lang.expr. *)

(* Notation "# v" := (of_val v) (at level 20). *)

Section between_rec.
  Context `{!heapG Σ,!gradRN Σ}.
  Notation D := (prodO stlc_mu.lang.valO cast_calculus.lang.valO -n> iPropO Σ).
  (* Implicit Types e : stlc_mu.lang.expr. *)
  (* Implicit Types e : stlc_mu.lang.expr. *)
  Implicit Types fs : list stlc_mu.lang.val.
  (* Implicit Types f : stlc_mu.lang.val. *)
  Implicit Types A : list (cast_calculus.types.type * cast_calculus.types.type).
  (* Implicit Types a : (cast_calculus.types.type * cast_calculus.types.type). *)
  Local Hint Resolve to_of_val : core.

  Lemma interp_subst Δ2 τ τ' v : ⟦ τ ⟧ (⟦ τ' ⟧ Δ2 :: Δ2) v ≡ ⟦ τ.[τ'/] ⟧ Δ2 v.
  Proof. apply (interp_subst_up []). Qed.

  (* Lemma compat_cast_between_TRec A τl τr (p : (TRec τl, TRec τr) ∉ A) (pC : cons_struct ((TRec τl, TRec τr) :: A) ). *)


  Definition back_cast_ar {A} {τi τf} (pC : cons_struct A τi τf) :=
  ∀ ei' K' v v' fs, bi_entails
                      (rel_cast_functions A fs ∗ interp τi [] (v, v') ∗ initially_inv ei' ∗ currently_half (fill K' (Cast (# v') τi τf)))
                      (WP (𝓕c pC fs (stlc_mu.lang.of_val v)) {{ w, ∃ w', currently_half (fill K' (# w')) ∗ interp τf [] (w, w') }})%I.

  (** Proving it *)

  Lemma refold_interp_unknown' vv' : fixpoint interp_unknown1' vv' ≡ interp TUnknown [] vv'.
  Proof.
    auto.
  Qed.

  (* Lemma back_cast_ar_all {A} {τi τf} (pC : cons_struct A τi τf) : back_cast_ar pC. *)
  (* Proof. *)
  (*   induction pC; rewrite /𝓕c /𝓕 /back_cast_ar; iIntros (ei' K' v v' fs) "(Hfs & #Hvv' & #Hei' & Hv')". *)
  (*   - rewrite /𝓕c /𝓕 extract_no_subs. *)
  (*     destruct G. *)
  (*     + (** TUnit *) rewrite unfold_fixpoint_interp_unknown1'. *)
  (*       iDestruct "Hvv'" as "[Hvv'Unit|[Hpp'|[Hss'|[Hff'|Huu']]]]". *)
  (*       * iDestruct "Hvv'Unit" as "%"; inversion H; clear v v' H H1 H2. *)
  (*         admit. *)
  (*       * iDestruct "Hpp'" as (v1 v1' v2 v2') "(% & #H1 & #H2)". simpl in H; inversion H; clear H H1 H2 v v'. *)
  (*         repeat rewrite (refold_interp_unknown'). *)
  (*         admit. *)
  (*       * iDestruct "Hss'" as "[H1 | H2]". *)
  (*         -- iDestruct "H1" as (v1 v1') "[% Hv1v1']"; rewrite (refold_interp_unknown'); inversion H; clear H H1 H2 v v'. *)
  (*            admit. *)
  (*         -- iDestruct "H2" as (v2 v2') "[% Hv2v2']"; rewrite (refold_interp_unknown'); inversion H; clear H H1 H2 v v'. *)
  (*            admit. *)
  (*       * iDestruct "Hff'" as (f f') "[% Hff']". inversion H. clear H H1 H2 v v'. *)
  (*         admit. *)
  (*       * iDestruct "Huu'" as (u u') "[% H]"; rewrite (refold_interp_unknown'); inversion H; clear H H1 H2 v v'. *)
  (*         admit. *)
  (*       * constructor. *)
  (*     + (** TProd *) admit. *)
  (*     + (** TSum *) admit. *)
  (*     + (** TArrow *) rewrite unfold_fixpoint_interp_unknown1'. *)
  (*       iDestruct "Hvv'" as "[Hvv'Unit|[Hpp'|[Hss'|[Hff'|Huu']]] ]". *)
  (*       * iDestruct "Hvv'Unit" as "%"; inversion H; clear v v' H H1 H2. *)
  (*         admit. *)
  (*       * iDestruct "Hpp'" as (v1 v1' v2 v2') "(% & #H1 & #H2)". simpl in H; inversion H; clear H H1 H2 v v'. *)
  (*         repeat rewrite (refold_interp_unknown'). *)
  (*         admit. *)
  (*       * iDestruct "Hss'" as "[H1 | H2]". *)
  (*         -- iDestruct "H1" as (v1 v1') "[% Hv1v1']"; rewrite (refold_interp_unknown'); inversion H; clear H H1 H2 v v'. *)
  (*            admit. *)
  (*         -- iDestruct "H2" as (v2 v2') "[% Hv2v2']"; rewrite (refold_interp_unknown'); inversion H; clear H H1 H2 v v'. *)
  (*            admit. *)
  (*       * iDestruct "Hff'" as (f f') "[% Hff']". inversion H. clear H H1 H2 v v'. *)
  (*         admit. *)
  (*       * iDestruct "Huu'" as (u u') "[% H]"; rewrite (refold_interp_unknown'); inversion H; clear H H1 H2 v v'. *)
  (*         admit. *)
  (*       * constructor. *)
  (*     + (** TRec *) rewrite unfold_fixpoint_interp_unknown1'. *)
  (*       iDestruct "Hvv'" as "[Hvv'Unit|[Hpp'|[Hss'|[Hff'|Huu']]] ]". *)
  (*       * iDestruct "Hvv'Unit" as "%"; inversion H; clear v v' H H1 H2. *)
  (*         admit. *)
  (*       * iDestruct "Hpp'" as (v1 v1' v2 v2') "(% & #H1 & #H2)". simpl in H; inversion H; clear H H1 H2 v v'. *)
  (*         repeat rewrite (refold_interp_unknown'). *)
  (*         admit. *)
  (*       * iDestruct "Hss'" as "[H1 | H2]". *)
  (*         -- iDestruct "H1" as (v1 v1') "[% Hv1v1']"; rewrite (refold_interp_unknown'); inversion H; clear H H1 H2 v v'. *)
  (*            admit. *)
  (*         -- iDestruct "H2" as (v2 v2') "[% Hv2v2']"; rewrite (refold_interp_unknown'); inversion H; clear H H1 H2 v v'. *)
  (*            admit. *)
  (*       * iDestruct "Hff'" as (f f') "[% Hff']". inversion H. clear H H1 H2 v v'. *)
  (*         admit. *)
  (*       * iDestruct "Huu'" as (u u') "[% H]"; rewrite (refold_interp_unknown'); inversion H; clear H H1 H2 v v'. *)
  (*         admit. *)
  (*       * constructor. *)
  (*   - rewrite /𝓕c /𝓕. rewrite embed_no_subs. destruct G. *)
  (*     + iDestruct "Hvv'" as "%". simpl in H. inversion H. rewrite H0 H1. clear v v' H H0 H1. *)
  (*       admit. *)
  (*     + iDestruct "Hvv'" as ((v1 , v1') (v2 , v2')) "[% [H1 H2]]". simpl in H; inversion H; clear H H1 H2 v v'. *)
  (*       admit. *)
  (*     + iDestruct "Hvv'" as "[H1 | H2]". *)
  (*       * iDestruct "H1" as ((v1 , v1')) "[% H1]". *)
  (*         simpl in H; inversion H; clear H H1 H2 v v'. *)
  (*         admit. *)
  (*       * iDestruct "H2" as ((v2 , v2')) "[% H2]". *)
  (*         simpl in H; inversion H; clear H H1 H2 v v'. *)
  (*         admit. *)
  (*     + admit. *)
  (*     + admit. *)
  (*   - admit. *)
  (*   - admit. *)
  (*   - admit. *)
  (*   - admit. *)
  (*   - admit. *)
  (*   - admit. *)
  (*   - fold interp. simpl. admit. *)
  (*   - rewrite /𝓕c /𝓕. *)
  (*     fold (𝓕 pC). simpl. *)
  (*     (* asimpl. fold between_TRec. (𝓕c pC2 fs). *) *)
  (*     admit. *)
  (*   - admit. *)

  (* Admitted. *)






  (*       fold interp_unknown1 interp_unknown. *)
  (*       rewrite interp_unknown_unfold /interp_unknown1; iDestruct "Hvv'" as "#Hvv'"; iDestruct "Hvv'" as "[Hvv'Unit|[Hpp'|[Hss'|[Hff'|Hur']]] ]"; fold interp_unknown1 interp_unknown. *)
  (*       * iDestruct "Hvv'Unit" as ((w , w')) "[% Hww']"; simpl in H; inversion H; clear v v' H H1 H2. *)
  (*         asimpl. *)
  (*         iApply wp_pure_step_later; auto; iNext; asimpl. *)
  (*         iDestruct "Hww'" as "%"; inversion H; rewrite H0 H1; clear w w' H H0 H1. *)
  (*         iApply (wp_bind (stlc_mu.lang.fill_item $ stlc_mu.lang.CaseCtx _ _)). *)
  (*         iApply wp_pure_step_later; auto; iNext. *)
  (*         iApply wp_value. *)
  (*         iApply wp_pure_step_later; auto; iNext. *)
  (*         iApply wp_pure_step_later; auto; iNext. asimpl. *)
  (*         iApply wp_pure_step_later; auto; iNext. *)
  (*         iApply wp_pure_step_later; auto; iNext. asimpl. *)
  (*         iMod (step_pure _ ei' K' (Cast (Cast Unit TUnit ⋆) ⋆ TUnit) (# UnitV) with "[Hv']") as "HHHH"; intros; auto. *)
  (*         apply Same_Ground with (v := UnitV ); auto; constructor. *)
  (*         iApply wp_value. *)
  (*         iExists UnitV. *)
  (*         by repeat iFrame. *)
  (*       * (* diverging branch *) *)
  (*         iDestruct "Hpp'" as ((p , p')) "[% Hpp']"; simpl in H; inversion H; clear H H1 H2 v v'. *)
  (*         asimpl. *)
  (*         iApply wp_pure_step_later; auto; iNext; asimpl. *)
  (*         iDestruct "Hpp'" as ((v1 , v1') (v2 , v2')) "[% [Hv1v1' Hv2v2']]"; simpl in H; inversion H; clear H H1 H2 p p'. *)
  (*         iApply (wp_bind (stlc_mu.lang.fill_item $ stlc_mu.lang.CaseCtx _ _)). *)
  (*         iApply wp_pure_step_later; auto; iNext. *)
  (*         iApply wp_value. *)
  (*         iApply wp_pure_step_later; auto; iNext; asimpl. *)
  (*         iApply wp_pure_step_later; auto; iNext; asimpl. *)
  (*         iApply wp_pure_step_later; auto; iNext. asimpl. *)
  (*         by iApply wp_Ω. *)
  (*       * admit. *)
  (*       * admit. *)
  (*       * iDestruct "Hur'" as ((u , r')) "[% Hr]". simpl in H. inversion H. clear H H1 H2. *)
  (*         admit. *)
  (*     + rewrite interp_unknown_unfold /interp_unknown1; iDestruct "Hvv'" as "#Hvv'"; iDestruct "Hvv'" as "[Hvv'Unit|[Hpp'|[Hss'|[Hff'|Hur']]] ]"; fold interp_unknown1 interp_unknown. *)
  (*       * (* diverging branch *) *)
  (*         iDestruct "Hvv'Unit" as ((w , w')) "[% Hww']"; simpl in H; inversion H; clear v v' H H1 H2. *)
  (*         asimpl. *)
  (*         iApply wp_pure_step_later; auto; iNext; asimpl. *)
  (*         iDestruct "Hww'" as "%"; inversion H; rewrite H0 H1; clear w w' H H0 H1. *)
  (*         iApply (wp_bind (stlc_mu.lang.fill_item $ stlc_mu.lang.CaseCtx _ _)). *)
  (*         iApply wp_pure_step_later; auto; iNext. *)
  (*         iApply wp_value. *)
  (*         iApply (wp_bind (stlc_mu.lang.fill_item $ stlc_mu.lang.CaseCtx _ _)). *)
  (*         iApply wp_value. *)
  (*         iApply wp_pure_step_later; auto; iNext. *)
  (*         iApply wp_pure_step_later; auto; iNext. asimpl. *)
  (*         iApply wp_pure_step_later; auto; iNext. asimpl. *)
  (*         by iApply wp_Ω. *)
  (*       * iDestruct "Hpp'" as ((p , p')) "[% Hpp']"; simpl in H; inversion H; clear H H1 H2. *)
  (*         asimpl. *)
  (*         iApply wp_pure_step_later; auto; iNext; asimpl. *)
  (*         iDestruct "Hpp'" as ((v1 , v1') (v2 , v2')) "[% [Hv1v1' Hv2v2']]"; simpl in H; inversion H; clear H H1 H2 p p'. *)
  (*         iApply (wp_bind (stlc_mu.lang.fill_item $ stlc_mu.lang.CaseCtx _ _)). *)
  (*         iApply wp_pure_step_later; auto; iNext. *)
  (*         iApply wp_value. *)
  (*         iApply wp_pure_step_later; auto; iNext; asimpl. *)
  (*         iApply wp_pure_step_later; auto; iNext; asimpl. *)
  (*         iApply wp_pure_step_later; auto; iNext. asimpl. *)
  (*         iMod (step_pure _ ei' K' *)
  (*                         (Cast *)
  (*                            (Cast (Pair (# v1') (# v2')) *)
  (*                                  (⋆ × ⋆) ⋆) ⋆ *)
  (*                            (⋆ × ⋆) *)
  (*                         ) *)
  (*                         (Pair (# v1') (# v2')) *)
  (*                 with "[Hv']") as "HHHH"; auto. *)
  (*         intro. eapply Same_Ground. simplify_option_eq. auto. constructor. *)
  (*         iApply wp_value. *)
  (*         iExists (PairV (v1') (v2')). *)
  (*         simpl. repeat iFrame. *)
  (*         iExists (v1 , v1') , (v2 , v2'). by auto. *)
  (*       * admit. *)
  (*       * admit. *)
  (*       * admit. *)
  (*     + admit. *)
  (*     + admit. *)
  (*     + rewrite interp_unknown_unfold /interp_unknown1; iDestruct "Hvv'" as "#Hvv'"; iDestruct "Hvv'" as "[Hvv'Unit|[Hpp'|[Hss'|[Hff'|Hur']]] ]"; fold interp_unknown1 interp_unknown. *)
  (*       * admit. *)
  (*       * admit. *)
  (*       * admit. *)
  (*       * admit. *)
  (*       * iDestruct "Hur'" as ((u , r')) "[% Hur']"; inversion H; clear H H1 H2. *)
  (*         iMod (step_pure _ ei' K' *)
  (*                         (Cast (# castupV_TRec r') ⋆ (TRec ⋆)) *)
  (*                         (# r') *)
  (*                 with "[Hv']") as "HHHH"; auto. *)
  (*         intro; eapply Same_Ground; simplify_option_eq; auto; constructor. *)
  (*         iApply wp_pure_step_later; auto; iNext; asimpl. *)
  (*         iApply (wp_bind (stlc_mu.lang.fill_item $ stlc_mu.lang.CaseCtx _ _)). *)
  (*         iApply wp_pure_step_later; auto. *)
  (*         iApply wp_value. simpl.  *)
  (*         iApply wp_pure_step_later; auto. asimpl.  *)
  (*         iApply wp_value. *)
  (*         repeat iNext. *)
  (*         iExists r'. by iFrame. *)
  (*   - destruct G; rewrite /𝓕c /𝓕. *)
  (*     + iApply wp_pure_step_later; auto; iNext; asimpl. *)
  (*       iDestruct "Hvv'" as "%"; inversion H. rewrite H0 H1. clear H H0 H1 v v'. *)
  (*       iApply wp_value. iExists (CastV UnitV TUnit ⋆ (From_ground_to_unknown TUnit Ground_TUnit)). *)
  (*       simpl in *. *)
  (*       iFrame. *)
  (*       rewrite interp_unknown_unfold /interp_unknown1. *)
  (*       admit. *)
  (*     + admit. *)
  (*     + admit. *)
  (*     + admit. *)
  (*     + rewrite fixpoint_interp_rec1_eq. *)
  (*       iDestruct "Hvv'" as ((r , r')) "[% #Hrr']". inversion H; clear H H1 H2. *)
  (*       iApply wp_pure_step_later; auto; iNext; asimpl. *)
  (*       iApply (wp_bind (fill [stlc_mu.lang.InjRCtx ; stlc_mu.lang.FoldCtx ])). *)
  (*       iApply wp_pure_step_later; auto. iNext; asimpl. *)
  (*       iApply wp_value. *)
  (*       iApply wp_value. *)
  (*       iExists (CastV (FoldV r') (TRec ⋆) ⋆ (From_ground_to_unknown (TRec ⋆) Ground_TRec)). *)
  (*       simpl in *. *)
  (*       iFrame. *)
  (*       rewrite{1} interp_unknown_unfold. *)
  (*       rewrite{1} interp_unknown_unfold. *)
  (*       repeat rewrite{1} /interp_unknown1. *)
  (*       iRight. *)
  (*       iRight. *)
  (*       iRight. *)
  (*       iRight. *)
  (*       iModIntro. *)
  (*       iExists (r , FoldV r'). simpl. iSplitL. *)
  (*       auto. *)
  (*       admit. *)
  (*   - admit. *)
  (*   - admit. *)
  (*   - rewrite /𝓕c /𝓕. asimpl. *)
  (*     iApply wp_pure_step_later; auto. *)
  (*     asimpl. *)
  (*     iDestruct "Hvv'" as %[eq1 eq2]; simplify_eq. *)
  (*     iNext. *)
  (*     iMod (step_pure _ ei' K' (Cast (# UnitV) TUnit TUnit) (# UnitV) with "[Hv']") as "HHHH"; auto. *)
  (*     intros; by eapply IdBase. *)
  (*     iApply wp_value. *)
  (*     iExists UnitV. iFrame. iSplit; trivial. *)
  (*   - rewrite /𝓕c /𝓕; asimpl. *)
  (*     iMod (step_pure _ ei' K' (Cast (# v') ⋆ ⋆) (# v') with "[Hv']") as "Hv'"; auto. *)
  (*     intros; by eapply IdStar. *)
  (*     iApply wp_pure_step_later; auto; asimpl. *)
  (*     iNext. *)
  (*     iApply wp_value. *)
  (*     iExists v'. iFrame. *)
  (*   - iDestruct "Hvv'" as "[Hvv'1 | Hvv'2]". *)
  (*     + iDestruct "Hvv'1" as (vv'1) "Hvv'1". destruct vv'1 as (v1 , v1'). *)
  (*       iDestruct "Hvv'1" as "[% Hvv'1]". inversion H. *)
  (*       iMod (step_pure _ ei' K' (Cast (# InjLV v1') (τ1 + τ2)%type (τ1' + τ2')%type) _ with "[Hv']") as "Hv'"; auto; try (intros; eapply SumCast; auto). *)
  (*       iMod ((step_case_inl _ ei' K' (# v1')) with "[Hv']") as "Hv'"; auto. *)
  (*       (* rewrite /𝓕c /𝓕 /between_TSum. *) *)
  (*       rewrite /𝓕c /𝓕. *)
  (*       iApply wp_pure_step_later. auto; asimpl. *)
  (*       iApply wp_pure_step_later; auto; asimpl. *)
  (*       iNext. iNext. *)
  (*       iApply wp_bind. admit. *)
  (*       iApply wp_wand_r. *)
  (*       iSplitL. *)
  (*       iApply (IHpC1 ei' (InjLCtx :: K')). repeat iFrame. auto. *)
  (*       clear H H1 H2 v1 v1'. *)
  (*       iIntros (v1) "HHH". iDestruct "HHH" as (v1') "[Hv1' Hvv'1]". *)
  (*       iApply wp_value. *)
  (*       iExists (InjLV v1'). repeat iFrame. iLeft. iExists (v1 , v1'). *)
  (*       iSplitR. by simpl. done. *)
  (*     + admit. *)
  (*   - iSimpl in "Hvv'". iDestruct "Hvv'" as ((v1 , v1') (v2 , v2')) "[% [Hv1v1' Hv2v2']]". simpl in H; inversion H; clear H H1 H2 v v'. *)
  (*     iApply wp_pure_step_later; auto. *)
  (*     fold (𝓕 pC1) (𝓕 pC2). asimpl. fold (𝓕c pC1 fs) (𝓕c pC2 fs). *)
  (*     iDestruct "Hfs" as "[% Hfs']"; iAssert (rel_cast_functions A fs) with "[Hfs']" as "Hfs". iSplit; done. *)
  (*     rewrite 𝓕c_rewrite. *)
  (*     iApply (wp_bind (fill [stlc_mu.lang.AppRCtx (𝓕cV pC1 fs H) ; stlc_mu.lang.PairLCtx ((𝓕c pC2 fs) (stlc_mu.lang.Snd (stlc_mu.lang.Pair (stlc_mu.lang.of_val v1) (stlc_mu.lang.of_val v2)))) ])). *)
  (*     iApply wp_pure_step_later; auto. *)
  (*     do 2 iNext. iApply wp_value. simpl. *)
  (*     iApply (wp_bind (fill [stlc_mu.lang.PairLCtx ((𝓕c pC2 fs) (stlc_mu.lang.Snd (stlc_mu.lang.Pair (stlc_mu.lang.of_val v1) (stlc_mu.lang.of_val v2)))) ])). *)
  (*     rewrite -𝓕c_rewrite. *)
  (*     iApply (wp_wand with "[Hfs Hv1v1' Hei' Hv']"). *)
  (*     (* iApply (IHpC1 ei' :: K' with "Hfs Hv1v1' Hei' Hv'"). *) *)
  (*     admit. *)
  (*     admit. *)
  (*   - admit. *)
  (*   - rewrite /𝓕c /𝓕. *)
  (*     fold (𝓕 pC). *)
  (*     iApply wp_pure_step_later; auto; asimpl. *)
  (*     iApply (wp_bind $ stlc_mu.lang.fill_item $ stlc_mu.lang.AppLCtx _). *)
  (*     iApply wp_pure_step_later; auto; asimpl. *)
  (*     iApply wp_pure_step_later; auto; asimpl. *)

  (*   - rewrite /𝓕c /𝓕. asimpl. *)
  (*     destruct (fs !! i) as [f | abs] eqn:Hf. *)
  (*     + rewrite (stlc_mu.typing.env_subst_lookup _ _ f); auto. *)
  (*       iDestruct "Hfs" as "[% Hfs]". *)
  (*       rewrite fixpoint_interp_rec1_eq. *)
        
  (*       rewrite interp_unknown_unfold /interp_unknown1. *)
  (*       unfold fixpoint_re *)
  (*       iAssert  *)
        
  (*   destruct () *)


End between_rec.
