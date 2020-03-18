From fae_gtlc_mu.refinements.static_gradual Require Export tactics_left logical_relation resources_right compat_easy help_left compat_cast.defs.
From fae_gtlc_mu.cast_calculus Require Export types typing.
From fae_gtlc_mu.stlc_mu Require Export lang.
From fae_gtlc_mu.cast_calculus Require Export lang.
From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import lifting.
From fae_gtlc_mu.cast_calculus Require Export types.
From fae_gtlc_mu.cast_calculus Require Export consistency.structural.definition.
From fae_gtlc_mu.backtranslation Require Export cast_help.general cast_help.extract cast_help.embed.

Section compat_cast_all.
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

  (** Proving it *)

  (* Lemma rewrite_subs_app (e1 e2 : expr) σ : *)
  (*   (App e1 e2).[σ] = App e1.[σ] e2.[σ]. *)
  (* Proof. *)
  (*     by simpl. *)
  (* Qed. *)

 Lemma wp_fix'' (f : stlc_mu.lang.expr) Φ :
   (▷ ▷ WP f (stlc_mu.lang.Lam (rename (+1) (Fix'' f) (stlc_mu.lang.Var 0)))   {{ Φ }} -∗ (WP (Fix'' f) {{ Φ }}))%I.
 Proof.
   iIntros "H".
   rewrite{2} /Fix''.
   iApply (wp_bind $ stlc_mu.lang.fill_item $ stlc_mu.lang.AppLCtx _).
   apply (@ectxi_lang_ctx_item stlc_mu.lang.ectxi_lang). (* hmmmm :( *)
   wp_head.
   (* iApply wp_pure_step_later; auto; iNext. *)
   iApply wp_value.
   simpl.
   iApply wp_pure_step_later; auto; iNext.
   asimpl.
   iApply "H".
 Qed.

  Lemma refold_interp_unknown' vv' : fixpoint interp_unknown1' vv' ≡ interp TUnknown [] vv'.
  Proof.
    auto.
  Qed.

  Lemma back_cast_ar_all {A} {τi τf} (pC : cons_struct A τi τf) : back_cast_ar pC.
  Proof.
    induction pC; rewrite /𝓕c /𝓕 /back_cast_ar; iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    - rewrite /𝓕c /𝓕 extract_no_subs.
      destruct G.
      + (** TUnit *) rewrite unfold_fixpoint_interp_unknown1'.
        iDestruct "Hvv'" as "[Hvv'Unit|[Hpp'|[Hss'|[Hff'|Huu']]]]".
        * iDestruct "Hvv'Unit" as "%"; inversion H; clear v v' H H1 H2.
          admit.
        * iDestruct "Hpp'" as (v1 v1' v2 v2') "(% & #H1 & #H2)". simpl in H; inversion H; clear H H1 H2 v v'.
          repeat rewrite (refold_interp_unknown').
          admit.
        * iDestruct "Hss'" as "[H1 | H2]".
          -- iDestruct "H1" as (v1 v1') "[% Hv1v1']"; rewrite (refold_interp_unknown'); inversion H; clear H H1 H2 v v'.
             admit.
          -- iDestruct "H2" as (v2 v2') "[% Hv2v2']"; rewrite (refold_interp_unknown'); inversion H; clear H H1 H2 v v'.
             admit.
        * iDestruct "Hff'" as (f f') "[% Hff']". inversion H. clear H H1 H2 v v'.
          admit.
        * iDestruct "Huu'" as (u u') "[% H]"; rewrite (refold_interp_unknown'); inversion H; clear H H1 H2 v v'.
          admit.
        * constructor.
      + (** TProd *) admit.
      + (** TSum *) admit.
      + (** TArrow *) rewrite unfold_fixpoint_interp_unknown1'.
        iDestruct "Hvv'" as "[Hvv'Unit|[Hpp'|[Hss'|[Hff'|Huu']]] ]".
        * iDestruct "Hvv'Unit" as "%"; inversion H; clear v v' H H1 H2.
          admit.
        * iDestruct "Hpp'" as (v1 v1' v2 v2') "(% & #H1 & #H2)". simpl in H; inversion H; clear H H1 H2 v v'.
          repeat rewrite (refold_interp_unknown').
          admit.
        * iDestruct "Hss'" as "[H1 | H2]".
          -- iDestruct "H1" as (v1 v1') "[% Hv1v1']"; rewrite (refold_interp_unknown'); inversion H; clear H H1 H2 v v'.
             admit.
          -- iDestruct "H2" as (v2 v2') "[% Hv2v2']"; rewrite (refold_interp_unknown'); inversion H; clear H H1 H2 v v'.
             admit.
        * iDestruct "Hff'" as (f f') "[% Hff']". inversion H. clear H H1 H2 v v'.
          admit.
        * iDestruct "Huu'" as (u u') "[% H]"; rewrite (refold_interp_unknown'); inversion H; clear H H1 H2 v v'.
          admit.
        * constructor.
      + (** TRec *) rewrite unfold_fixpoint_interp_unknown1'.
        iDestruct "Hvv'" as "[Hvv'Unit|[Hpp'|[Hss'|[Hff'|Huu']]] ]".
        * iDestruct "Hvv'Unit" as "%"; inversion H; clear v v' H H1 H2.
          admit.
        * iDestruct "Hpp'" as (v1 v1' v2 v2') "(% & #H1 & #H2)". simpl in H; inversion H; clear H H1 H2 v v'.
          repeat rewrite (refold_interp_unknown').
          admit.
        * iDestruct "Hss'" as "[H1 | H2]".
          -- iDestruct "H1" as (v1 v1') "[% Hv1v1']"; rewrite (refold_interp_unknown'); inversion H; clear H H1 H2 v v'.
             admit.
          -- iDestruct "H2" as (v2 v2') "[% Hv2v2']"; rewrite (refold_interp_unknown'); inversion H; clear H H1 H2 v v'.
             admit.
        * iDestruct "Hff'" as (f f') "[% Hff']". inversion H. clear H H1 H2 v v'.
          admit.
        * iDestruct "Huu'" as (u u') "[% H]"; rewrite (refold_interp_unknown'); inversion H; clear H H1 H2 v v'.
          admit.
        * constructor.
    - rewrite /𝓕c /𝓕. rewrite embed_no_subs. destruct G.
      + iDestruct "Hvv'" as "%". simpl in H. inversion H. rewrite H0 H1. clear v v' H H0 H1.
        admit.
      + iDestruct "Hvv'" as ((v1 , v1') (v2 , v2')) "[% [H1 H2]]". simpl in H; inversion H; clear H H1 H2 v v'.
        admit.
      + iDestruct "Hvv'" as "[H1 | H2]".
        * iDestruct "H1" as ((v1 , v1')) "[% H1]".
          simpl in H; inversion H; clear H H1 H2 v v'.
          admit.
        * iDestruct "H2" as ((v2 , v2')) "[% H2]".
          simpl in H; inversion H; clear H H1 H2 v v'.
          admit.
      + admit.
      + admit.
    - admit.
    - admit.
    - iDestruct "Hvv'" as "%"; inversion H. simpl in *. rewrite H0 H1. clear v v' H H0 H1.
      asimpl. wp_head.
      iMod (step_pure _ ei' K'
                      (Cast Unit TUnit TUnit)
                      Unit with "[Hv']") as "Hv'". intros. eapply IdBase. by simpl. auto.
      iSplitR. done. done. asimpl. wp_value. iExists UnitV. iSplitL. done. done.
    - asimpl. wp_head.
      iMod (step_pure _ ei' K'
                      (Cast (# v') ⋆ ⋆)
                      (# v') with "[Hv']") as "Hv'". intros. eapply IdStar. by simpl. auto.
      iSplitR. done. done. asimpl. wp_value. iExists v'. iSplitL. done. done.
    - admit.
    - iDestruct "Hvv'" as ((v1, v1') (v2, v2')) "(% & #H1 & #H2)". simpl in H; inversion H; clear H H1 H2 v v'.
      iDestruct "Hfs" as "[% Hfs']"; iAssert (rel_cast_functions A fs) with "[Hfs']" as "Hfs". iSplit; done. iClear "Hfs'".
      fold interp.
      rewrite /𝓕c /𝓕.
      rewrite between_TProd_subst_rewrite.
      fold (𝓕 pC1) (𝓕 pC2).
      fold (𝓕c pC1 fs) (𝓕c pC2 fs).
      wp_head. asimpl.
      rewrite 𝓕c_rewrite.
      (** boring steps implementation side *)
      iApply (wp_bind (fill $ [stlc_mu.lang.AppRCtx _ ; stlc_mu.lang.PairLCtx _])).
      wp_head. wp_value. simpl.
      iApply (wp_bind (fill $ [stlc_mu.lang.PairLCtx _])).
      (** boring steps specification side *)
      iMod (step_pure _ ei' K'
                      (Cast (Pair (# v1') (# v2')) (τ1 × τ2) (τ1' × τ2'))
                      (Pair (Cast (Fst (Pair (# v1') (# v2'))) τ1 τ1') (Cast (Snd (Pair (# v1') (# v2'))) τ2 τ2')) with "[Hv']") as "Hv'".
      intros. eapply ProdCast. by simplify_option_eq. auto. iSplitR; try done.
      iMod (step_pure _ ei' (CastCtx τ1 τ1' :: PairLCtx _ :: K')
                      (Fst (Pair (# v1') (# v2')))
                      (# v1') with "[Hv']") as "Hv'".
      intros. eapply FstS. by rewrite to_of_val. by rewrite to_of_val. auto. iSplitR; try done. simpl.
      (** first IH *)
      iApply (wp_wand with "[Hv']").
      rewrite -𝓕c_rewrite.
      iApply (IHpC1 ei' (PairLCtx _ :: K') with "[Hv']").
      iSplitR; try done.
      iSplitR; try done.
      iSplitR; try done.
      iIntros (v1f) "HHH". iDestruct "HHH" as (v1f') "[Hv2' #Hv1fv1f']".
      (** boring steps implementation side *)
      rewrite 𝓕c_rewrite.
      iApply (wp_bind (fill $ [stlc_mu.lang.AppRCtx _ ; stlc_mu.lang.PairRCtx _])).
      wp_head. wp_value. simpl.
      (** boring steps specification side *)
      iMod (step_pure _ ei' (CastCtx τ2 τ2' :: PairRCtx _ :: K')
                      (Snd (Pair (# v1') (# v2')))
                      (# v2') with "[Hv2']") as "Hv2'".
      intros. eapply SndS. by rewrite to_of_val. by rewrite to_of_val. auto. iSplitR; try done. simpl.
      (** second IH *)
      iApply (wp_bind (fill $ [stlc_mu.lang.PairRCtx _])).
      iApply (wp_wand with "[-]").
      rewrite -𝓕c_rewrite.
      iApply (IHpC2 ei' (PairRCtx _ :: K') with "[Hv2']").
      (** easy *)
      iSplitR; try done.
      iSplitR; try done.
      iSplitR; try done.
      iIntros (v2f) "HHH". iDestruct "HHH" as (v2f') "[Hvf #Hv2fv2f']". simpl.
      wp_value.
      iExists (PairV v1f' v2f'). iSplitL. done.
      iExists (v1f , v1f') , (v2f , v2f') . iSplitR. done. by iSplit.
    - fold interp.
      rename v into f. rename v' into f'. iDestruct "Hv'" as "Hf'". iDestruct "Hvv'" as "Hff'". iClear "Hvv'".
      rewrite /𝓕c /𝓕.
      fold (𝓕 pC1) (𝓕 pC2).
      rewrite between_TArrow_subst_rewrite.
      fold (𝓕c pC1 fs) (𝓕c pC2 fs).
      iDestruct "Hfs" as "[% Hfs']"; iAssert (rel_cast_functions A fs) with "[Hfs']" as "Hfs". iSplit; done. iClear "Hfs'".
      do 2 rewrite 𝓕c_rewrite.
      unfold between_TArrow.
      wp_head.
      asimpl.
      iApply wp_value.
      iExists (CastV f' (TArrow τ1 τ2) (TArrow τ3 τ4) (Between_arrow_types τ1 τ2 τ3 τ4)).
      iSplitL "Hf'"; first done.
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
                      (App (Cast (# f') (TArrow τ1 τ2) (TArrow τ3 τ4)) (# a'))
                      (Cast (App (# f') (Cast (# a') τ3 τ1)) τ2 τ4) with "[Hf']") as "Hf'".
      intros. eapply AppCast; try by rewrite -to_of_val. auto. by iFrame.
      (** first IH for the arguments *)
      iApply (wp_bind (fill $ [stlc_mu.lang.AppRCtx _ ; stlc_mu.lang.AppRCtx _])).
      iApply (wp_wand with "[-]").
      rewrite -𝓕c_rewrite.
      iApply (IHpC1 ei' (AppRCtx f' :: CastCtx τ2 τ4 :: K') with "[Hf']").
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
      iApply (wp_bind (fill $ [stlc_mu.lang.AppRCtx _ ])).
      iApply (wp_wand with "[-]").
      iDestruct ("Hff'" with "Hbb'") as "Hfbf'b' /=".
      iApply ("Hfbf'b'" $! (CastCtx τ2 τ4 :: K')).
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
    - (** setting up iLöb *)
      (* iLöb as "IHlob" forall (v v' ei') "Hvv' Hei'". *)
      fold (𝓕c (consTRecTRecExposeCall A τl τr pμτlμτrnotA pC) fs).
      (* iRevert (ei' K' v v') "Hvv' Hei' Hv'". *)
      rewrite /𝓕c /𝓕.
      fold (𝓕 pC).
      (** rewriting value relation for v and v' *)
      rewrite fixpoint_interp_rec1_eq.
      iDestruct "Hvv'" as ([w w']) "#[% Hww']".
      inversion H; clear v v' H H1 H2.
      fold interp.
      fold (interp_rec ⟦ τl ⟧ []).
      assert (bydef : interp_rec ⟦ τl ⟧ [] = ⟦ TRec τl ⟧ []); auto; rewrite bydef. clear bydef.
      rewrite (interp_subst [] τl (TRec τl) (w, w')).
      (** evaluation steps in WP *)
      (* applying to value v *)
      iApply wp_pure_step_later; auto; iNext.
      (* bringing subs of fs inwards *)
      rewrite rewrite_subs_app.
      do 2 rewrite Fix''_subs_rewrite.
      asimpl.
      (* evaluation step of the Fix'' itself *)
      iApply (wp_bind (stlc_mu.lang.fill_item $ stlc_mu.lang.AppLCtx _)).
      iApply wp_fix''.
      (** easy steps *)
      iApply wp_pure_step_later; auto; iNext.
      do 2 iNext.
      iApply wp_value.
      iApply wp_pure_step_later; auto; iNext. (* unfold fold w *)
      (** rewriting *)
      asimpl.
      assert (H :
                (stlc_mu.lang.Lam
                   (stlc_mu.lang.Unfold
                      (stlc_mu.lang.Fold
                         (stlc_mu.lang.Lam
                            (stlc_mu.lang.Lam
                               (stlc_mu.lang.Lam
                                  (stlc_mu.lang.Fold
                                     ((𝓕 pC).[ids 1
                                                  .: stlc_mu.typing.env_subst fs >>
                                                  ren (+4)]
                                               (stlc_mu.lang.Unfold (ids 0)))))
                               (stlc_mu.lang.Lam
                                  (stlc_mu.lang.Unfold (ids 1) (ids 1) (ids 0))))))
                      (stlc_mu.lang.Fold
                         (stlc_mu.lang.Lam
                            (stlc_mu.lang.Lam
                               (stlc_mu.lang.Lam
                                  (stlc_mu.lang.Fold
                                     ((𝓕 pC).[ids 1
                                                  .: stlc_mu.typing.env_subst fs >>
                                                  ren (+4)]
                                               (stlc_mu.lang.Unfold (ids 0)))))
                               (stlc_mu.lang.Lam
                                  (stlc_mu.lang.Unfold (ids 1) (ids 1) (ids 0))))))
                      (ids 0)) = (between_TRec' (𝓕 pC)).[stlc_mu.typing.env_subst fs] )
             ). by asimpl. rewrite H; clear H.
      rewrite between_TRec'_subst_rewrite.
      rewrite between_TRec'_to_value.
      assert (H : (𝓕 pC).[stlc_mu.lang.of_val (between_TRecV' (𝓕 pC).[up (stlc_mu.typing.env_subst fs)]) .: stlc_mu.typing.env_subst fs] = (𝓕 pC).[stlc_mu.typing.env_subst (between_TRecV' (𝓕 pC).[up (stlc_mu.typing.env_subst fs)] :: fs)]); first by simpl. rewrite H; clear H.
      (** easy steps *)
      iApply (wp_bind (stlc_mu.lang.fill_item $ stlc_mu.lang.FoldCtx)).
      iDestruct "Hfs" as "[% Hfs']"; iAssert (rel_cast_functions A fs) with "[Hfs']" as "Hfs". iSplit; done.
      (* iDestruct "Hfs" as "[% Hfs]". *)
      assert (Hs : length ((TRec τl, TRec τr) :: A) =
                  length
                    (between_TRecV'
                       (𝓕 pC).[up (stlc_mu.typing.env_subst fs)] :: fs)). simpl; auto.
      fold (𝓕c pC (between_TRecV' (𝓕 pC).[up (stlc_mu.typing.env_subst fs)] :: fs)).
      (* fold (𝓕c (consTRecTRecExposeCall A τl τr pμτlμτrnotA pC) fs). *)
      rewrite 𝓕c_rewrite.
      iApply (wp_bind (stlc_mu.lang.fill_item $ stlc_mu.lang.AppRCtx _)).
      iApply wp_pure_step_later; auto; iNext.
      iApply wp_value.
      simpl. (** hmmm; unfolds IHLöb... *)
      (** rewriting stuff *)
      rewrite -𝓕c_rewrite /𝓕c.
      assert (T : between_TRecV' (𝓕 pC).[up (stlc_mu.typing.env_subst fs)] =
                  (𝓕cV (consTRecTRecExposeCall A τl τr pμτlμτrnotA pC) fs H)
             ). {
        apply stlc_mu.lang.of_val_inj.
        rewrite -between_TRec'_to_value.
        rewrite -between_TRec'_subst_rewrite.
        by simpl.
        (* rewrite -𝓕c_rewrite. rewrite /𝓕c. *)
        (* by simpl. *)
      } rewrite T. clear T.
      (** eval specification side *)
      iMod (step_pure _ ei' K'
                      (Cast (Fold w') (TRec τl) (TRec τr))
                      (Fold (Cast (Unfold (Fold w')) (τl.[TRec τl/]) (τr.[TRec τr/]))) with "[Hv']") as "Hv'".
      intros. apply (RecursiveCast _ (FoldV w')). by rewrite -to_of_val. auto. by iFrame.
      iMod (step_pure _ ei' (CastCtx τl.[TRec τl/] τr.[TRec τr/] :: FoldCtx :: K')
                      (Unfold (Fold (# w')))
                      w' with "[Hv']") as "Hv'".
      intros. apply (Unfold_Fold _ w'). by rewrite to_of_val. auto. by iFrame.
      (** apply IH *)
      iApply (wp_wand with "[-]").
      iApply (IHpC ei' (FoldCtx :: K') w w' (𝓕cV (consTRecTRecExposeCall A τl τr pμτlμτrnotA pC) fs H :: fs)). iSplitL "Hfs". iSplitR; first by done.
      (** applying IHlob and Hfs *)
      admit.
      (** other *)
      iSplitR. done. iSplitR. done. by simpl.
      (** finish *)
      iIntros (v) "H".
      iDestruct "H" as (v') "[Hv' #Hvv']".
      iApply wp_value.
      iExists (FoldV v').
      iFrame.
      rewrite fixpoint_interp_rec1_eq.
      simpl. iModIntro.
      iExists (v , v').
      iSplitR. done.
      iNext.
      by rewrite (interp_subst [] τr (TRec τr) (v, v')).
    - 
      rewrite /𝓕c /𝓕. asimpl.
      (** getting the information about the length of the list *)
      iDestruct "Hfs" as "[% Hfs']".
      (* iAssert (rel_cast_functions A fs) with "[Hfs']" as "Hfs". iSplit; done. *)

      destruct (fs !! i) as [f | abs] eqn:Hf.
      + simpl.
        rewrite (stlc_mu.typing.env_subst_lookup _ i f); try done.
        iDestruct (big_sepL_lookup_acc _  i with "Hfs'") as "HHHH". apply Hf.


        iDestruct (big_sepL_lookup_acc (∀ (v0 : stlc_mu.lang.val) (v'0 : val),
            ⟦ TRec τl ⟧ [] (v0, v'0) → ⟦ TRec τr ⟧ₑ [] (f ( v0), Cast (# v'0) (TRec τl) (TRec τr))) _ i with "Hfs'") as "HHHH". apply Hf.

j/sep
        jkjjk


      + assert (Hi : i < length fs). rewrite -H. by eapply lookup_lt_Some.
        assert (Hi' : i >= length fs). by apply lookup_ge_None_1. exfalso. lia.


  Admitted.






        fold interp_unknown1 interp_unknown.
        rewrite interp_unknown_unfold /interp_unknown1; iDestruct "Hvv'" as "#Hvv'"; iDestruct "Hvv'" as "[Hvv'Unit|[Hpp'|[Hss'|[Hff'|Hur']]] ]"; fold interp_unknown1 interp_unknown.
        * iDestruct "Hvv'Unit" as ((w , w')) "[% Hww']"; simpl in H; inversion H; clear v v' H H1 H2.
          asimpl.
          iApply wp_pure_step_later; auto; iNext; asimpl.
          iDestruct "Hww'" as "%"; inversion H; rewrite H0 H1; clear w w' H H0 H1.
          iApply (wp_bind (stlc_mu.lang.fill_item $ stlc_mu.lang.CaseCtx _ _)).
          iApply wp_pure_step_later; auto; iNext.
          iApply wp_value.
          iApply wp_pure_step_later; auto; iNext.
          iApply wp_pure_step_later; auto; iNext. asimpl.
          iApply wp_pure_step_later; auto; iNext.
          iApply wp_pure_step_later; auto; iNext. asimpl.
          iMod (step_pure _ ei' K' (Cast (Cast Unit TUnit ⋆) ⋆ TUnit) (# UnitV) with "[Hv']") as "HHHH"; intros; auto.
          apply Same_Ground with (v := UnitV ); auto; constructor.
          iApply wp_value.
          iExists UnitV.
          by repeat iFrame.
        * (* diverging branch *)
          iDestruct "Hpp'" as ((p , p')) "[% Hpp']"; simpl in H; inversion H; clear H H1 H2 v v'.
          asimpl.
          iApply wp_pure_step_later; auto; iNext; asimpl.
          iDestruct "Hpp'" as ((v1 , v1') (v2 , v2')) "[% [Hv1v1' Hv2v2']]"; simpl in H; inversion H; clear H H1 H2 p p'.
          iApply (wp_bind (stlc_mu.lang.fill_item $ stlc_mu.lang.CaseCtx _ _)).
          iApply wp_pure_step_later; auto; iNext.
          iApply wp_value.
          iApply wp_pure_step_later; auto; iNext; asimpl.
          iApply wp_pure_step_later; auto; iNext; asimpl.
          iApply wp_pure_step_later; auto; iNext. asimpl.
          by iApply wp_Ω.
        * admit.
        * admit.
        * iDestruct "Hur'" as ((u , r')) "[% Hr]". simpl in H. inversion H. clear H H1 H2.
          admit.
      + rewrite interp_unknown_unfold /interp_unknown1; iDestruct "Hvv'" as "#Hvv'"; iDestruct "Hvv'" as "[Hvv'Unit|[Hpp'|[Hss'|[Hff'|Hur']]] ]"; fold interp_unknown1 interp_unknown.
        * (* diverging branch *)
          iDestruct "Hvv'Unit" as ((w , w')) "[% Hww']"; simpl in H; inversion H; clear v v' H H1 H2.
          asimpl.
          iApply wp_pure_step_later; auto; iNext; asimpl.
          iDestruct "Hww'" as "%"; inversion H; rewrite H0 H1; clear w w' H H0 H1.
          iApply (wp_bind (stlc_mu.lang.fill_item $ stlc_mu.lang.CaseCtx _ _)).
          iApply wp_pure_step_later; auto; iNext.
          iApply wp_value.
          iApply (wp_bind (stlc_mu.lang.fill_item $ stlc_mu.lang.CaseCtx _ _)).
          iApply wp_value.
          iApply wp_pure_step_later; auto; iNext.
          iApply wp_pure_step_later; auto; iNext. asimpl.
          iApply wp_pure_step_later; auto; iNext. asimpl.
          by iApply wp_Ω.
        * iDestruct "Hpp'" as ((p , p')) "[% Hpp']"; simpl in H; inversion H; clear H H1 H2.
          asimpl.
          iApply wp_pure_step_later; auto; iNext; asimpl.
          iDestruct "Hpp'" as ((v1 , v1') (v2 , v2')) "[% [Hv1v1' Hv2v2']]"; simpl in H; inversion H; clear H H1 H2 p p'.
          iApply (wp_bind (stlc_mu.lang.fill_item $ stlc_mu.lang.CaseCtx _ _)).
          iApply wp_pure_step_later; auto; iNext.
          iApply wp_value.
          iApply wp_pure_step_later; auto; iNext; asimpl.
          iApply wp_pure_step_later; auto; iNext; asimpl.
          iApply wp_pure_step_later; auto; iNext. asimpl.
          iMod (step_pure _ ei' K'
                          (Cast
                             (Cast (Pair (# v1') (# v2'))
                                   (⋆ × ⋆) ⋆) ⋆
                             (⋆ × ⋆)
                          )
                          (Pair (# v1') (# v2'))
                  with "[Hv']") as "HHHH"; auto.
          intro. eapply Same_Ground. simplify_option_eq. auto. constructor.
          iApply wp_value.
          iExists (PairV (v1') (v2')).
          simpl. repeat iFrame.
          iExists (v1 , v1') , (v2 , v2'). by auto.
        * admit.
        * admit.
        * admit.
      + admit.
      + admit.
      + rewrite interp_unknown_unfold /interp_unknown1; iDestruct "Hvv'" as "#Hvv'"; iDestruct "Hvv'" as "[Hvv'Unit|[Hpp'|[Hss'|[Hff'|Hur']]] ]"; fold interp_unknown1 interp_unknown.
        * admit.
        * admit.
        * admit.
        * admit.
        * iDestruct "Hur'" as ((u , r')) "[% Hur']"; inversion H; clear H H1 H2.
          iMod (step_pure _ ei' K'
                          (Cast (# castupV_TRec r') ⋆ (TRec ⋆))
                          (# r')
                  with "[Hv']") as "HHHH"; auto.
          intro; eapply Same_Ground; simplify_option_eq; auto; constructor.
          iApply wp_pure_step_later; auto; iNext; asimpl.
          iApply (wp_bind (stlc_mu.lang.fill_item $ stlc_mu.lang.CaseCtx _ _)).
          iApply wp_pure_step_later; auto.
          iApply wp_value. simpl. 
          iApply wp_pure_step_later; auto. asimpl. 
          iApply wp_value.
          repeat iNext.
          iExists r'. by iFrame.
    - destruct G; rewrite /𝓕c /𝓕.
      + iApply wp_pure_step_later; auto; iNext; asimpl.
        iDestruct "Hvv'" as "%"; inversion H. rewrite H0 H1. clear H H0 H1 v v'.
        iApply wp_value. iExists (CastV UnitV TUnit ⋆ (From_ground_to_unknown TUnit Ground_TUnit)).
        simpl in *.
        iFrame.
        rewrite interp_unknown_unfold /interp_unknown1.
        admit.
      + admit.
      + admit.
      + admit.
      + rewrite fixpoint_interp_rec1_eq.
        iDestruct "Hvv'" as ((r , r')) "[% #Hrr']". inversion H; clear H H1 H2.
        iApply wp_pure_step_later; auto; iNext; asimpl.
        iApply (wp_bind (fill [stlc_mu.lang.InjRCtx ; stlc_mu.lang.FoldCtx ])).
        iApply wp_pure_step_later; auto. iNext; asimpl.
        iApply wp_value.
        iApply wp_value.
        iExists (CastV (FoldV r') (TRec ⋆) ⋆ (From_ground_to_unknown (TRec ⋆) Ground_TRec)).
        simpl in *.
        iFrame.
        rewrite{1} interp_unknown_unfold.
        rewrite{1} interp_unknown_unfold.
        repeat rewrite{1} /interp_unknown1.
        iRight.
        iRight.
        iRight.
        iRight.
        iModIntro.
        iExists (r , FoldV r'). simpl. iSplitL.
        auto.
        admit.
    - admit.
    - admit.
    - rewrite /𝓕c /𝓕. asimpl.
      iApply wp_pure_step_later; auto.
      asimpl.
      iDestruct "Hvv'" as %[eq1 eq2]; simplify_eq.
      iNext.
      iMod (step_pure _ ei' K' (Cast (# UnitV) TUnit TUnit) (# UnitV) with "[Hv']") as "HHHH"; auto.
      intros; by eapply IdBase.
      iApply wp_value.
      iExists UnitV. iFrame. iSplit; trivial.
    - rewrite /𝓕c /𝓕; asimpl.
      iMod (step_pure _ ei' K' (Cast (# v') ⋆ ⋆) (# v') with "[Hv']") as "Hv'"; auto.
      intros; by eapply IdStar.
      iApply wp_pure_step_later; auto; asimpl.
      iNext.
      iApply wp_value.
      iExists v'. iFrame.
    - iDestruct "Hvv'" as "[Hvv'1 | Hvv'2]".
      + iDestruct "Hvv'1" as (vv'1) "Hvv'1". destruct vv'1 as (v1 , v1').
        iDestruct "Hvv'1" as "[% Hvv'1]". inversion H.
        iMod (step_pure _ ei' K' (Cast (# InjLV v1') (τ1 + τ2)%type (τ1' + τ2')%type) _ with "[Hv']") as "Hv'"; auto; try (intros; eapply SumCast; auto).
        iMod ((step_case_inl _ ei' K' (# v1')) with "[Hv']") as "Hv'"; auto.
        (* rewrite /𝓕c /𝓕 /between_TSum. *)
        rewrite /𝓕c /𝓕.
        iApply wp_pure_step_later. auto; asimpl.
        iApply wp_pure_step_later; auto; asimpl.
        iNext. iNext.
        iApply wp_bind. admit.
        iApply wp_wand_r.
        iSplitL.
        iApply (IHpC1 ei' (InjLCtx :: K')). repeat iFrame. auto.
        clear H H1 H2 v1 v1'.
        iIntros (v1) "HHH". iDestruct "HHH" as (v1') "[Hv1' Hvv'1]".
        iApply wp_value.
        iExists (InjLV v1'). repeat iFrame. iLeft. iExists (v1 , v1').
        iSplitR. by simpl. done.
      + admit.
    - iSimpl in "Hvv'". iDestruct "Hvv'" as ((v1 , v1') (v2 , v2')) "[% [Hv1v1' Hv2v2']]". simpl in H; inversion H; clear H H1 H2 v v'.
      iApply wp_pure_step_later; auto.
      fold (𝓕 pC1) (𝓕 pC2). asimpl. fold (𝓕c pC1 fs) (𝓕c pC2 fs).
      iDestruct "Hfs" as "[% Hfs']"; iAssert (rel_cast_functions A fs) with "[Hfs']" as "Hfs". iSplit; done.
      rewrite 𝓕c_rewrite.
      iApply (wp_bind (fill [stlc_mu.lang.AppRCtx (𝓕cV pC1 fs H) ; stlc_mu.lang.PairLCtx ((𝓕c pC2 fs) (stlc_mu.lang.Snd (stlc_mu.lang.Pair (stlc_mu.lang.of_val v1) (stlc_mu.lang.of_val v2)))) ])).
      iApply wp_pure_step_later; auto.
      do 2 iNext. iApply wp_value. simpl.
      iApply (wp_bind (fill [stlc_mu.lang.PairLCtx ((𝓕c pC2 fs) (stlc_mu.lang.Snd (stlc_mu.lang.Pair (stlc_mu.lang.of_val v1) (stlc_mu.lang.of_val v2)))) ])).
      rewrite -𝓕c_rewrite.
      iApply (wp_wand with "[Hfs Hv1v1' Hei' Hv']").
      (* iApply (IHpC1 ei' :: K' with "Hfs Hv1v1' Hei' Hv'"). *)
      admit.
      admit.
    - admit.
    - rewrite /𝓕c /𝓕.
      fold (𝓕 pC).
      iApply wp_pure_step_later; auto; asimpl.
      iApply (wp_bind $ stlc_mu.lang.fill_item $ stlc_mu.lang.AppLCtx _).
      iApply wp_pure_step_later; auto; asimpl.
      iApply wp_pure_step_later; auto; asimpl.

    - rewrite /𝓕c /𝓕. asimpl.
      destruct (fs !! i) as [f | abs] eqn:Hf.
      + rewrite (stlc_mu.typing.env_subst_lookup _ _ f); auto.
        iDestruct "Hfs" as "[% Hfs]".
        rewrite fixpoint_interp_rec1_eq.
        
        rewrite interp_unknown_unfold /interp_unknown1.
        unfold fixpoint_re
        iAssert 
        
    destruct ()


End compat_cast_all.
