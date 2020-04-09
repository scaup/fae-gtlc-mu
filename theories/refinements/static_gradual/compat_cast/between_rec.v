From fae_gtlc_mu.refinements.static_gradual Require Export logical_relation resources_right compat_easy help_left compat_cast.defs tactics_left.
From fae_gtlc_mu.cast_calculus Require Export types typing.
From fae_gtlc_mu.cast_calculus Require Export lang.
From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import lifting.
From fae_gtlc_mu.cast_calculus Require Export consistency.structural.definition.
From fae_gtlc_mu.backtranslation Require Export cast_help.general cast_help.extract cast_help.embed.
From fae_gtlc_mu.cast_calculus Require Export lang types.
(* From iris.program_logic Require Import language. *)
(* Coercion stlc_mu.lang.of_val : stlc_mu.lang.val >-> stlc_mu.lang.expr. *)
(* Coercion cast_calculus.lang.of_val : cast_calculus.lang.val >-> cast_calculus.lang.expr. *)

(* Notation "# v" := (of_val v) (at level 20). *)

(* Coercion of_val : val >-> expr. *)

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

  (** Proving it *)

  Lemma refold_interp_unknown' vv' : fixpoint interp_unknown1' vv' ≡ interp TUnknown [] vv'.
  Proof.
    auto.
  Qed.

  Lemma back_cast_ar_trec_trec_use:
    ∀ (A : list (type * type)) (τl τr : {bind type}) (i : nat) (pμτlμtrinA : A !! i = Some (TRec τl, TRec τr)),
      back_cast_ar (consTRecTRecUseCall A τl τr i pμτlμtrinA).
  Proof.
    intros A τl τr i pμτlμtr.
    rewrite /𝓕c /𝓕 /back_cast_ar; iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    rewrite /𝓕c /𝓕. asimpl.
    (** getting the information about the length of the list *)
    iDestruct "Hfs" as "[% Hfs']".
    (* iAssert (rel_cast_functions A fs) with "[Hfs']" as "Hfs". iSplit; done. *)
    destruct (fs !! i) as [f | abs] eqn:Hf.
    rewrite (stlc_mu.typing.env_subst_lookup _ i f); try done.
    {
      iDestruct (big_sepL2_lookup with "Hfs'") as "#Hf". exact pμτlμtr. exact Hf.
      iApply ("Hf" $! v v' with "Hvv'"). done.
    }
    { (* trivially impossible case *)
      assert (Hi : i < length fs). rewrite -H. by eapply lookup_lt_Some.
      assert (Hi' : i >= length fs). by apply lookup_ge_None_1. exfalso. lia.
    }
  Qed.

  Lemma wp_fix'' (f : stlc_mu.lang.expr) Φ :
    ⊢ (▷ ▷ WP f (stlc_mu.lang.Lam (rename (+1) (Fix'' f) (stlc_mu.lang.Var 0)))   {{ Φ }} -∗ (WP (Fix'' f) {{ Φ }}))%I.
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


  Lemma back_cast_ar_trec_trec_expose:
    ∀ (A : list (type * type)) (τl τr : {bind type}) (pμτlμτrnotA : (TRec τl, TRec τr) ∉ A)
      (pC : ((TRec τl, TRec τr) :: A) ⊢ τl.[TRec τl/] ~ τr.[TRec τr/]) (IHpC : back_cast_ar pC),
      back_cast_ar (consTRecTRecExposeCall A τl τr pμτlμτrnotA pC).
  Proof.
    intros A τl τr pμτlμτrnotA pC IHpC.
    rewrite /𝓕c /𝓕 /back_cast_ar; iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    (** setting up iLöb *)
    iLöb as "IHlob" forall (v v' ei' K') "Hvv' Hei'".
    fold (𝓕c (consTRecTRecExposeCall A τl τr pμτlμτrnotA pC) fs).
    (* iRevert (ei' K' v v') "Hvv' Hei' Hv'". *)
    rewrite {2}/𝓕c. rewrite /𝓕.
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
    assert (triv :
              Fix'' (stlc_mu.lang.Lam (stlc_mu.lang.Lam (stlc_mu.lang.Fold (rename (+1) (𝓕 pC).[upn 1 (ren (+1))] (stlc_mu.lang.Unfold (stlc_mu.lang.Var 0)))))).[up (stlc_mu.typing.env_subst fs)].[stlc_mu.lang.of_val $ stlc_mu.lang.FoldV w/] (stlc_mu.lang.Var 0).[up (stlc_mu.typing.env_subst fs)].[stlc_mu.lang.of_val $ stlc_mu.lang.FoldV w/] = Fix'' (stlc_mu.lang.Lam (stlc_mu.lang.Lam (stlc_mu.lang.Fold ((𝓕 pC).[up (stlc_mu.typing.env_subst fs) >> ren (+1)] (stlc_mu.lang.Unfold (ids 0)))))) (stlc_mu.lang.Fold (w))). by asimpl. rewrite triv. clear triv.
    (* evaluation step of the Fix'' itself *)
    iApply (wp_bind (stlc_mu.lang.fill_item $ stlc_mu.lang.AppLCtx _)).
    iApply wp_fix''.
    (** easy steps *)
    iApply wp_pure_step_later; auto; iNext.
    do 2 iNext.
    iApply wp_value.
    iApply wp_pure_step_later; auto; iNext. (* unfold fold w *)
    (** rewriting *)

    assert (triv : ((stlc_mu.lang.Fold ((𝓕 pC).[up (stlc_mu.typing.env_subst fs) >> ren (+1)] (stlc_mu.lang.Unfold (ids 0)))).[up
                                                                                                                (stlc_mu.lang.Lam
                                                                                                                    (rename (+1)
                                                                                                                      (Fix''
                                                                                                                          (stlc_mu.lang.Lam
                                                                                                                            (stlc_mu.lang.Lam
                                                                                                                                (stlc_mu.lang.Fold
                                                                                                                                  ((𝓕 pC).[up
                                                                                                                                        (stlc_mu.typing.env_subst fs) >>
                                                                                                                                      ren (+1)]
                                                                                                                                      (stlc_mu.lang.Unfold (ids 0)))))))
                                                                                                                      (stlc_mu.lang.Var 0)) .: ids)].[stlc_mu.lang.Fold ( w)/]) = (stlc_mu.lang.Fold ((𝓕 pC).[(between_TRec' (𝓕 pC)).[stlc_mu.typing.env_subst fs] .: stlc_mu.typing.env_subst fs] (stlc_mu.lang.Unfold (stlc_mu.lang.Fold (w)))))).

    by asimpl. rewrite triv. clear triv.
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
    rewrite (𝓕c_rewrite pC).
    iApply (wp_bind (stlc_mu.lang.fill_item $ stlc_mu.lang.AppRCtx _)).
    iApply wp_pure_step_later; auto; iNext.
    iApply wp_value.
    fold (𝓕c (consTRecTRecExposeCall A τl τr pμτlμτrnotA pC) fs).
    simpl. (** hmmm; unfolds IHLöb... *)
    (** rewriting stuff *)
    rewrite -(𝓕c_rewrite pC) {2}/𝓕c.
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
    (* iApply (IHpC ei' (FoldCtx :: K') w w' (𝓕cV (consTRecTRecExposeCall A τl τr pμτlμτrnotA pC) fs H :: fs)). iSplitL "Hfs". iSplitR; first by done. *)
    (** applying IHlob and Hfs *)
    (* rewrite /𝓕c. *)
    iSplit.
    iModIntro. iIntros (v v') "#Hvv'".
    { clear K'. iIntros (K') "Hv'". iSimpl in "Hv'".
      rewrite -𝓕c_rewrite.
      iApply ("IHlob" $! v v' with "Hv' Hvv' Hei'").
    }
    done.
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
    (* trival shells here *)
  Admitted.


End between_rec.
