From fae_gtlc_mu.refinements.static_gradual Require Export logical_relation resources_right compat_easy help_left compat_cast.defs.
From fae_gtlc_mu.cast_calculus Require Export types typing.
From fae_gtlc_mu.stlc_mu Require Export lang.
From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import lifting.
From fae_gtlc_mu.cast_calculus Require Export consistency.structural.
From fae_gtlc_mu.backtranslation Require Export cast_help.general cast_help.extract cast_help.embed.
From fae_gtlc_mu.cast_calculus Require Export lang types.

Section compat_cast_prod_prod.
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

  (** Proving it *)

  (* Lemma rewrite_subs_app (e1 e2 : expr) σ : *)
  (*   (App e1 e2).[σ] = App e1.[σ] e2.[σ]. *)
  (* Proof. *)
  (*     by simpl. *)
  (* Qed. *)

  Lemma back_cast_ar_prod_prod:
    ∀ (A : list (type * type)) (τ1 τ1' τ2 τ2' : type) (pC1 : cons_struct A τ1 τ1') (pC2 : cons_struct A τ2 τ2')
      (IHpC1 : back_cast_ar pC1) (IHpC2 : back_cast_ar pC2),
      back_cast_ar (consTProdTProd A τ1 τ1' τ2 τ2' pC1 pC2).
  Proof.
    intros A τ1 τ1' τ2 τ2' pC1 pC2 IHpC1 IHpC2.
    rewrite /back_cast_ar. iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    iDestruct "Hfs" as "[% Hfs']"; iAssert (rel_cast_functions A fs) with "[Hfs']" as "Hfs". iSplit; done. iClear "Hfs'".
    rewrite /𝓕c /𝓕. fold (𝓕 pC1) (𝓕 pC2). rewrite between_TProd_subst_rewrite.
    rewrite interp_rw_TProd.
    iDestruct "Hvv'" as ((v1, v1') (v2, v2')) "(% & #H1 & #H2)". simpl in H0. inversion H0. clear H0 H2 H3 v v'.
    iDestruct "Hfs" as "[% Hfs']"; iAssert (rel_cast_functions A fs) with "[Hfs']" as "Hfs". iSplit; done. iClear "Hfs'".
    fold interp.
    fold (𝓕c pC1 fs) (𝓕c pC2 fs).

    wp_head. asimpl.
    rewrite 𝓕c_rewrite.
    (** boring steps implementation side *)
    iApply (wp_bind (ectx_language.fill $ [stlc_mu.lang.AppRCtx _ ; stlc_mu.lang.PairLCtx _])).
    wp_head. wp_value. simpl.
    iApply (wp_bind (ectx_language.fill $ [stlc_mu.lang.PairLCtx _])).
    (** boring steps specification side *)
    iMod (step_pure _ ei' K'
                    (Cast (Pair (# v1') (# v2')) (τ1 × τ2) (τ1' × τ2'))
                    (Pair (Cast (# v1') τ1 τ1') (Cast (# v2') τ2 τ2')) with "[Hv']") as "Hv'".
    intros. eapply ProdCast. by simplify_option_eq. auto. auto. eauto.
    (** first IH *)
    iApply (wp_wand with "[Hv' Hfs]").
    rewrite -𝓕c_rewrite.
    iApply (IHpC1 ei' (PairLCtx _ :: K') with "[Hv' Hfs]").
    iSplitL "Hfs"; try done.
    iSplitR; try done.
    iSplitR; try done.
    iIntros (v1f) "HHH". iDestruct "HHH" as (v1f') "[Hv2' #Hv1fv1f']".
    (** boring steps implementation side *)
    rewrite 𝓕c_rewrite.
    iApply (wp_bind (ectx_language.fill  $ [stlc_mu.lang.AppRCtx _ ; stlc_mu.lang.PairRCtx _])).
    wp_head. wp_value. simpl.
    (** second IH *)
    iApply (wp_bind (ectx_language.fill $ [stlc_mu.lang.PairRCtx _])).
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
    rewrite interp_rw_TProd.
    iExists (v1f , v1f') , (v2f , v2f') . iSplitR. done. by iSplit.
    Unshelve. all:apply hack.
Qed.

End compat_cast_prod_prod.
