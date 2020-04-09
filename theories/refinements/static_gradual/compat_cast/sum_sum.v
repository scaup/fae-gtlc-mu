From fae_gtlc_mu.refinements.static_gradual Require Export tactics_left logical_relation resources_right compat_easy help_left compat_cast.defs.
From fae_gtlc_mu.cast_calculus Require Export types typing.
From fae_gtlc_mu.stlc_mu Require Export lang.
From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import lifting.
From fae_gtlc_mu.cast_calculus Require Export consistency.structural.definition.
From fae_gtlc_mu.backtranslation Require Export cast_help.general cast_help.extract cast_help.embed.
From fae_gtlc_mu.cast_calculus Require Export lang types.

Section compat_cast_sum_sum.
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

  Lemma back_cast_ar_sum_sum:
    ∀ (A : list (type * type)) (τ1 τ1' τ2 τ2' : type) (pC1 : A ⊢ τ1 ~ τ1') (pC2 : A ⊢ τ2 ~ τ2')
      (IHpC1 : back_cast_ar pC1) (IHpC2 : back_cast_ar pC2),
      back_cast_ar (consTSumTSum A τ1 τ1' τ2 τ2' pC1 pC2).
  Proof.
    intros A τ1 τ1' τ2 τ2' pC1 pC2 IHpC1 IHpC2.
    rewrite /back_cast_ar. iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    iDestruct "Hfs" as "[% Hfs']"; iAssert (rel_cast_functions A fs) with "[Hfs']" as "Hfs". iSplit; done. iClear "Hfs'".
    rewrite /𝓕c /𝓕. fold (𝓕 pC1) (𝓕 pC2). rewrite between_TSum_subst_rewrite.
    wp_head. asimpl.
    iMod (step_pure _ ei' K'
                    (Cast (# v') (τ1 + τ2)%type (τ1' + τ2')%type)
                    (Case (# v') (InjL (Cast (Var 0) τ1 τ1')) (InjR (Cast (Var 0) τ2 τ2'))) with "[Hv']") as "Hv'".
    intros. eapply SumCast. by simplify_option_eq. auto. iSplitR; try done.
    iDestruct "Hvv'" as "[H1 | H2]".
    + iDestruct "H1" as ((v1 , v1')) "[% Hv1v1']". inversion H0. clear H0 H2 H3 v v'.
      wp_head. asimpl.
      iMod ((step_case_inl _ _ _ (# v1'))  with "[Hv']") as "Hv'". auto. iSplitR. try done. done.
      iApply (wp_bind (fill $ [stlc_mu.lang.InjLCtx])).
      iApply (wp_wand with "[-]").
      iApply (IHpC1 ei' (InjLCtx :: K') with "[Hv']").
      iSplitR; try done.
      iSplitR; try done.
      iSplitR; try done.
      iIntros (v1f) "HHH". iDestruct "HHH" as (v1f') "[Hv1f' Hv1fv1f']".
      wp_value.
      iExists (InjLV v1f').
      iSplitL "Hv1f'". done.
      iLeft. iExists (v1f , v1f'). by iFrame.
    + iDestruct "H2" as ((v1 , v1')) "[% Hv1v1']". inversion H0. clear H0 H2 H3 v v'.
      wp_head. asimpl.
      iMod ((step_case_inr _ _ K' (# v1'))  with "[Hv']") as "Hv'". auto. iSplitR. try done. simpl. done.
      iApply (wp_bind (fill $ [stlc_mu.lang.InjRCtx])).
      iApply (wp_wand with "[-]").
      iApply (IHpC2 ei' (InjRCtx :: K') with "[Hv']").
      iSplitR; try done.
      iSplitR; try done.
      iSplitR; try done.
      iIntros (v1f) "HHH". iDestruct "HHH" as (v1f') "[Hv1f' Hv1fv1f']".
      wp_value.
      iExists (InjRV v1f').
      iSplitL "Hv1f'". done.
      iRight. iExists (v1f , v1f'). by iFrame.
  Admitted.


End compat_cast_sum_sum.
