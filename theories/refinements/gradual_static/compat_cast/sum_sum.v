From fae_gtlc_mu.stlc_mu Require Export types typing.
From fae_gtlc_mu.cast_calculus Require Export lang.
From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import lifting.
From fae_gtlc_mu.backtranslation Require Export cast_help.general cast_help.extract cast_help.embed.
From fae_gtlc_mu.stlc_mu Require Export lang.
From fae_gtlc_mu.refinements.gradual_static Require Export logical_relation resources_left resources_right compat_easy compat_cast.defs.
From fae_gtlc_mu.cast_calculus Require Export consistency.structural types.

Section compat_cast_sum_sum.
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

  (** Proving it *)

  (* Lemma rewrite_subs_app (e1 e2 : expr) σ : *)
  (*   (App e1 e2).[σ] = App e1.[σ] e2.[σ]. *)
  (* Proof. *)
  (*     by simpl. *)
  (* Qed. *)

  Hint Resolve to_of_val : core.

  Hint Extern 5 (AsVal _) => eexists; simpl; try done; eapply cast_calculus.lang.of_to_val; fast_done : typeclass_instances.
  Hint Extern 10 (AsVal _) =>
  eexists; rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

  Lemma back_cast_ar_sum_sum:
    ∀ (A : list (type * type)) (τ1 τ1' τ2 τ2' : type) (pC1 : cons_struct A τ1 τ1') (pC2 : cons_struct A τ2 τ2')
      (IHpC1 : back_cast_ar pC1) (IHpC2 : back_cast_ar pC2),
      back_cast_ar (consTSumTSum A τ1 τ1' τ2 τ2' pC1 pC2).
  Proof.
    intros A τ1 τ1' τ2 τ2' pC1 pC2 IHpC1 IHpC2.
    rewrite /back_cast_ar. iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    iDestruct "Hfs" as "[% Hfs']"; iAssert (rel_cast_functions A fs) with "[Hfs']" as "Hfs". iSplit; done. iClear "Hfs'".
    rewrite /𝓕c /𝓕. fold (𝓕 pC1) (𝓕 pC2). rewrite between_TSum_subst_rewrite /between_TSum.
    iMod ((step_lam _ ei' K') with "[Hv']") as "Hv'"; auto. simpl.
    rewrite interp_rw_TSum.
    iDestruct "Hvv'" as "[H1 | H2]".
    + iDestruct "H1" as ((v1 , v1')) "[% Hv1v1']". inversion H0. clear H0 H2 H3 v v'.
      iMod ((step_case_inl _ ei' K') with "[Hv']") as "Hv'"; auto. asimpl.
      wp_head.
      iApply (wp_bind [cast_calculus.lang.InjLCtx]).
      iApply (wp_wand with "[-]").
      iApply (IHpC1 ei' (InjLCtx :: K') with "[Hv']"); iFrame; auto.
      iIntros (v1f) "HHH". iDestruct "HHH" as (v1f') "[Hv1f' Hv1fv1f']".
      iApply wp_value.
      iExists (InjLV v1f').
      iSplitL "Hv1f'". done.
      rewrite interp_rw_TSum.
      iLeft. iExists (v1f , v1f'). by iFrame.
    + iDestruct "H2" as ((v1 , v1')) "[% Hv1v1']". inversion H0. clear H0 H2 H3 v v'.
      iMod ((step_case_inr _ ei' K') with "[Hv']") as "Hv'"; auto. asimpl.
      wp_head.
      iApply (wp_bind [cast_calculus.lang.InjRCtx]).
      iApply (wp_wand with "[-]").
      iApply (IHpC2 ei' (InjRCtx :: K') with "[Hv']"); iFrame; auto.
      iIntros (v2f) "HHH". iDestruct "HHH" as (v2f') "[Hv2f' Hv2fv2f']".
      iApply wp_value.
      iExists (InjRV v2f').
      iSplitL "Hv2f'". done.
      rewrite interp_rw_TSum.
      iRight. iExists (v2f , v2f'). by iFrame.
  Qed.


End compat_cast_sum_sum.
