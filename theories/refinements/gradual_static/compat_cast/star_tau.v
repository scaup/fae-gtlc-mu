From fae_gtlc_mu.stlc_mu Require Export types typing.
From fae_gtlc_mu.cast_calculus Require Export lang.
From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import lifting.
From fae_gtlc_mu.backtranslation Require Export cast_help.general_def_lemmas.
From fae_gtlc_mu.stlc_mu Require Export lang.
From fae_gtlc_mu.refinements.gradual_static Require Export logical_relation resources_left resources_right compat_easy compat_cast.defs.
From fae_gtlc_mu.cast_calculus Require Export types.

Section compat_cast_star_tau.
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
  Hint Extern 5 (AsVal _) => eexists; simpl; try done; eapply cast_calculus.lang.of_to_val; fast_done : typeclass_instances.

  Lemma back_cast_ar_star_tau:
    ∀ (A : list (type * type)) (τ τG : type) (pτnG : Ground τ → False) (pτnStar : τ ≠ ⋆) (pτSτG : get_shape τ = Some τG) (pC1 : alternative_consistency A ⋆ τG) (pC2 : alternative_consistency A τG τ),
      back_cast_ar pC1 → back_cast_ar pC2 → back_cast_ar (factorDown_Ground A τ τG pτnG pτnStar pτSτG pC1 pC2).
  Proof.
    intros A τ τG pτnG pτnStar pτSτG pC1 pC2 IHpC1 IHpC2.
    iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    rewrite /back_cast_ar /𝓕c /𝓕. rewrite factorization_subst_rewrite. fold (𝓕 pC1). fold (𝓕 pC2).
    fold (𝓕c pC1 fs). fold (𝓕c pC2 fs). rewrite /factorization.
    iDestruct "Hfs" as "[% Hfs']"; iAssert (rel_cast_functions A fs) with "[Hfs']" as "Hfs". iSplit; done. iClear "Hfs'".
    (** implementation *)
    iApply wp_pure_step_later; try auto. apply pure_fact_down; auto. done. by eauto; eexists. simpl. done. iNext.
    (** specification *)
    iMod ((step_lam _ ei' K') with "[Hv']") as "Hv'"; auto. asimpl.
    (** first IH *)
    rewrite 𝓕c_rewrite.
    iApply (wp_bind [CastCtx _ _]). iApply (wp_wand with "[-]").
    iApply (IHpC1 ei' (AppRCtx _ :: K') with "[Hv']"); auto.
    (** .... *)
    iIntros (w) "blaa".  iDestruct "blaa" as (w') "[Hw' #Hww']".
    simpl. rewrite -𝓕c_rewrite.
    (** second IH *)
    iApply (wp_wand with "[-]").
    iApply (IHpC2 ei' K' with "[Hw']"); auto.
    auto.
  Qed.

End compat_cast_star_tau.
