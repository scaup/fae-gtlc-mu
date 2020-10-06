From fae_gtlc_mu.refinements.static_gradual Require Export logical_relation resources_right compat_easy compat_cast.defs.
From fae_gtlc_mu.cast_calculus Require Export types typing.
From fae_gtlc_mu.stlc_mu Require Export lang.
From fae_gtlc_mu.cast_calculus Require Export lang.
From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import lifting.
From fae_gtlc_mu.backtranslation.cast_help Require Export general_def general_def_lemmas extract embed.
From fae_gtlc_mu.cast_calculus Require Export types lang.

Section compat_cast_star_tau.
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

  Lemma back_cast_ar_star_tau:
    ∀ (A : list (type * type)) (τ τG : type) (pτnG : Ground τ → False) (pτnStar : τ ≠ ⋆) (pτSτG : get_shape τ = Some τG) (pC1 : alternative_consistency A ⋆ τG) (pC2 : alternative_consistency A τG τ),
      back_cast_ar pC1 → back_cast_ar pC2 → back_cast_ar (factorDown_Ground A τ τG pτnG pτnStar pτSτG pC1 pC2).
  Proof.
    intros A τ τG pτnG pτnStar pτSτG pC1 pC2 IHpC1 IHpC2.
    rewrite /back_cast_ar /𝓕c /𝓕. fold (𝓕 pC1). fold (𝓕 pC2).
    iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    iDestruct "Hfs" as "[% Hfs']"; iAssert (rel_cast_functions A fs) with "[Hfs']" as "Hfs". iSplit; done. iClear "Hfs'".
    wp_head. asimpl.
    fold (𝓕c pC1 fs). fold (𝓕c pC2 fs). do 2 rewrite 𝓕c_rewrite.
    iApply (wp_bind (ectx_language.fill $ [stlc_mu.lang.AppRCtx _])).
    iApply (wp_wand with "[-]").
    iMod (step_pure _ ei' K'
                    (Cast (# v') ⋆ τ)
                    (Cast (Cast (# v') ⋆ τG) τG τ) with "[Hv']") as "Hv'"; auto.
    { eapply DownFactorization; auto. }
    rewrite -𝓕c_rewrite.
    iApply (IHpC1 ei' (CastCtx τG τ :: K') with "[Hv']"); auto.
    iIntros (w) "blaa".  iDestruct "blaa" as (w') "[Hw' #Hww']".
    simpl.
    rewrite -𝓕c_rewrite.
    iApply (IHpC2 ei' K' with "[Hw']"); auto.
  Qed.

End compat_cast_star_tau.
