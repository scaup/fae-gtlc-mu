From fae_gtlc_mu.refinements.static_gradual Require Export logical_relation resources_right compat_easy help_left compat_cast.defs.
From fae_gtlc_mu.cast_calculus Require Export types typing.
From fae_gtlc_mu.stlc_mu Require Export lang.
From fae_gtlc_mu.cast_calculus Require Export lang.
From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import lifting.
From fae_gtlc_mu.cast_calculus Require Export consistency.structural.
From fae_gtlc_mu.backtranslation Require Export cast_help.general cast_help.extract cast_help.embed.
From fae_gtlc_mu.cast_calculus Require Export lang types.

Section compat_cast_tau_star.
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

  Lemma back_cast_ar_tau_star:
    ∀ (A : list (type * type)) (τ τG : type) (pτnG : Ground τ → False) (pτnStar : τ ≠ ⋆) (pτSτG : get_shape τ = Some τG) (pC1 : cons_struct A τ τG) (pC2 : cons_struct A τG ⋆),
      back_cast_ar pC1 → back_cast_ar pC2 → back_cast_ar (consTauStar A τ τG pτnG pτnStar pτSτG pC1 pC2).
  Proof.
    intros A τ τG pτnG pτnStar pτSτG pC1 pC2 IHpC1 IHpC2.
    rewrite /back_cast_ar /𝓕c /𝓕. fold (𝓕 pC1). fold (𝓕 pC2).
    iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    iDestruct "Hfs" as "[% Hfs']"; iAssert (rel_cast_functions A fs) with "[Hfs']" as "Hfs". iSplit; done. iClear "Hfs'".
    wp_head. asimpl.
    fold (𝓕c pC1 fs). fold (𝓕c pC2 fs). do 2 rewrite 𝓕c_rewrite.
    iApply (wp_bind (fill $ [stlc_mu.lang.AppRCtx _])).
    iApply (wp_wand with "[-]").
    iMod (step_pure _ ei' K'
                    (Cast (# v') τ ⋆)
                    (Cast (Cast (# v') τ τG) τG ⋆) with "[Hv']") as "Hv'"; auto.
    { eapply UpFactorization; auto. by eapply get_shape_is_ground. }
    rewrite -𝓕c_rewrite.
    iApply (IHpC1 ei' (CastCtx τG ⋆ :: K') with "[Hv']"); auto.
    iIntros (w) "blaa".  iDestruct "blaa" as (w') "[Hw' #Hww']".
    simpl.
    rewrite -𝓕c_rewrite.
    iApply (IHpC2 ei' K' with "[Hw']"); auto.
    Unshelve. apply hack.
  Qed.

End compat_cast_tau_star.
