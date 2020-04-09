From fae_gtlc_mu.refinements.static_gradual Require Export tactics_left logical_relation resources_right compat_easy help_left compat_cast.defs.
From fae_gtlc_mu.cast_calculus Require Export types typing.
From fae_gtlc_mu.stlc_mu Require Export lang.
From fae_gtlc_mu.cast_calculus Require Export lang.
From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import lifting.
From fae_gtlc_mu.cast_calculus Require Export consistency.structural.definition.
From fae_gtlc_mu.backtranslation Require Export cast_help.general cast_help.extract cast_help.embed.
From fae_gtlc_mu.cast_calculus Require Export types.

Section compat_cast_tau_star.
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

  Lemma back_cast_ar_tau_star:
    ∀ (A : list (type * type)) (τ τG : type) (pτnG : Ground τ → False) (pτnStar : τ ≠ ⋆) 
      (pτSτG : get_shape τ = Some τG) (pC : A ⊢ τ ~ τG), back_cast_ar (consTauStar A τ τG pτnG pτnStar pτSτG pC).
  Proof.
    intros A τ τG pτnG pτnStar pτSτG pC.
    rewrite /back_cast_ar /𝓕c /𝓕. iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    fold (𝓕 pC).
    wp_head. asimpl. rewrite embed_no_subs.
    (** IH *)
    (* embed is a value.. *)
    admit.
    (* iApply (wp_bind (fill $ [stlc_mu.lang.AppRCtx _])). *)
    (** embedding stuff *)
  Admitted.

End compat_cast_tau_star.
