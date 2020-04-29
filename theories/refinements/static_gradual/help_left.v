From fae_gtlc_mu.refinements.static_gradual Require Export logical_relation resources_right compat_easy.
From fae_gtlc_mu.cast_calculus Require Export types typing.
From fae_gtlc_mu.stlc_mu Require Export lang.
From fae_gtlc_mu.cast_calculus Require Export lang.
From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import lifting.
From fae_gtlc_mu.cast_calculus Require Export types.
From fae_gtlc_mu.cast_calculus Require Export consistency.structural.definition.
From fae_gtlc_mu.backtranslation Require Export cast_help.general cast_help.extract cast_help.embed.

Section extract_embed.
  Context `{!implG Σ,!specG Σ}.
  Notation D := (prodO stlc_mu.lang.valO cast_calculus.lang.valO -n> iPropO Σ).
  (* Implicit Types e : stlc_mu.lang.expr. *)
  (* Implicit Types e : stlc_mu.lang.expr. *)
  Implicit Types fs : list stlc_mu.lang.val.
  (* Implicit Types f : stlc_mu.lang.val. *)
  Implicit Types A : list (cast_calculus.types.type * cast_calculus.types.type).
  (* Implicit Types a : (cast_calculus.types.type * cast_calculus.types.type). *)
  Local Hint Resolve to_of_val : core.

  (** We need to "close up" 𝓕 pC with functions... *)

 Lemma wp_Ω Φ : ⊢ (True -∗ (WP Ω {{ Φ }}))%I.
 Proof.
   iIntros.
   iLöb as "IH".
   iApply wp_pure_step_later; auto; iNext; asimpl.
   iApply (wp_bind $ stlc_mu.lang.fill_item $ stlc_mu.lang.AppLCtx _).
   iApply wp_pure_step_later; auto.
   iNext.
   iApply wp_value.
   fold Ω. done.
 Qed.



End extract_embed.
