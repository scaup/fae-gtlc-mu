From fae_gtlc_mu.stlc_mu Require Export types typing.
From fae_gtlc_mu.cast_calculus Require Export lang.
From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import lifting.
From fae_gtlc_mu.backtranslation Require Export cast_help.general cast_help.extract cast_help.embed props.extract_embed.
From fae_gtlc_mu.stlc_mu Require Export lang.
From fae_gtlc_mu.refinements.gradual_static Require Export logical_relation resources_left resources_right compat_easy compat_cast.defs.
From fae_gtlc_mu.cast_calculus Require Export consistency.structural types.

Section star_ground.
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

  Hint Resolve to_of_val : core.

  Hint Extern 5 (AsVal _) => eexists; simpl; try done; eapply cast_calculus.lang.of_to_val; fast_done : typeclass_instances.
  Hint Extern 10 (AsVal _) =>
  eexists; rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

  Local Hint Extern 5 (Ground _) => by constructor : typeclass_instances.

  Local Hint Extern 5 (_ ≠ _) => by intro abs; inversion abs : typeclass_instances.


  Lemma back_cast_ar_star_ground (A : list (type * type)) (τG : type) (G : Ground τG) : back_cast_ar (consStarTGround A τG G).
  Proof.
    rewrite /back_cast_ar /𝓕c /𝓕. iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')". rewrite extract_no_subs.
    destruct G; rewrite interp_rw_TUnknown;
      (iDestruct "Hvv'" as (w w') "#[[% Hww]|[[% Hww]|[[% Hww]|[[% Hww]|[% Hww]]]]]"; inversion H; clear H H1 H2 v v'); simpl;
        try by (wp_head; iApply wp_CastError').
    + wp_head. iMod (steps_pure _ ei' K' _ _ _ (extract_TUnit_embed_TUnit w') with "[Hv']") as "Hv'"; auto.
      wp_value. iExists _.  auto.
    + wp_head. iMod (steps_pure _ ei' K' _ _ _ (extract_TProd_embed_TProd w') with "[Hv']") as "Hv'"; auto.
      wp_value. iExists _.  auto.
    + wp_head. iMod (steps_pure _ ei' K' _ _ _ (extract_TSum_embed_TSum w') with "[Hv']") as "Hv'"; auto.
      wp_value. iExists _.  auto.
    + wp_head. iMod (steps_pure _ ei' K' _ _ _ (extract_TArrow_embed_TArrow w') with "[Hv']") as "Hv'"; auto.
      wp_value. iExists _.  auto.
    + wp_head. iMod (steps_pure _ ei' K' _ _ _ (extract_TRec_embed_TUnknown w') with "[Hv']") as "Hv'"; auto.
      wp_value. iExists _.  auto.
      rewrite interp_rw_TRec. asimpl. iSplit; auto. by simpl.
  Qed.

End star_ground.
