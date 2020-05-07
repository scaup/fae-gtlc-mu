From fae_gtlc_mu.refinements.static_gradual Require Export logical_relation resources_right compat_easy help_left compat_cast.defs.
From fae_gtlc_mu.cast_calculus Require Export types typing.
From fae_gtlc_mu.stlc_mu Require Export lang.
From fae_gtlc_mu.cast_calculus Require Export lang.
From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import lifting.
From fae_gtlc_mu.cast_calculus Require Export types.
From fae_gtlc_mu.cast_calculus Require Export consistency.structural.
From fae_gtlc_mu.backtranslation Require Export cast_help.general cast_help.extract cast_help.embed.
From fae_gtlc_mu.refinements.static_gradual.compat_cast Require Export between_rec prod_prod sum_sum arrow_arrow identity tau_star ground_star tau_star star_tau star_ground.

Section compat_cast_all.
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

  Lemma back_cast_ar_all {A} {τi τf} (pC : cons_struct A τi τf) : back_cast_ar pC.
  Proof.
    induction pC.
    - by apply back_cast_ar_star_ground.
    - by apply back_cast_ar_ground_star.
    - by apply back_cast_ar_tau_star.
    - by apply back_cast_ar_star_tau.
    - by apply back_cast_ar_base_base.
    - by apply back_cast_ar_star_star.
    - by apply back_cast_ar_sum_sum.
    - by apply back_cast_ar_prod_prod.
    - by apply back_cast_ar_arrow_arrow.
    - by apply back_cast_ar_trec_trec_expose.
    - by apply back_cast_ar_trec_trec_use.
  Qed.


  Notation "'` H" := (bin_log_related_alt H) (at level 8).

  Lemma bin_log_related_back_cast Γ e e' τi τf (pC : cons_struct [] τi τf)
      (IHHtyped : Γ ⊨ e ≤log≤ e' : τi) :
    Γ ⊨ 𝓕c pC [] e ≤log≤ Cast e' τi τf : τf.
  Proof.
    iIntros (vvs ei) "#[Hρ HΓ]"; iIntros (K) "Hj /=".
    rewrite 𝓕c_closed; try auto.
    rewrite 𝓕c_rewrite.
    iApply (wp_bind (fill [stlc_mu.lang.AppRCtx _])).
    iApply (wp_wand with "[Hj]"). iApply ('`IHHtyped _ _ (CastCtx τi τf :: K)). iFrame. auto.
    iIntros (v). iDestruct 1 as (v') "[Hv' Hvv']". simpl.
    rewrite -𝓕c_rewrite.
    iApply (wp_wand with "[-]").
    iApply ((back_cast_ar_all pC) with "[-]").
    iSplitR. unfold rel_cast_functions. iSplit; auto.
    iSplitL "Hvv'". auto. auto.
    clear v v'.
    iIntros (v). iDestruct 1 as (v') "[Hv' Hvv']".
    iExists v'.
    auto.
    Unshelve. apply hack.
  Qed.

  Lemma bin_log_related_omega Γ e' τ :
    Γ ⊨ Ω ≤log≤ e' : τ.
  Proof.
    iIntros (vvs ρ) "#[Hρ HΓ]"; iIntros (K) "Hj /=".
    by iApply wp_Ω.
  Qed.

End compat_cast_all.
