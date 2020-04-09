From fae_gtlc_mu.refinements.static_gradual Require Export tactics_left logical_relation resources_right compat_easy help_left compat_cast.defs.
From fae_gtlc_mu.cast_calculus Require Export types typing.
From fae_gtlc_mu.stlc_mu Require Export lang.
From fae_gtlc_mu.cast_calculus Require Export lang.
From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import lifting.
From fae_gtlc_mu.cast_calculus Require Export types.
From fae_gtlc_mu.cast_calculus Require Export consistency.structural.definition.
From fae_gtlc_mu.backtranslation Require Export cast_help.general cast_help.extract cast_help.embed.
From fae_gtlc_mu.refinements.static_gradual.compat_cast Require Export between_rec star_ground ground_star tau_star star_tau prod_prod sum_sum arrow_arrow identity.

Section compat_cast_all.
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


  Lemma back_cast_ar_all {A} {τi τf} (pC : cons_struct A τi τf) : back_cast_ar pC.
  Proof.
    induction pC.
    - by apply back_cast_ar_star_ground.
    - by apply back_cast_ar_ground_star.
    - apply back_cast_ar_tau_star.
    - apply back_cast_ar_star_tau.
    - apply back_cast_ar_base_base.
    - apply back_cast_ar_star_star.
    - by apply back_cast_ar_sum_sum.
    - by apply back_cast_ar_prod_prod.
    - by apply back_cast_ar_arrow_arrow.
    - by apply back_cast_ar_trec_trec_expose.
    - by apply back_cast_ar_trec_trec_use.
  Qed.

  Lemma bin_log_related_back_cast Γ e e' τi τf (pC : cons_struct [] τi τf)
      (IHHtyped : Γ ⊨ e ≤log≤ e' : τi) :
    Γ ⊨ 𝓕c pC [] e ≤log≤ Cast e' τi τf : τf.
  Proof.
    iIntros (Δ vvs ei ?) "#[Hρ HΓ]"; iIntros (K) "Hj /=".
    rewrite 𝓕c_rewrite.



    iApply (wp_bind (fill [stlc_mu.lang.UnfoldCtx])).
    iApply (wp_wand with "[Hj]"). iApply ('`IHHtyped _ _ _ (UnfoldCtx :: K)). iFrame. auto.
    iIntros (v). iDestruct 1 as (v') "[Hw #Hiw]".
    simpl.
    rewrite /= fixpoint_interp_rec1_eq /=.
    change (fixpoint _) with (interp (TRec τ) Δ).
    iDestruct "Hiw" as ([w w']) "#[% Hiz]"; simplify_eq/=.
    iMod (step_Fold _ _ K (of_val w') with "[-]") as "Hz"; eauto.
    iApply wp_pure_step_later; cbn; auto.
    iNext. iApply wp_value; auto. iExists _; iFrame "Hz".
      by rewrite -interp_subst.
  Qed.






End compat_cast_all.


