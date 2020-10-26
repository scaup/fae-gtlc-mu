From fae_gtlc_mu.refinements.gradual_static Require Export logical_relation.
From fae_gtlc_mu.backtranslation Require Export alternative_consistency.
From fae_gtlc_mu.backtranslation Require Export cast_help.general_def.
From fae_gtlc_mu.stlc_mu Require Export lang.

(* This file defines what needs to be proven for the compatibility lemma for casts. *)

Section defs.
  Context `{!implG Σ,!specG Σ}.

  (* Defines relatedness for a list of static values with respect A, a list of pairs of gradual types. *)

  Definition rel_cast_functions A (fs : list stlc_mu.lang.val) : iProp Σ :=
    ⌜length A = length fs⌝ ∗
    [∗ list] a ; f ∈ A ; fs , (
                           □ (∀ (v : cast_calculus.lang.val) (v' : stlc_mu.lang.val) ,
                                 ⟦ a.1 ⟧ (v , v') → ⟦ a.2 ⟧ₑ (Cast (v) a.1 a.2, (stlc_mu.lang.of_val f v'))
                             )
                         )%I.

  Global Instance rel_cast_functions_persistent A fs :
    Persistent (rel_cast_functions A fs).
  Proof.
    apply bi.sep_persistent; first by apply bi.pure_persistent.
    apply big_sepL2_persistent. intros _ (τi , τf) f. simpl.
    apply bi.intuitionistically_persistent.
  Qed.

  (** The (to-be-proven) statement that the -- closed up -- back-translated casts behave appropriately;
      it's a slightly adjusted version of the compatibility lemma for casts such that the proof is more ergonomic. *)

  Definition back_cast_ar {A} {τi τf} (pC : alternative_consistency A τi τf) :=
    ∀ ei' K' v v' fs,
      ( rel_cast_functions A fs ∧
        ⟦ τi ⟧ (v, v') ∧
        initially_inv ei' ∧
        currently_half (fill K' (𝓕c pC fs (stlc_mu.lang.of_val v')))
      )
        ⊢ (WP
             Cast v τi τf ?{{ w, ∃ w', currently_half (fill K' (stlc_mu.lang.of_val w')) ∧ ⟦ τf ⟧ (w, w') }})%I.

End defs.
