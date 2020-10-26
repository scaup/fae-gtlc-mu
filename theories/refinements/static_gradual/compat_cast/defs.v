From fae_gtlc_mu.refinements.static_gradual Require Export logical_relation.
From fae_gtlc_mu.backtranslation Require Export alternative_consistency.
From fae_gtlc_mu.backtranslation Require Export cast_help.general_def.
From fae_gtlc_mu.cast_calculus Require Export lang.

(* This file defines what needs to be proven for the compatibility lemma for casts. *)

Section defs.
  Context `{!implG Σ,!specG Σ}.

  (* Defines relatedness for a list of static values with respect A, a list of pairs of gradual types. *)
  (* This definition corresponds to equation 5 in the paper. *)

  Definition rel_cast_functions A (fs : list stlc_mu.lang.val) : iProp Σ :=
    ⌜length A = length fs⌝ ∗
    [∗ list] p ; f ∈ A ; fs , (
                           □ (∀ (v : stlc_mu.lang.val) (v' : cast_calculus.lang.val) ,
                                 ⟦ p.1 ⟧ (v , v') → ⟦ p.2 ⟧ₑ ((stlc_mu.lang.of_val f v) , Cast (v') p.1 p.2))
                         )%I.

  Global Instance rel_cast_functions_persistent A fs :
    Persistent (rel_cast_functions A fs).
  Proof.
    apply bi.sep_persistent; first by apply bi.pure_persistent.
    apply big_sepL2_persistent. intros _ (τi , τf) f. simpl.
    apply bi.intuitionistically_persistent.
  Qed.

  (** The (to-be-proven) statement that the -- closed up -- back-translated casts behave appropriately.
      This corresponds to the statement of lemma 4.7 in the paper;
      it's slightly adjust though to facilitate its proof. *)

  Definition back_cast_ar {A} {τi τf} (pC : alternative_consistency A τi τf) :=
  ∀ ei' K' v v' fs,
    ( rel_cast_functions A fs ∧ (* fs a list of values that relates to A as described above *)
      ⟦ τi ⟧ (v, v') ∧
      initially_inv ei' ∧
      currently_half (fill K' (Cast (cast_calculus.lang.of_val v') τi τf))
    )
      ⊢ (WP
           (𝓕c pC fs)(* the backtranslated cast; a function of type <<τi>> → <<τf>> *) v
           {{ w, ∃ w', currently_half (fill K' (cast_calculus.lang.of_val w')) ∧ ⟦ τf ⟧ (w, w') }}
        )%I.

End defs.
