From fae_gtlc_mu.refinements.static_gradual Require Export logical_relation.
From fae_gtlc_mu.backtranslation Require Export alternative_consistency.
From fae_gtlc_mu.backtranslation Require Export cast_help.general_def.
From fae_gtlc_mu.cast_calculus Require Export lang.

Section defs.
  Context `{!implG Σ,!specG Σ}.

  Definition rel_cast_functions A (fs : list stlc_mu.lang.val) : iProp Σ :=
    ⌜length A = length fs⌝ ∗
    [∗ list] a ; f ∈ A ; fs , (
                           □ (∀ (v : stlc_mu.lang.val) (v' : cast_calculus.lang.val) ,
                                 ⟦ a.1 ⟧ (v , v') → ⟦ a.2 ⟧ₑ ((stlc_mu.lang.of_val f v) , Cast (v') a.1 a.2))
                         )%I.

  Global Instance rel_cast_functions_persistent A fs :
    Persistent (rel_cast_functions A fs).
  Proof.
    apply bi.sep_persistent; first by apply bi.pure_persistent.
    apply big_sepL2_persistent. intros _ (τi , τf) f. simpl.
    apply bi.intuitionistically_persistent.
  Qed.

  (** The statement that the -- closed up -- back-translated casts behave appropriately.
      (We redefine it here to a new statement, making it a bit more amenable for proving.) *)

  Definition back_cast_ar {A} {τi τf} (pC : alternative_consistency A τi τf) :=
  ∀ ei' K' v v' fs, (rel_cast_functions A fs ∧ ⟦ τi ⟧ (v, v') ∧ initially_inv ei' ∧ currently_half (fill K' (Cast (cast_calculus.lang.of_val v') τi τf)))
                     ⊢ (WP 𝓕c pC fs (stlc_mu.lang.of_val v) {{ w, ∃ w', currently_half (fill K' (cast_calculus.lang.of_val w')) ∧ ⟦ τf ⟧ (w, w') }})%I.

End defs.
