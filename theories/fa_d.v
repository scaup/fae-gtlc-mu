From fae_gtlc_mu.stlc_mu Require Export contexts.

(** contextual equivalence for contexts in static language *)
Definition equiv_ctx_stlc_mu (C C' : ctx) (Γ : list type) (τ : type) :=
  typed_ctx C Γ τ [] TUnit ∧ typed_ctx C' Γ τ [] TUnit ∧
  ∀ e, Γ ⊢ₛ e : τ →
  (Halts (fill_ctx C e) <-> Halts (fill_ctx C' e)).

From fae_gtlc_mu.cast_calculus Require Export contexts.

(** contextual equivalence for contexts in gradual language *)
Definition equiv_ctx_cast_calculus (C C' : ctx) (Γ : list type) (τ : type) :=
  typed_ctx C Γ τ [] TUnit ∧ typed_ctx C' Γ τ [] TUnit ∧
  ∀ e, Γ ⊢ₜ e : τ →
  (Halts (fill_ctx C e) <-> Halts (fill_ctx C' e)).

Section static_gradual.
  From fae_gtlc_mu.refinements.static_gradual Require Export adequacy rel_ref_specs.
  From fae_gtlc_mu.embedding Require Export types contexts.
  From fae_gtlc_mu.backtranslation Require Export expressions.

  Lemma static_refines_gradual (C : stlc_mu.contexts.ctx) (Γ : list stlc_mu.types.type) (τ : stlc_mu.types.type) (pτ : stlc_mu.types.TClosed τ) (dC : stlc_mu.contexts.typed_ctx C Γ τ [] stlc_mu.types.TUnit) :
    ∀ (e : cast_calculus.lang.expr), (map embed_type Γ) ⊢ₜ e : (embed_type τ) →
       Halts_stat (stlc_mu.contexts.fill_ctx C <<e>>) →
       Halts_grad (cast_calculus.contexts.fill_ctx (embed_ctx C) e).
  Proof.
    intros e de Hs.
    apply (@adequacy actualΣ _ _ (stlc_mu.contexts.fill_ctx C <<e>>) _ TUnit); auto; intros.
    cut (map embed_type [] ⊨ stlc_mu.contexts.fill_ctx C << e >> ≤log≤ fill_ctx (embed_ctx C) e : embed_type stlc_mu.types.TUnit); auto.
    apply (embed_ctx_relates Γ <<e>> e τ); auto. by apply back_relates.
  Qed.

End static_gradual.

Section gradual_static.
  From fae_gtlc_mu.refinements.gradual_static Require Export adequacy rel_ref_specs.
  From fae_gtlc_mu.embedding Require Export types contexts.
  From fae_gtlc_mu.backtranslation Require Export expressions.

  Lemma gradual_refines_static (C : stlc_mu.contexts.ctx) (Γ : list stlc_mu.types.type) (τ : stlc_mu.types.type) (pτ : stlc_mu.types.TClosed τ) (dC : stlc_mu.contexts.typed_ctx C Γ τ [] stlc_mu.types.TUnit) :
    ∀ (e : cast_calculus.lang.expr), (map embed_type Γ) ⊢ₜ e : (embed_type τ) →
       Halts_grad (cast_calculus.contexts.fill_ctx (embed_ctx C) e) →
       Halts_stat (stlc_mu.contexts.fill_ctx C <<e>>).
  Proof.
    intros e de Hs.
    apply (@adequacy actualΣ _ _ (cast_calculus.contexts.fill_ctx (embed_ctx C) e) _ TUnit); auto; intros.
    cut (map embed_type [] ⊨ cast_calculus.contexts.fill_ctx (embed_ctx C) e ≤log≤ stlc_mu.contexts.fill_ctx C <<e>> : embed_type stlc_mu.types.TUnit); auto.
    apply (embed_ctx_relates Γ e <<e>> τ); auto. by apply back_relates.
  Qed.

End gradual_static.

(** Preservation of contextual equivalence of contexts *)

From fae_gtlc_mu.backtranslation Require Export well_typedness.
From fae_gtlc_mu.embedding Require Export well_typedness.

From fae_gtlc_mu Require Export fae. (* just for the simple lemmas *)
(* Definition retract τ : backtranslate_type (embed_type τ) = τ. *)
(* Proof. induction τ; simpl; try done; try by rewrite IHτ1 IHτ2. by rewrite IHτ. Qed. *)

Theorem preservation C1 C2 Γ τ (pτ : stlc_mu.types.TClosed τ) (Hs : equiv_ctx_stlc_mu C1 C2 Γ τ) :
  equiv_ctx_cast_calculus (embed_ctx C1) (embed_ctx C2) (map embed_type Γ) (embed_type τ).
Proof.
  destruct Hs as [HC1 [HC2 HC12] ].
  split; try split.
  cut (typed_ctx (embed_ctx C1) (map embed_type Γ) [|τ|] (map embed_type []) (embed_type stlc_mu.types.TUnit)); auto. by apply well_typedness_ctx.
  cut (typed_ctx (embed_ctx C2) (map embed_type Γ) [|τ|] (map embed_type []) (embed_type stlc_mu.types.TUnit)); auto. by apply well_typedness_ctx.
  intros e de. split.
  + intro Hg.
    apply (static_refines_gradual C2 Γ τ pτ HC2 e de).
    apply HC12. (* bff *) { cut (map backtranslate_type (map embed_type Γ) ⊢ₛ backtranslate_expr e : backtranslate_type (embed_type τ)). rewrite map_map (map_ext _ id). by rewrite map_id retract. intro. by rewrite retract. by apply backtranslation.well_typedness.well_typedness_expr.  }
    by apply (gradual_refines_static C1 Γ τ pτ HC1 e de).
  + intro Hs.
    apply (static_refines_gradual C1 Γ τ pτ HC1 e de).
    apply HC12. (* bff *) { cut (map backtranslate_type (map embed_type Γ) ⊢ₛ backtranslate_expr e : backtranslate_type (embed_type τ)). rewrite map_map (map_ext _ id). by rewrite map_id retract. intro. by rewrite retract. by apply backtranslation.well_typedness.well_typedness_expr.  }
    by apply (gradual_refines_static C2 Γ τ pτ HC2 e de).
Qed.


Theorem reflection C1 C2 Γ τ (pτ : stlc_mu.types.TClosed τ)
  (dC1 : stlc_mu.contexts.typed_ctx C1 Γ τ [] stlc_mu.types.TUnit) (dC2 : stlc_mu.contexts.typed_ctx C2 Γ τ [] stlc_mu.types.TUnit) :
  equiv_ctx_cast_calculus (embed_ctx C1) (embed_ctx C2) (map embed_type Γ) (embed_type τ) → equiv_ctx_stlc_mu C1 C2 Γ τ.
Proof.
  destruct 1 as [pEC1 [ pEC2 pEC12 ] ].
  split; try split; auto.
  intros e de. split.
  + intro Hs.
    apply (gradual_ctx_refines_static_easy Γ e τ); auto.
    apply pEC12; try by apply embedding.well_typedness.well_typedness_expr.
    by apply (static_ctx_refines_gradual_easy Γ e τ).
  + intro Hs.
    apply (gradual_ctx_refines_static_easy Γ e τ); auto.
    apply pEC12; try by apply embedding.well_typedness.well_typedness_expr.
    by apply (static_ctx_refines_gradual_easy Γ e τ).
Qed.
