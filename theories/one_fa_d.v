From fae_gtlc_mu.stlc_mu Require Export contexts typing.
From fae_gtlc_mu.cast_calculus Require Export contexts typing.
From fae_gtlc_mu.embedding Require Export expressions types well_typedness.
From fae_gtlc_mu.backtranslation Require Export expressions well_typedness.

Definition Halts_stat := stlc_mu.lang.Halts.

Section gradual_static.
  From fae_gtlc_mu.refinements.gradual_static Require Export adequacy.
  From fae_gtlc_mu.refinements.gradual_static Require Export rel_ref_specs.

  Lemma gradual_static (Γ : list stlc_mu.types.type) (e : cast_calculus.lang.expr) (τ : stlc_mu.types.type) (pτ : stlc_mu.types.TClosed τ) (de : (map embed_type Γ) ⊢ₜ e : (embed_type τ)):
    ∀ (Cₛ : stlc_mu.contexts.ctx), stlc_mu.contexts.typed_ctx Cₛ Γ τ [] stlc_mu.types.TUnit →
       Halts_grad (fill_ctx (embed_ctx Cₛ) e) →
       Halts_stat (stlc_mu.contexts.fill_ctx Cₛ (backtranslate_expr e)).
  Proof.
    intros Cₛ dCₛ Hs.
    apply (@adequacy actualΣ _ _ (fill_ctx (embed_ctx Cₛ) e) _ (embed_type stlc_mu.types.TUnit)); auto. intros.
    assert ([] = map embed_type []) as ->. done.
    apply (embed_ctx_relates Γ _ _ τ); auto.
    apply (back_relates (map embed_type Γ) e (embed_type τ)); auto.
  Qed.

End gradual_static.

From fae_gtlc_mu Require Export fae. (* for the static_ctx_refines_gradual_easy lemma and the retract lemma *)

Definition stuck_diverge_grad : cast_calculus.lang.expr → Prop :=
  fun e => ¬ cast_calculus.lang.Halts e.

Definition stuck_diverge_stat : stlc_mu.lang.expr → Prop :=
  fun e => ¬ stlc_mu.lang.Halts e.

Definition stat_P C Γ τ : Prop :=
    (stlc_mu.types.TClosed τ) ∧ (stlc_mu.contexts.typed_ctx C Γ τ [] stlc_mu.types.TUnit)
  ∧ (∀ e, Γ ⊢ₛ e : τ → stuck_diverge_stat (stlc_mu.contexts.fill_ctx C e)).

Definition grad_P C Γ τ : Prop :=
    (cast_calculus.types.TClosed τ) ∧ (cast_calculus.contexts.typed_ctx C Γ τ [] cast_calculus.types.TUnit)
  ∧ (∀ e, Γ ⊢ₜ e : τ → stuck_diverge_grad (cast_calculus.contexts.fill_ctx C e)).

(** stat_P and grad_P are the properties on contexts that we want to preserve and reflect *upon embedding* *)

Theorem preservation C Γ τ (Hs : stat_P C Γ τ) : grad_P (embed_ctx C) (map embed_type Γ) (embed_type τ).
Proof.
  destruct Hs as [pτ [pC Hs] ].
  split; try split. by apply embd_closed. cut (typed_ctx (embed_ctx C) (map embed_type Γ) [|τ|] (map embed_type []) (embed_type stlc_mu.types.TUnit)). auto.
  apply embedding.well_typedness.well_typedness_ctx; auto.
  intros eₜ deₜ abs. apply (Hs (backtranslate_expr eₜ)).
  cut (map backtranslate_type (map embed_type Γ) ⊢ₛ backtranslate_expr eₜ : backtranslate_type (embed_type τ)).
  rewrite map_map (map_ext _ id). by rewrite map_id retract. intro. by rewrite retract.
  by apply backtranslation.well_typedness.well_typedness_expr.
  apply (gradual_static Γ _ τ); auto.
Qed.

Theorem reflection C Γ τ (pτ : stlc_mu.types.TClosed τ) (dC : stlc_mu.contexts.typed_ctx C Γ τ [] stlc_mu.types.TUnit) :
  (grad_P (embed_ctx C) (map embed_type Γ) (embed_type τ)) → stat_P C Γ τ.
Proof.
  intro Hg. destruct Hg as [peτ [peC Hg] ].
  split; try split; auto.
  intros e de abs. apply (Hg (embed_expr e)). by apply embedding.well_typedness.well_typedness_expr.
  by eapply static_ctx_refines_gradual_easy.
Qed.
