From fae_gtlc_mu.stlc_mu Require Export contexts.
From fae_gtlc_mu.cast_calculus Require Export contexts.
From fae_gtlc_mu.embedding Require Export expressions types.
From fae_gtlc_mu.backtranslation Require Export contexts.
From fae_gtlc_mu.refinements.static_gradual Require Export soundness.
From fae_gtlc_mu.refinements.static_gradual Require Export rel_ref_specs.

Notation "Γ ⊨ e '=ctx-grad=' e' : τ" :=
  (cast_calculus.contexts.ctx_equiv Γ e e' τ) (at level 74, e, e', τ at next level).

Notation "Γ ⊨ e '=ctx-stat=' e' : τ" :=
  (stlc_mu.contexts.ctx_equiv Γ e e' τ) (at level 74, e, e', τ at next level).

Lemma static_ctx_refines_gradual (Γ : list stlc_mu.typing.type) (e : stlc_mu.lang.expr) (τ : stlc_mu.typing.type) (de : Γ ⊢ₛ e : τ) :
  ∀ (Cₜ : cast_calculus.contexts.ctx), cast_calculus.contexts.typed_ctx Cₜ (map embed_type Γ) (embed_type τ) [] TUnit →
     Halts_stat (stlc_mu.contexts.fill_ctx (backtranslate_ctx Cₜ) e) →
     Halts_grad (fill_ctx Cₜ [[e]]).
Proof.
  intros Cₜ dCₜ Hs.
  apply (@soundness actualΣ _ _ (stlc_mu.contexts.fill_ctx (backtranslate_ctx Cₜ) e) _ TUnit).
  intros.
  eapply back_ctx_relates. admit. admit. apply dCₜ.
  apply embedding_relates; done.
  done.
Admitted.

Lemma gradual_ctx_refines_static (Γ : list stlc_mu.typing.type) (e : stlc_mu.lang.expr) (τ : stlc_mu.typing.type) :
  ∀ (K : cast_calculus.contexts.ctx), cast_calculus.contexts.typed_ctx K (map embed_type Γ) (embed_type τ) [] TUnit →
     Halts_grad (fill_ctx K [[e]]) →
     Halts_stat (stlc_mu.contexts.fill_ctx (backtranslate_ctx K) e).
Proof.
Admitted.


Theorem ctx_eq_preservation Γ e1 e2 τ (Hctx : Γ ⊨ e1 =ctx-stat= e2 : τ) :
  map embed_type Γ ⊨ [[e1]] =ctx-grad= [[e2]] : embed_type τ.
Proof.
  split; try split. admit. admit.
  intros Cₜ dCₜ. split.
  - intro Hg1.
    apply (static_ctx_refines_gradual Γ e2 τ (ltac:(apply Hctx)) Cₜ dCₜ).
    apply Hctx. admit.
    apply (gradual_ctx_refines_static Γ e1 τ Cₜ dCₜ).
    apply Hg1.
  - intro Hg2.
    apply (static_ctx_refines_gradual Γ e1 τ (ltac:(apply Hctx)) Cₜ dCₜ).
    apply Hctx. admit.
    apply (gradual_ctx_refines_static Γ e2 τ Cₜ dCₜ).
    apply Hg2.
Admitted.
