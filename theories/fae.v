From fae_gtlc_mu.stlc_mu Require Export contexts typing ctx_equiv.
From fae_gtlc_mu.cast_calculus Require Export contexts typing ctx_equiv.
From fae_gtlc_mu.embedding Require Export expressions types types_lemmas well_typedness.
From fae_gtlc_mu.backtranslation Require Export contexts well_typedness.

From fae_gtlc_mu.refinements.static_gradual Require Export adequacy.
From fae_gtlc_mu.refinements.static_gradual Require Export rel_ref_specs.
From fae_gtlc_mu.embedding Require Export contexts.
From fae_gtlc_mu.refinements.static_gradual Require Export adequacy.

Section static_gradual.

  (** Left to right in theorem 4.1 (<<Ct>>[e] ⇓) ⇒ (Ct[[[e]]] ⇓) *)
  Lemma static_ctx_refines_gradual (Γ : list stlc_mu.types.type) (e : stlc_mu.lang.expr) (τ : stlc_mu.types.type) (de : Γ ⊢ₛ e : τ) :
    ∀ (Cₜ : cast_calculus.contexts.ctx), cast_calculus.contexts.typed_ctx Cₜ (map embed_type Γ) (embed_type τ) [] TUnit →
       stlc_mu.lang.Halts (stlc_mu.contexts.fill_ctx (backtranslate_ctx Cₜ) e) →
       cast_calculus.lang.Halts (fill_ctx Cₜ [[e]]).
  Proof.
    intros Cₜ dCₜ Hs.
    (* use adequacy result of relatedness *)
    apply (@adequacy actualΣ _ _ (stlc_mu.contexts.fill_ctx (backtranslate_ctx Cₜ) e) _ TUnit); auto. intros.
    (* actually prove relatedness by invoking proofs of 1) <<Cₜ>> relates to Cₜ and 2) e relates to [[e]] *)
    apply (back_ctx_relates (map embed_type Γ) _ _ (embed_type τ)); auto. apply (embd_closed (stlc_mu.typing.typed_closed de)).
    by apply embedding_relates.
  Qed.

  (* Easy lemma to help prove reflection of equivalences (not in paper) *)
  Lemma static_ctx_refines_gradual_easy (Γ : list stlc_mu.types.type) (e : stlc_mu.lang.expr) (τ : stlc_mu.types.type) (de : Γ ⊢ₛ e : τ) :
    ∀ (C : stlc_mu.contexts.ctx), stlc_mu.contexts.typed_ctx C Γ τ [] stlc_mu.types.TUnit →
        stlc_mu.lang.Halts (stlc_mu.contexts.fill_ctx C e) →
        cast_calculus.lang.Halts (fill_ctx (embed_ctx C) [[e]]).
  Proof.
    intros C dC Hs.
    apply (@adequacy actualΣ _ _ (stlc_mu.contexts.fill_ctx C e) _ (embed_type stlc_mu.types.TUnit)); auto. intros.
    assert ([] = map embed_type []) as ->. done.
    apply (embed_ctx_relates Γ _ _ τ); auto. by eapply stlc_mu.typing.typed_closed.
    by apply embedding_relates.
  Qed.

End static_gradual.

From fae_gtlc_mu.refinements.gradual_static Require Export adequacy.
From fae_gtlc_mu.refinements.gradual_static Require rel_ref_specs.

Section gradual_static.

  (** right to left in theorem 4.1: (Ct[[[e]]] ⇓) ⇒ (<<Ct>>[e] ⇓) *)
  Lemma gradual_ctx_refines_static (Γ : list stlc_mu.types.type) (e : stlc_mu.lang.expr) (τ : stlc_mu.types.type) (de : Γ ⊢ₛ e : τ ):
    ∀ (K : cast_calculus.contexts.ctx), cast_calculus.contexts.typed_ctx K (map embed_type Γ) (embed_type τ) [] TUnit →
       cast_calculus.lang.Halts (fill_ctx K [[e]]) →
       stlc_mu.lang.Halts (stlc_mu.contexts.fill_ctx (backtranslate_ctx K) e).
  Proof.
    intros Cₜ dCₜ Hs.
    (* use adequacy result of relatedness *)
    apply (@gradual_static.adequacy.adequacy actualΣ _ _ (fill_ctx Cₜ [[e]]) (stlc_mu.contexts.fill_ctx (backtranslate_ctx Cₜ) e) TUnit); auto. intros.
    (* actually prove relatedness by invoking proofs of 1) Cₜ relates to <<Cₜ>> and 2) [[e]] relates to e *)
    apply (gradual_static.rel_ref_specs.back_ctx_relates (map embed_type Γ) _ _ (embed_type τ)); auto. apply (embd_closed (stlc_mu.typing.typed_closed de)).
    by apply gradual_static.rel_ref_specs.embedding_relates.
  Qed.

  (* Easy lemma to help prove reflection of equivalences (not in paper) *)
  Lemma gradual_ctx_refines_static_easy (Γ : list stlc_mu.types.type) (e : stlc_mu.lang.expr) (τ : stlc_mu.types.type) (de : Γ ⊢ₛ e : τ) :
    ∀ (C : stlc_mu.contexts.ctx), stlc_mu.contexts.typed_ctx C Γ τ [] stlc_mu.types.TUnit →
        cast_calculus.lang.Halts (fill_ctx (embed_ctx C) [[e]]) →
        stlc_mu.lang.Halts (stlc_mu.contexts.fill_ctx C e).
  Proof.
    intros C dC Hs.
    apply (@adequacy actualΣ _ _ (fill_ctx (embed_ctx C) [[e]]) (stlc_mu.contexts.fill_ctx C e) (embed_type stlc_mu.types.TUnit)); auto. intros.
    assert ([] = map embed_type []) as ->. done.
    apply (gradual_static.rel_ref_specs.embed_ctx_relates Γ _ _ τ); auto. by eapply stlc_mu.typing.typed_closed.
    by apply gradual_static.rel_ref_specs.embedding_relates.
  Qed.

End gradual_static.

(* small lemma *)
Definition retract τ : backtranslate_type (embed_type τ) = τ.
Proof. induction τ; simpl; try done; try by rewrite IHτ1 IHτ2. by rewrite IHτ. Qed.

(** Preservation of equivalences *)
Theorem ctx_eq_preservation Γ e1 e2 τ (Hctx : Γ ⊨ e1 =ctx-stat= e2 : τ) :
  map embed_type Γ ⊨ [[e1]] =ctx-grad= [[e2]] : embed_type τ.
Proof.
  (* easy well-typedness results *)
  assert (pe1 : Γ ⊢ₛ e1 : τ). apply Hctx. assert (pe2 : Γ ⊢ₛ e2 : τ). apply Hctx.
  split; try split; try by apply embedding.well_typedness.well_typedness_expr.
  (* actual proof *)
  intros Cₜ dCₜ. split.
  - intro Hg1.
    (* by applying static_ctx_refines_gradual and gradual_ctx_refines_static two times and the obligatory administration *)
    apply (static_ctx_refines_gradual Γ e2 τ (ltac:(apply Hctx)) Cₜ dCₜ).
    apply Hctx.
    cut (stlc_mu.contexts.typed_ctx
           (backtranslate_ctx Cₜ)
           (map backtranslate_type (map embed_type Γ)) (backtranslate_type $ embed_type τ)
           (map backtranslate_type []) (backtranslate_type $ embed_type stlc_mu.types.TUnit)).
    repeat rewrite retract. rewrite map_map (map_ext _ id _ (Γ)). by rewrite (map_id Γ). intro; by rewrite retract.
    apply well_typedness_ctx. apply (embd_closed (stlc_mu.typing.typed_closed pe1)). auto.
    by apply (gradual_ctx_refines_static Γ e1 τ pe1 Cₜ dCₜ).
  - intro Hg2.
    (* by applying static_ctx_refines_gradual and gradual_ctx_refines_static two times and the obligatory administration *)
    apply (static_ctx_refines_gradual Γ e1 τ (ltac:(apply Hctx)) Cₜ dCₜ).
    apply Hctx.
    cut (stlc_mu.contexts.typed_ctx
           (backtranslate_ctx Cₜ)
           (map backtranslate_type (map embed_type Γ)) (backtranslate_type $ embed_type τ)
           (map backtranslate_type []) (backtranslate_type $ embed_type stlc_mu.types.TUnit)).
    repeat rewrite retract. rewrite map_map (map_ext _ id _ (Γ)). by rewrite (map_id Γ). intro; by rewrite retract.
    apply well_typedness_ctx. apply (embd_closed (stlc_mu.typing.typed_closed pe1)). auto.
    apply (gradual_ctx_refines_static Γ e2 τ pe2 Cₜ dCₜ).
    apply Hg2.
Qed.

From fae_gtlc_mu.embedding Require Export well_typedness.

(** Reflection of equivalences *)
Theorem ctx_eq_reflection Γ e1 e2 τ (de1 : Γ ⊢ₛ e1 : τ) (de2 : Γ ⊢ₛ e2 : τ)
  (Hctx : map embed_type Γ ⊨ [[e1]] =ctx-grad= [[e2]] : embed_type τ) :
  Γ ⊨ e1 =ctx-stat= e2 : τ.
Proof.
  split; try split; try done.
  intros Cₜ dCₜ. split.
  - intro Hg1.
    apply (gradual_ctx_refines_static_easy Γ e2 τ de2 Cₜ dCₜ).
    apply Hctx.
    change (typed_ctx (embed_ctx Cₜ) (map embed_type Γ) [|τ|] (map embed_type []) (embed_type stlc_mu.types.TUnit)).
    apply well_typedness_ctx; auto. by eapply stlc_mu.typing.typed_closed.
    by apply (static_ctx_refines_gradual_easy Γ e1 τ de1 Cₜ dCₜ).
  - intro Hg2.
    apply (gradual_ctx_refines_static_easy Γ e1 τ de1 Cₜ dCₜ).
    apply Hctx.
    change (typed_ctx (embed_ctx Cₜ) (map embed_type Γ) [|τ|] (map embed_type []) (embed_type stlc_mu.types.TUnit)).
    apply well_typedness_ctx; auto. by eapply stlc_mu.typing.typed_closed.
    by apply (static_ctx_refines_gradual_easy Γ e2 τ de2 Cₜ dCₜ).
Qed.
