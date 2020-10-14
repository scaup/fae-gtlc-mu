From fae_gtlc_mu.refinements.static_gradual Require Export logical_relation compat_easy.
From fae_gtlc_mu.embedding Require Import expressions types types_lemmas.
From fae_gtlc_mu.stlc_mu Require Export typing.
From fae_gtlc_mu.cast_calculus Require Export types consistency_lemmas.
From fae_gtlc_mu.refinements.static_gradual Require Import compat_cast.all.
From fae_gtlc_mu.backtranslation Require Import expressions well_typedness.
From fae_gtlc_mu.stlc_mu Require Export contexts.
From fae_gtlc_mu.cast_calculus Require Export contexts.
From fae_gtlc_mu.backtranslation Require Import contexts.
From fae_gtlc_mu Require Export embedding.contexts.


Section relation_for_specification_lemma.
  Context `{!implG Σ, !specG Σ}.

  (** Static terms are related to their embeddings *)
  Theorem embedding_relates (Γ : list stlc_mu.types.type) (e : stlc_mu.lang.expr) (τ : stlc_mu.types.type) :
    Γ ⊢ₛ e : τ → map embed_type Γ ⊨ e ≤log≤ [[e]] : [| τ |].
  Proof.
    induction 1; simpl.
    - apply bin_log_related_var. by rewrite list_lookup_fmap H.
    - by apply bin_log_related_unit.
    - by apply bin_log_related_pair.
    - by eapply bin_log_related_fst.
    - by eapply bin_log_related_snd.
    - by apply bin_log_related_injl.
    - by apply bin_log_related_injr.
    - by eapply bin_log_related_case.
    - by apply bin_log_related_lam.
    - by eapply bin_log_related_app.
    - apply bin_log_related_fold. by rewrite -embd_unfold_comm.
    - rewrite embd_unfold_comm. apply bin_log_related_unfold. by simpl in IHtyped.
  Qed.

  (** Gradual terms are related to their backtranslation *)
  Theorem back_relates (Γ : list cast_calculus.types.type) (e : cast_calculus.lang.expr) (τ : cast_calculus.types.type) :
    Γ ⊢ₜ e : τ → Γ ⊨ <<<e>>> ≤log≤ e : τ.
  Proof.
    induction 1; simpl.
    - by apply bin_log_related_var.
    - by apply bin_log_related_unit.
    - by apply bin_log_related_pair.
    - by eapply bin_log_related_fst.
    - by eapply bin_log_related_snd.
    - by apply bin_log_related_injl.
    - by apply bin_log_related_injr.
    - by eapply bin_log_related_case.
    - by apply bin_log_related_lam.
    - by eapply bin_log_related_app.
    - by apply bin_log_related_fold.
    - by apply bin_log_related_unfold.
    - assert (pτi : Closed τi). apply (cast_calculus.typing.typed_closed H).
      destruct (consistency_open_dec τi τf);
                destruct (decide (Closed τi));
                destruct (decide (Closed τf)); try by contradiction.
      by apply bin_log_related_back_cast.
    - apply bin_log_related_omega.
  Qed.

  Lemma back_ctx_item_relates (Γ : list cast_calculus.types.type) (e : stlc_mu.lang.expr) (e' : cast_calculus.lang.expr) (τ : cast_calculus.types.type) (pτ : Closed τ)
        (Γ' : list cast_calculus.types.type) (τ' : cast_calculus.types.type) (C : cast_calculus.contexts.ctx_item) :
      cast_calculus.contexts.typed_ctx_item C Γ τ Γ' τ' →
      Γ ⊨ e ≤log≤ e' : τ →
      Γ' ⊨ stlc_mu.contexts.fill_ctx_item (backtranslate_ctx_item C) e ≤log≤ cast_calculus.contexts.fill_ctx_item C e' : τ'.
  Proof.
    destruct C; intros; inversion H; simplify_eq; simpl.
    - by apply bin_log_related_lam.
    - eapply bin_log_related_app; eauto using back_relates.
    - eapply bin_log_related_app; eauto using back_relates.
    - eapply bin_log_related_pair; eauto using back_relates.
    - eapply bin_log_related_pair; eauto using back_relates.
    - by eapply bin_log_related_fst.
    - by eapply bin_log_related_snd.
    - by apply bin_log_related_injl.
    - by apply bin_log_related_injr.
    - eapply bin_log_related_case; try apply back_relates; try done.
    - eapply bin_log_related_case; try apply back_relates; try done.
    - eapply bin_log_related_case; try apply back_relates; try done.
    - by apply bin_log_related_fold.
    - by apply bin_log_related_unfold.
    - destruct (consistency_open_dec τ τ');
                destruct (decide (Closed τ));
                destruct (decide (Closed τ')); try by contradiction.
      by apply bin_log_related_back_cast.
  Qed.

  (** Gradual contexts are related to their backtranslation *)
  Lemma back_ctx_relates (Γ : list cast_calculus.types.type) (e : stlc_mu.lang.expr) (e' : cast_calculus.lang.expr) (τ : cast_calculus.types.type) (pτ : Closed τ)
        (Γ' : list cast_calculus.types.type) (τ' : cast_calculus.types.type) (C : cast_calculus.contexts.ctx) :
      cast_calculus.contexts.typed_ctx C Γ τ Γ' τ' →
      Γ ⊨ e ≤log≤ e' : τ →
      Γ' ⊨ stlc_mu.contexts.fill_ctx (backtranslate_ctx C) e ≤log≤ cast_calculus.contexts.fill_ctx C e' : τ'.
  Proof.
    revert Γ τ pτ Γ' τ' e e'.
    induction C; intros Γ τ pτ Γ' τ' e e' H.
    - by inversion H.
    - inversion_clear H. intro Hee'. simpl.
      apply back_ctx_item_relates with (Γ := Γ2) (τ := τ2). by eapply typed_ctx_closedness. auto. by eapply IHC.
  Qed.

  Lemma embed_ctx_item_relates (Γ : list stlc_mu.types.type) (e : stlc_mu.lang.expr) (e' : cast_calculus.lang.expr) (τ : stlc_mu.types.type) (pτ : Closed τ)
        (Γ' : list stlc_mu.types.type) (τ' : stlc_mu.types.type) (C : stlc_mu.contexts.ctx_item) :
      stlc_mu.contexts.typed_ctx_item C Γ τ Γ' τ' →
      (map embed_type Γ) ⊨ e ≤log≤ e' : (embed_type τ) →
      (map embed_type Γ') ⊨ stlc_mu.contexts.fill_ctx_item C e ≤log≤ cast_calculus.contexts.fill_ctx_item (embed_ctx_item C) e' : (embed_type τ').
  Proof.
    destruct C; intros; inversion H; simplify_eq; simpl.
    - by apply bin_log_related_lam.
    - eapply bin_log_related_app; eauto using embedding_relates.
    - eapply bin_log_related_app; eauto.
      assert (TArrow [|τ|] [|τ'|] = embed_type (stlc_mu.types.TArrow τ τ')) as ->; try done.
      eauto using embedding_relates.
    - eapply bin_log_related_pair; eauto using embedding_relates.
    - eapply bin_log_related_pair; eauto using embedding_relates.
    - by eapply bin_log_related_fst.
    - by eapply bin_log_related_snd.
    - by apply bin_log_related_injl.
    - by apply bin_log_related_injr.
    - eapply bin_log_related_case; try apply embedding_relates; try done.
      fold (embed_type τ1). assert ([|τ1|] :: map embed_type Γ' = map embed_type (τ1 :: Γ')) as ->; try done.
      eauto using embedding_relates.
      fold (embed_type τ2). assert ([|τ2|] :: map embed_type Γ' = map embed_type (τ2 :: Γ')) as ->; try done.
      eauto using embedding_relates.
    - eapply (bin_log_related_case _ _ _ _ _ _ _ _ (embed_type τ2)); try apply embedding_relates; try done.
      assert (TSum [|τ1|] [|τ2|] = embed_type (stlc_mu.types.TSum τ1 τ2)) as ->; try done.
      eauto using embedding_relates.
      assert ([|τ2|] :: map embed_type Γ' = map embed_type (τ2 :: Γ')) as ->; try done.
      eauto using embedding_relates.
    - eapply (bin_log_related_case _ _ _ _ _ _ _ (embed_type τ1)); try apply embedding_relates; try done.
      assert (TSum [|τ1|] [|τ2|] = embed_type (stlc_mu.types.TSum τ1 τ2)) as ->; try done.
      eauto using embedding_relates.
      assert ([|τ1|] :: map embed_type Γ' = map embed_type (τ1 :: Γ')) as ->; try done.
      eauto using embedding_relates.
    - apply bin_log_related_fold. by rewrite -embd_unfold_comm.
    - rewrite embd_unfold_comm. by apply bin_log_related_unfold.
  Qed.

  (** Static contexts are related to their embeddings *)
  Lemma embed_ctx_relates (Γ : list stlc_mu.types.type) (e : stlc_mu.lang.expr) (e' : cast_calculus.lang.expr) (τ : stlc_mu.types.type) (pτ : Closed τ)
        (Γ' : list stlc_mu.types.type) (τ' : stlc_mu.types.type) (C : stlc_mu.contexts.ctx) :
      stlc_mu.contexts.typed_ctx C Γ τ Γ' τ' →
      (map embed_type Γ) ⊨ e ≤log≤ e' : (embed_type τ) →
      (map embed_type Γ') ⊨ stlc_mu.contexts.fill_ctx C e ≤log≤ cast_calculus.contexts.fill_ctx (embed_ctx C) e' : (embed_type τ').
  Proof.
    revert Γ τ pτ Γ' τ' e e'.
    induction C; intros Γ τ pτ Γ' τ' e e' H.
    - by inversion H.
    - inversion_clear H. intro Hee'. simpl.
      apply embed_ctx_item_relates with (Γ := Γ2) (τ := τ2). by eapply stlc_mu.contexts.typed_ctx_closedness. auto. by eapply IHC.
  Qed.

End relation_for_specification_lemma.
