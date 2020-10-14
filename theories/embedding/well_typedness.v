From fae_gtlc_mu.embedding Require types types_lemmas expressions contexts.
From fae_gtlc_mu.stlc_mu Require typing.
From fae_gtlc_mu.embedding Require Import types types_lemmas expressions contexts.
From fae_gtlc_mu.stlc_mu Require Import typing.
From fae_gtlc_mu.cast_calculus Require Export typing contexts.

Lemma well_typedness_expr Γ e τ : (Γ ⊢ₛ e : τ) →
    map embed_type Γ ⊢ₜ embed_expr e : embed_type τ.
Proof.
  induction 1; simpl; try by econstructor.
  - constructor. by apply embd_closed. by rewrite list_lookup_fmap H.
  - apply InjL_typed. by apply embd_closed. auto.
  - apply InjR_typed. by apply embd_closed. auto.
  - eapply Lam_typed. by apply embd_closed. apply IHtyped.
  - apply Fold_typed.
    by rewrite embd_unfold_comm in IHtyped.
  - rewrite embd_unfold_comm.
    by apply Unfold_typed.
Qed.

Lemma well_typedness_ctx_item Γ (τ : stlc_mu.types.type) (pτ : Closed τ) Γ' τ' C :
  stlc_mu.contexts.typed_ctx_item C Γ τ Γ' τ' →
  typed_ctx_item (embed_ctx_item C) (map embed_type Γ) (embed_type τ) (map embed_type Γ') (embed_type τ').
Proof.
  induction 1; try (by constructor).
  - apply TP_CTX_Lam. by apply embd_closed.
  - apply TP_CTX_AppL. apply well_typedness_expr; done.
  - apply TP_CTX_AppR.
    assert (TArrow [|τ|] [|τ'|] = embed_type (stlc_mu.types.TArrow τ τ')) as ->; try done.
    by apply well_typedness_expr.
  - constructor. by apply well_typedness_expr.
  - constructor. by apply well_typedness_expr.
  - constructor. by apply embd_closed.
  - constructor. by apply embd_closed.
  - constructor; rewrite -map_cons; by apply well_typedness_expr.
  - eapply TP_CTX_CaseM with (τ2 := [|τ2|]); auto.
    assert (TSum [|τ1|] [|τ2|] = embed_type (stlc_mu.types.TSum τ1 τ2)) as ->; try done.
    by apply well_typedness_expr. rewrite -map_cons. by apply well_typedness_expr.
  - eapply TP_CTX_CaseR with (τ1 := [|τ1|]); auto.
    assert (TSum [|τ1|] [|τ2|] = embed_type (stlc_mu.types.TSum τ1 τ2)) as ->; try done.
    by apply well_typedness_expr. rewrite -map_cons. by apply well_typedness_expr.
  - rewrite embd_unfold_comm. apply TP_CTX_Fold.
  - rewrite embd_unfold_comm. apply TP_CTX_Unfold.
Qed.

Lemma well_typedness_ctx Γ (τ : stlc_mu.types.type) (pτ : Closed τ) Γ' τ' C :
  stlc_mu.contexts.typed_ctx C Γ τ Γ' τ' →
  typed_ctx (embed_ctx C) (map embed_type Γ) (embed_type τ) (map embed_type Γ') (embed_type τ').
Proof.
  induction 1.
  - constructor.
  - econstructor; simpl. apply well_typedness_ctx_item with (τ := τ2).
    eapply stlc_mu.contexts.typed_ctx_closedness. apply pτ. apply H0. apply H. apply IHtyped_ctx. auto.
Qed.
