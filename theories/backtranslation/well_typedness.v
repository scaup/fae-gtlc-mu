From fae_gtlc_mu.cast_calculus Require Export typing contexts.
From fae_gtlc_mu.stlc_mu Require Export typing contexts.

From fae_gtlc_mu.backtranslation Require Import types expressions cast_help.general contexts.

Lemma well_typedness_expr Γ e τ :
  Γ ⊢ₜ e : τ →
    map backtranslate_type Γ ⊢ₛ backtranslate_expr e : backtranslate_type τ.
Proof.
  induction 1; simpl; try by constructor.
  - constructor. by rewrite list_lookup_fmap H.
  - eapply Fst_typed. apply IHtyped.
  - eapply Snd_typed. apply IHtyped.
  - eapply Case_typed. apply IHtyped1. apply IHtyped2. apply IHtyped3.
  - eapply App_typed. apply IHtyped1. apply IHtyped2.
  - apply Fold_typed.
    rewrite unfolding_backtranslation_commutes in IHtyped.
    apply IHtyped.
  - rewrite unfolding_backtranslation_commutes.
    apply Unfold_typed. apply IHtyped.
  - destruct (cons_stand_dec τi τf); destruct (decide (TClosed τi)); destruct (decide (TClosed τf)); try by contradiction.
    eapply App_typed.
    rewrite /𝓕c /env_subst. admit.
    apply IHtyped.
  - apply Ω_typed. admit.
Admitted.

From fae_gtlc_mu.embedding Require Export types.

Lemma well_typedness_ctx_item Γ τ Γ' τ' C :
  cast_calculus.contexts.typed_ctx_item C Γ τ Γ' τ' →
  typed_ctx_item (backtranslate_ctx_item C) (map backtranslate_type Γ) (backtranslate_type τ) (map backtranslate_type Γ') (backtranslate_type τ').
Proof.
  induction 1; try (by constructor).
  - apply TP_CTX_AppL. apply well_typedness_expr; done.
  - apply TP_CTX_AppR.
    assert (triv : backtranslate_type (types.TArrow τ τ') = TArrow <<τ>> <<τ'>>). by simpl. rewrite -triv. clear triv.
    by apply well_typedness_expr.
  - constructor. by apply well_typedness_expr.
  - constructor. by apply well_typedness_expr.
  - constructor.
    assert (triv : backtranslate_type τ1 :: (map backtranslate_type Γ) = map backtranslate_type (τ1 :: Γ)). by simpl. rewrite triv. clear triv.
      by apply well_typedness_expr.
    assert (triv : backtranslate_type τ2 :: (map backtranslate_type Γ) = map backtranslate_type (τ2 :: Γ)). by simpl. rewrite triv. clear triv.
      by apply well_typedness_expr.
  - apply TP_CTX_CaseM with (τ2 := <<τ2>>).
    assert (triv : backtranslate_type (types.TSum τ1 τ2) = TSum <<τ1>> <<τ2>>). by simpl. rewrite -triv. clear triv.
      by apply well_typedness_expr.
    assert (triv : backtranslate_type τ2 :: (map backtranslate_type Γ) = map backtranslate_type (τ2 :: Γ)). by simpl. rewrite triv. clear triv.
      by apply well_typedness_expr.
  - apply TP_CTX_CaseR with (τ1 := <<τ1>>).
    assert (triv : backtranslate_type (types.TSum τ1 τ2) = TSum <<τ1>> <<τ2>>). by simpl. rewrite -triv. clear triv.
      by apply well_typedness_expr.
    assert (triv : backtranslate_type τ1 :: (map backtranslate_type Γ) = map backtranslate_type (τ1 :: Γ)). by simpl. rewrite triv. clear triv.
      by apply well_typedness_expr.
  - rewrite unfolding_backtranslation_commutes. apply TP_CTX_Fold.
  - rewrite unfolding_backtranslation_commutes. apply TP_CTX_Unfold.
  - simpl. destruct (cons_stand_dec τi τf); destruct (decide (TClosed τi)); destruct (decide (TClosed τf)); try by contradiction.
    eapply TP_CTX_AppR. admit.
Admitted.

Lemma well_typedness_ctx Γ τ Γ' τ' C :
  cast_calculus.contexts.typed_ctx C Γ τ Γ' τ' →
  typed_ctx (backtranslate_ctx C) (map backtranslate_type Γ) (backtranslate_type τ) (map backtranslate_type Γ') (backtranslate_type τ').
Proof.
  induction 1.
  - constructor.
  - econstructor; simpl. by apply well_typedness_ctx_item.
    auto.
Qed.
