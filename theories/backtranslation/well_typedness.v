From fae_gtlc_mu.cast_calculus Require Export typing contexts.
From fae_gtlc_mu.stlc_mu Require Export typing contexts.
From fae_gtlc_mu.cast_calculus Require Import lang consistency consistency_lemmas.
From fae_gtlc_mu.backtranslation Require Import types expressions cast_help.general_def cast_help.general_def_lemmas contexts.

Lemma well_typedness_expr Γ e τ : (Γ ⊢ₜ e : τ) →
    map backtranslate_type Γ ⊢ₛ backtranslate_expr e : backtranslate_type τ.
Proof.
  induction 1; simpl; try by econstructor.
  - constructor. by apply back_closed. by rewrite list_lookup_fmap H.
  - apply InjL_typed. by apply back_closed. auto.
  - apply InjR_typed. by apply back_closed. auto.
  - eapply Lam_typed. by apply back_closed. apply IHtyped.
  - apply Fold_typed.
    by rewrite back_unfold_comm in IHtyped.
  - rewrite back_unfold_comm.
    by apply Unfold_typed.
  - assert (pτi : Closed τi). apply (cast_calculus.typing.typed_closed H).
    destruct (consistency_open_dec τi τf);
      destruct (decide (Closed τi));
      destruct (decide (Closed τf)); try by contradiction.
    eapply App_typed with (τ1 := <<τi>>).
    apply EClosed_typed; auto. apply 𝓕c_closed; auto.
    rewrite /𝓕c /env_subst. asimpl.
    apply 𝓕_typed with (A := []); auto. apply IHtyped.
  - apply Ω_typed. by apply back_closed.
Qed.

(* From fae_gtlc_mu.embedding Require Export types. *)

Lemma well_typedness_ctx_item Γ (τ : cast_calculus.types.type) (pτ : Closed τ) Γ' τ' C :
  cast_calculus.contexts.typed_ctx_item C Γ τ Γ' τ' →
  typed_ctx_item (backtranslate_ctx_item C) (map backtranslate_type Γ) (backtranslate_type τ) (map backtranslate_type Γ') (backtranslate_type τ').
Proof.
  induction 1; try (by constructor).
  - apply TP_CTX_Lam. by apply back_closed.
  - apply TP_CTX_AppL. apply well_typedness_expr; done.
  - apply TP_CTX_AppR.
    cut (map backtranslate_type Γ ⊢ₛ backtranslate_expr e1 : <<(cast_calculus.types.TArrow τ τ')>>). by simpl.
    by apply well_typedness_expr.
  - constructor. by apply well_typedness_expr.
  - constructor. by apply well_typedness_expr.
  - constructor. by apply back_closed.
  - constructor. by apply back_closed.
  - constructor; rewrite -map_cons; by apply well_typedness_expr.
  - eapply TP_CTX_CaseM with (τ2 := <<τ2>>); auto.
    cut (map backtranslate_type Γ ⊢ₛ backtranslate_expr e0 : <<(cast_calculus.types.TSum τ1 τ2)>>). by simpl.
    by apply well_typedness_expr. rewrite -map_cons. by apply well_typedness_expr.
  - eapply TP_CTX_CaseR with (τ1 := <<τ1>>); auto.
    cut (map backtranslate_type Γ ⊢ₛ backtranslate_expr e0 : <<(cast_calculus.types.TSum τ1 τ2)>>). by simpl.
    by apply well_typedness_expr. rewrite -map_cons. by apply well_typedness_expr.
  - rewrite back_unfold_comm. apply TP_CTX_Fold.
  - rewrite back_unfold_comm. apply TP_CTX_Unfold.
  - simpl. destruct (consistency_open_dec τi τf); destruct (decide (Closed τi)); destruct (decide (Closed τf)); try by contradiction.
    apply TP_CTX_AppR. apply EClosed_typed. apply 𝓕c_closed; auto.
    rewrite /𝓕c /=. asimpl. apply 𝓕_typed with (A := []); auto.
Qed.

Lemma well_typedness_ctx Γ (τ : cast_calculus.types.type) (pτ : Closed τ) Γ' τ' C :
  cast_calculus.contexts.typed_ctx C Γ τ Γ' τ' →
  typed_ctx (backtranslate_ctx C) (map backtranslate_type Γ) (backtranslate_type τ) (map backtranslate_type Γ') (backtranslate_type τ').
Proof.
  induction 1.
  - constructor.
  - econstructor; simpl. apply well_typedness_ctx_item with (τ := τ2).
    eapply cast_calculus.contexts.typed_ctx_closedness. apply pτ. apply H0. apply H. apply IHtyped_ctx. auto.
Qed.
