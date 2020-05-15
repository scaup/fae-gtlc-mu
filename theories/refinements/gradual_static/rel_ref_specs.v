From fae_gtlc_mu.refinements.gradual_static Require Export logical_relation compat_easy.
From fae_gtlc_mu.embedding Require Import expressions types.
From fae_gtlc_mu.stlc_mu Require Export typing.
From fae_gtlc_mu.cast_calculus Require Export types.

Section relation_for_specification_lemma.
  Context `{!implG Σ, !specG Σ}.

  Theorem embedding_relates (Γ : list stlc_mu.types.type) (e : stlc_mu.lang.expr) (τ : stlc_mu.types.type) :
    Γ ⊢ₛ e : τ → map embed_type Γ ⊨ [[e]] ≤log≤ e : [| τ |].
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

  From fae_gtlc_mu.refinements.gradual_static Require Import compat_cast.all.
  From fae_gtlc_mu.backtranslation Require Import expressions well_typedness.

  Theorem back_relates (Γ : list cast_calculus.types.type) (e : cast_calculus.lang.expr) (τ : cast_calculus.types.type) :
    Γ ⊢ₜ e : τ → Γ ⊨ e ≤log≤ <<e>> : τ.
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
    - assert (pτi : cast_calculus.types.TClosed τi). apply (cast_calculus.typing.typed_closed H).
      destruct (cons_stand_open_dec τi τf);
                destruct (decide (cast_calculus.types.TClosed τi));
                destruct (decide (cast_calculus.types.TClosed τf)); try by contradiction.
      by apply bin_log_related_back_cast.
    - apply bin_log_related_omega.
  Qed.

  From fae_gtlc_mu.stlc_mu Require Export contexts.
  From fae_gtlc_mu.cast_calculus Require Export contexts.
  From fae_gtlc_mu.backtranslation Require Import contexts.

  Lemma back_ctx_item_relates (Γ : list cast_calculus.types.type) (e : cast_calculus.lang.expr) (e' : stlc_mu.lang.expr) (τ : cast_calculus.types.type) (pτ : TClosed τ)
        (Γ' : list cast_calculus.types.type) (τ' : cast_calculus.types.type) (C : cast_calculus.contexts.ctx_item) :
      cast_calculus.contexts.typed_ctx_item C Γ τ Γ' τ' →
      Γ ⊨ e ≤log≤ e' : τ →
      Γ' ⊨ cast_calculus.contexts.fill_ctx_item C e ≤log≤ stlc_mu.contexts.fill_ctx_item (backtranslate_ctx_item C) e' : τ'.
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
    - destruct (cons_stand_open_dec τ τ');
                destruct (decide (cast_calculus.types.TClosed τ));
                destruct (decide (cast_calculus.types.TClosed τ')); try by contradiction.
      by apply bin_log_related_back_cast.
  Qed.

  Lemma back_ctx_relates (Γ : list cast_calculus.types.type) (e : cast_calculus.lang.expr) (e' : stlc_mu.lang.expr) (τ : cast_calculus.types.type) (pτ : TClosed τ)
        (Γ' : list cast_calculus.types.type) (τ' : cast_calculus.types.type) (C : cast_calculus.contexts.ctx) :
      cast_calculus.contexts.typed_ctx C Γ τ Γ' τ' →
      Γ ⊨ e ≤log≤ e' : τ →
      Γ' ⊨ cast_calculus.contexts.fill_ctx C e ≤log≤ stlc_mu.contexts.fill_ctx (backtranslate_ctx C) e' : τ'.
  Proof.
    revert Γ τ pτ Γ' τ' e e'.
    induction C; intros Γ τ pτ Γ' τ' e e' H.
    - by inversion H.
    - inversion_clear H. intro Hee'. simpl.
      apply back_ctx_item_relates with (Γ := Γ2) (τ := τ2). by eapply typed_ctx_closedness. auto. by eapply IHC.
  Qed.

End relation_for_specification_lemma.
