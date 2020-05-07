From fae_gtlc_mu.stlc_mu Require Export typing contexts.
From fae_gtlc_mu.cast_calculus Require Export typing contexts.

From fae_gtlc_mu.embedding Require Import types expressions.

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

