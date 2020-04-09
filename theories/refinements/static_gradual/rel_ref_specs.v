From fae_gtlc_mu.refinements.static_gradual Require Export logical_relation compat_easy.
From fae_gtlc_mu.embedding Require Import expressions types.
From fae_gtlc_mu.cast_calculus Require Export types.

Ltac fold_interp :=
  match goal with
  | |- context [ interp_expr (interp_arrow (interp ?A) (interp ?A'))
                            ?B (?C, ?D) ] =>
    change (interp_expr (interp_arrow (interp A) (interp A')) B (C, D)) with
    (interp_expr (interp (TArrow A A')) B (C, D))
  | |- context [ interp_expr (interp_prod (interp ?A) (interp ?A'))
                            ?B (?C, ?D) ] =>
    change (interp_expr (interp_prod (interp A) (interp A')) B (C, D)) with
    (interp_expr (interp (TProd A A')) B (C, D))
  | |- context [ interp_expr (interp_prod (interp ?A) (interp ?A'))
                            ?B (?C, ?D) ] =>
    change (interp_expr (interp_prod (interp A) (interp A')) B (C, D)) with
    (interp_expr (interp (TProd A A')) B (C, D))
  | |- context [ interp_expr (interp_sum (interp ?A) (interp ?A'))
                            ?B (?C, ?D) ] =>
    change (interp_expr (interp_sum (interp A) (interp A')) B (C, D)) with
    (interp_expr (interp (TSum A A')) B (C, D))
  | |- context [ interp_expr (interp_rec (interp ?A)) ?B (?C, ?D) ] =>
    change (interp_expr (interp_rec (interp A)) B (C, D)) with
    (interp_expr (interp (TRec A)) B (C, D))
  end.

Section relation_for_specification_lemma.
  Context `{!heapG Σ, !gradRN Σ}.

  (* Notation "Γ ⊨ e '≤log≤' e' : τ" := *)
    (* (bin_log_related Γ e e' τ) (at level 74, e, e', τ at next level). *)

  Theorem embedding_relates (Γ : list stlc_mu.typing.type) (e : stlc_mu.lang.expr) (τ : stlc_mu.typing.type) :
    Γ ⊢ₛ e : τ → map embed_type Γ ⊨ e ≤log≤ [[e]] : [| τ |].
  Proof.
    induction 1; simpl.
    - apply bin_log_related_var. by rewrite list_lookup_fmap H.
    - by apply bin_log_related_unit.
    - apply bin_log_related_pair; eauto.
    - eapply bin_log_related_fst; eauto.
    - eapply bin_log_related_snd; eauto.
    - eapply bin_log_related_injl; eauto.
    - eapply bin_log_related_injr; eauto.
    - eapply bin_log_related_case; try done;
        ((by (rewrite map_length; match goal with H : _ |- _ => eapply (stlc_mu.typing.typed_n_closed _ _ _ H) end)) ||
         (try done)).
      admit.
      admit.
    - eapply bin_log_related_lam; eauto.
      rewrite map_length.
        match goal with H : _ |- _ => eapply (stlc_mu.typing.typed_n_closed _ _ _ H) end.
        admit.
    - eapply bin_log_related_app; eauto.
    - eapply bin_log_related_fold; eauto.
      by rewrite -embed_through_unfold.
    - rewrite embed_through_unfold. eapply bin_log_related_unfold; eauto.
  Admitted.

  From fae_gtlc_mu.refinements.static_gradual Require Import compat_cast.all.
  From fae_gtlc_mu.backtranslation Require Import expressions.

  Theorem back_relates (Γ : list cast_calculus.types.type) (e : cast_calculus.lang.expr) (τ : cast_calculus.types.type) :
    Γ ⊢ₜ e : τ → Γ ⊨ <<e>> ≤log≤ e : τ.
  Proof.
    induction 1; simpl.
    - by apply bin_log_related_var.
    - by apply bin_log_related_unit.
    - apply bin_log_related_pair; eauto.
    - eapply bin_log_related_fst; eauto.
    - eapply bin_log_related_snd; eauto.
    - eapply bin_log_related_injl; eauto.
    - eapply bin_log_related_injr; eauto.
    - eapply bin_log_related_case; try done.
      admit.
      admit.
      admit.
      admit.
    - eapply bin_log_related_lam; eauto.
      admit.
      admit.
    - eapply bin_log_related_app; eauto.
    - eapply bin_log_related_fold; eauto.
    - eapply bin_log_related_unfold; eauto.
    - destruct (cons_stand_dec τi τf); destruct (decide (TClosed τi)); destruct (decide (TClosed τf)); try by contradiction.
      by apply bin_log_related_back_cast.
    - apply bin_log_related_omega.
  Admitted.

  From fae_gtlc_mu.stlc_mu Require Export contexts.
  From fae_gtlc_mu.cast_calculus Require Export contexts.
  From fae_gtlc_mu.backtranslation Require Import contexts.

  Lemma back_ctx_relates (Γ : list stlc_mu.typing.type) (e : stlc_mu.lang.expr) (e' : cast_calculus.lang.expr)
        (τ : stlc_mu.typing.type) (Γ' : list cast_calculus.types.type) (τ' : cast_calculus.types.type) (C : cast_calculus.contexts.ctx) :
    (∀ f, e.[upn (length Γ) f] = e) →
    (∀ f, e'.[upn (length Γ) f] = e') →
      cast_calculus.contexts.typed_ctx C (map embed_type Γ) [|τ|] Γ' τ' →
      map embed_type Γ ⊨ e ≤log≤ e' : [| τ |] →
      Γ' ⊨ stlc_mu.contexts.fill_ctx (backtranslate_ctx C) e ≤log≤ cast_calculus.contexts.fill_ctx C e' : τ'.
  Proof.
    revert Γ τ Γ' τ' e e'.
    induction C as [aa |c C] => Γ τ Γ' τ' e e' H1 H2; simpl.
    - by intros; inversion_clear H.
    - inversion_clear 1 as [aa |? ? ? ? ? ? ? ? Hx1 Hx2]. intros H3.
      specialize (IHC _ _ _ _ e e' H1 H2 Hx2 H3).
      inversion Hx1; subst; simpl; try fold_interp.
      + eapply bin_log_related_lam.
        admit.
        admit.
        admit.
        (* eauto; *)
          (* match goal with *)
            (* H : _ |- _ => eapply (typed_ctx_n_closed _ _ _ _ _ _ _ H) *)
          (* end. *)
      + eapply bin_log_related_app; eauto using back_relates.
      + eapply bin_log_related_app; eauto using back_relates.
      + eapply bin_log_related_pair; eauto using back_relates.
      + eapply bin_log_related_pair; eauto using back_relates.
      + eapply bin_log_related_fst; eauto.
      + eapply bin_log_related_snd; eauto.
      + eapply bin_log_related_injl; eauto.
      + eapply bin_log_related_injr; eauto.
      + eapply bin_log_related_case; try done; try apply back_relates.
        admit.
        admit.
        admit.
        admit.
        admit.
        admit.
      + eapply bin_log_related_case; try done; try apply back_relates.
        admit.
        admit.
        admit.
        admit.
        admit.
        admit.
      + eapply bin_log_related_case; try done; try apply back_relates.
        admit.
        admit.
        admit.
        admit.
        admit.
        admit.
      + eapply bin_log_related_fold; eauto.
      + eapply bin_log_related_unfold; eauto.
      + destruct (cons_stand_dec τ2 τ'); destruct (decide (TClosed τ2)); destruct (decide (TClosed τ')); try by contradiction.
        simpl.
        by apply bin_log_related_back_cast.
  Admitted.

End relation_for_specification_lemma.
