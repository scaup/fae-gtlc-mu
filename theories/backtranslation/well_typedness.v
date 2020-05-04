From fae_gtlc_mu.cast_calculus Require Export typing (*contexts*).
From fae_gtlc_mu.stlc_mu Require Export typing (*contexts*).

From fae_gtlc_mu.backtranslation Require Import types expressions cast_help.general (*contexts*).

Lemma force_typed Γ Γ' pΓ pΓ' e τ τ' pτ pτ' : Γ & pΓ ⊢ₛ e : τ & pτ → Γ = Γ' → τ = τ' → Γ' & pΓ' ⊢ₛ e : τ & pτ'. (** use with cae *)
Proof. intros. simplify_eq. eapply PI_typed. eapply PI_Γ_typed. done. Qed.

Lemma well_typedness_expr Γ pΓ e τ pτ :
  Γ & pΓ ⊢ₜ e : τ & pτ →
    map backtranslate_type Γ & (Forall_fmap_impl _ _ _ _ (@back_closed) pΓ) ⊢ₛ backtranslate_expr e : backtranslate_type τ & (back_closed pτ).
Proof.
  induction 1; simpl; try by econstructor.
  - constructor. by rewrite list_lookup_fmap H.
  - eapply Case_typed. apply IHtyped1.
    eapply PI_typed. eapply PI_Γ_typed. apply IHtyped2.
    eapply PI_typed. eapply PI_Γ_typed. apply IHtyped3.
  - eapply Lam_typed. eapply PI_Γ_typed. apply IHtyped.
  - assert (HC : TClosed <<(τb.[cast_calculus.types.TRec τb/])>>). by apply back_closed.
    eapply rewrite_typed.
    eapply Fold_typed. eapply PI_Γ_typed. eapply rewrite_typed. apply IHtyped.
    rewrite back_unfold_comm. auto. auto.
  - eapply Unfold_typed_help. by rewrite back_unfold_comm.
    eapply rewrite_typed. by apply IHtyped. by simpl.
  - destruct (decide (cons_stand_open τi τf)); destruct (decide (cast_calculus.types.TClosed τi)); destruct (decide (cast_calculus.types.TClosed τf)); try by contradiction.
    eapply App_typed.
    apply EClosed_typed. apply 𝓕c_closed; auto.
    rewrite /𝓕c /env_subst. asimpl. eapply force_typed. apply 𝓕_typed. auto. auto.
    apply IHtyped.
  - apply Ω_typed.
  Unshelve.
   try by apply back_closed.
   try by apply back_closed.
   try by apply back_closed.
   cut (TClosed (<<(cast_calculus.types.TRec τb)>>)). by simpl.
   by apply back_closed.
   by rewrite back_unfold_comm in HC.
   cut (TClosed (<<(cast_calculus.types.TRec τb)>>)). by simpl.
   by apply back_closed.
   cut (TClosed (<<(cast_calculus.types.TArrow τi τf)>>)). by simpl.
   apply back_closed. by apply cast_calculus.types.TArrow_closed.
   auto.
   auto.
   auto.
Qed.

(* From fae_gtlc_mu.embedding Require Export types. *)

(* Lemma well_typedness_ctx_item Γ τ Γ' τ' C : *)
(*   cast_calculus.contexts.typed_ctx_item C Γ τ Γ' τ' → *)
(*   typed_ctx_item (backtranslate_ctx_item C) (map backtranslate_type Γ) (backtranslate_type τ) (map backtranslate_type Γ') (backtranslate_type τ'). *)
(* Proof. *)
(*   induction 1; try (by constructor). *)
(*   - apply TP_CTX_AppL. apply well_typedness_expr; done. *)
(*   - apply TP_CTX_AppR. *)
(*     assert (triv : backtranslate_type (types.TArrow τ τ') = TArrow <<τ>> <<τ'>>). by simpl. rewrite -triv. clear triv. *)
(*     by apply well_typedness_expr. *)
(*   - constructor. by apply well_typedness_expr. *)
(*   - constructor. by apply well_typedness_expr. *)
(*   - constructor. *)
(*     assert (triv : backtranslate_type τ1 :: (map backtranslate_type Γ) = map backtranslate_type (τ1 :: Γ)). by simpl. rewrite triv. clear triv. *)
(*       by apply well_typedness_expr. *)
(*     assert (triv : backtranslate_type τ2 :: (map backtranslate_type Γ) = map backtranslate_type (τ2 :: Γ)). by simpl. rewrite triv. clear triv. *)
(*       by apply well_typedness_expr. *)
(*   - apply TP_CTX_CaseM with (τ2 := <<τ2>>). *)
(*     assert (triv : backtranslate_type (types.TSum τ1 τ2) = TSum <<τ1>> <<τ2>>). by simpl. rewrite -triv. clear triv. *)
(*       by apply well_typedness_expr. *)
(*     assert (triv : backtranslate_type τ2 :: (map backtranslate_type Γ) = map backtranslate_type (τ2 :: Γ)). by simpl. rewrite triv. clear triv. *)
(*       by apply well_typedness_expr. *)
(*   - apply TP_CTX_CaseR with (τ1 := <<τ1>>). *)
(*     assert (triv : backtranslate_type (types.TSum τ1 τ2) = TSum <<τ1>> <<τ2>>). by simpl. rewrite -triv. clear triv. *)
(*       by apply well_typedness_expr. *)
(*     assert (triv : backtranslate_type τ1 :: (map backtranslate_type Γ) = map backtranslate_type (τ1 :: Γ)). by simpl. rewrite triv. clear triv. *)
(*       by apply well_typedness_expr. *)
(*   - rewrite back_unfold_comm. apply TP_CTX_Fold. *)
(*   - rewrite back_unfold_comm. apply TP_CTX_Unfold. *)
(*   - simpl. destruct (cons_stand_dec τi τf); destruct (decide (TClosed τi)); destruct (decide (TClosed τf)); try by contradiction. *)
(*     eapply TP_CTX_AppR. admit. *)
(* Admitted. *)

(* Lemma well_typedness_ctx Γ τ Γ' τ' C : *)
(*   cast_calculus.contexts.typed_ctx C Γ τ Γ' τ' → *)
(*   typed_ctx (backtranslate_ctx C) (map backtranslate_type Γ) (backtranslate_type τ) (map backtranslate_type Γ') (backtranslate_type τ'). *)
(* Proof. *)
(*   induction 1. *)
(*   - constructor. *)
(*   - econstructor; simpl. by apply well_typedness_ctx_item. *)
(*     auto. *)
(* Qed. *)
