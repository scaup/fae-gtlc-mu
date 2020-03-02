From fae_gtlc_mu.stlc_mu Require Export typing lang lib.fix.
From fae_gtlc_mu.cast_calculus Require Export types consistency.structural.definition.
From fae_gtlc_mu.backtranslation.cast_help Require Export universe embed extract between factorize.
(* From fae_gtlc_mu.backtranslation Require Export types de_bruijn_hell. *)

(** emulation of a cast between an arbitrary pair of consistent types *)
(* recursively defined on the alternative consistency relation *)

Fixpoint 𝓕 {A : list (types.type * types.type)} {τi τf : cast_calculus.types.type} (P : A ⊢ τi ~ τf) : expr :=
  match P with
  | consStarTGround _ τG G => extract τG G
  | consTGroundStar _ τG G => embed τG G
  | consTauStar _ τ τG pUBτ pτnG pτnStar pτSτG pτConsτG =>
    factorization_up
      (𝓕 pτConsτG) τG (get_shape_is_ground pτSτG)
  | consStarTau _ τ τG pUBτ pτnG pτnStar pτSτG pτGConsτ =>
    factorization_down
      (𝓕 pτGConsτ) τG (get_shape_is_ground pτSτG)
  | consBaseBase _ => identity
  | consStarStar _ => identity
  | consTSumTSum _ τ1 τ1' τ2 τ2' pCons1 pCons2 =>
    between_TSum
      (𝓕 pCons1)
      (𝓕 pCons2)
  | consTProdTProd _ τ1 τ1' τ2 τ2' pCons1 pCons2 =>
    between_TProd
      (𝓕 pCons1)
      (𝓕 pCons2)
  | consTArrowTArrow _ τ1 τ2 τ3 τ4 pCons31 pCons24 =>
    between_TArrow
      (𝓕 pCons31)
      (𝓕 pCons24)
  | consTRecTRecExposeCall _ τl τr pμτlμτrnotA pUnfτlUnfτr =>
    between_TRec
      (𝓕 pUnfτlUnfτr)
  | consTRecTRecUseCall _ τl τr i pμτlμtrinA => Lam ((Var (S i)) (Var 0))
  end.

Lemma 𝓕_is_value {A} {τi τf} (pC : A ⊢ τi ~ τf) : is_Some $ to_val (𝓕 pC).
Proof.
  induction pC; try destruct G; simplify_option_eq; eauto.
Qed.

Definition 𝓕V {A} {τi τf} (pC : A ⊢ τi ~ τf) : val := is_Some_proj (𝓕_is_value pC).

From fae_gtlc_mu.stlc_mu Require Export typing lang lib.fix.

Definition pair_to_static_function (p : cast_calculus.types.type * cast_calculus.types.type) : stlc_mu.typing.type :=
  TArrow <<p.1>> <<p.2>>.

Lemma 𝓕_typed (A : list (cast_calculus.types.type * cast_calculus.types.type)) (τi τf : cast_calculus.types.type) (pτiConsτf : A ⊢ τi ~ τf) :
  (map pair_to_static_function A) ⊢ₛ (𝓕 pτiConsτf) : (TArrow <<τi>> <<τf>>).
Proof.
  induction pτiConsτf; simpl.
  - apply extract_typed.
  - apply embed_typed.
  - apply factorization_up_typed.
    apply IHpτiConsτf.
  - apply factorization_down_typed.
    apply IHpτiConsτf.
  - apply identity_typed.
  - apply identity_typed.
  - apply between_TSum_typed.
    apply IHpτiConsτf1.
    apply IHpτiConsτf2.
  - apply between_TProd_typed.
    apply IHpτiConsτf1.
    apply IHpτiConsτf2.
  - apply between_TArrow_typed.
    apply IHpτiConsτf1.
    apply IHpτiConsτf2.
  - apply between_TRec_typed.
    admit.
    admit.
    rewrite map_cons in IHpτiConsτf.
    repeat rewrite unfolding_backtranslation_commutes in IHpτiConsτf.
    apply IHpτiConsτf.
  - apply Lam_typed. eapply App_typed. apply Var_typed.
    simpl. rewrite list_lookup_fmap.
    by rewrite pμτlμtrinA.
Admitted.
