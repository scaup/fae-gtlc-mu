From fae_gtlc_mu.cast_calculus Require Export types consistency.structural.
From fae_gtlc_mu.stlc_mu Require Export typing lang lib.fix.
From fae_gtlc_mu.stlc_mu.lib Require Export universe.
From fae_gtlc_mu.stlc_mu.lib.cast_emulations Require Export embed factorize extract between.
From fae_gtlc_mu.backtranslation Require Export types.

(** emulation of a cast between an arbitrary pair of consistent types *)
(* recursively defined on the alternative consistency relation *)

Fixpoint 𝓕 (A : list Assumption) (τi τf : cast_calculus.types.type) (P : A ⊢ τi ~ τf) : expr :=
  match P with
  | consStarTGround _ τ G (* ⋆ ~ G *) => extract τ G
  | consTGroundStar _ τ G (* G ~ ⋆ *) => embed τ G
  | consTauStar _ τ τG pUB nGτ nSτ pshapeτ PττG =>
    factorization_up (𝓕 A τ τG PττG) τG (get_shape_is_ground pshapeτ)
  | consStarTau _ τ τG pUB nGτ nSτ pshapeτ PττG =>
    factorization_down (𝓕 A τG τ PττG) τG (get_shape_is_ground pshapeτ)
  | consBaseBase _ => identity
  | consStarStar _ => identity
  | consTSumTSum _ τ1 τ1' τ2 τ2' P1 P2 =>
    between_TSum
      (𝓕 A τ1 τ1' P1)
      (𝓕 A τ2 τ2' P2)
  | consTProdTProd _ τ1 τ1' τ2 τ2' P1 P2 =>
    between_TProd
      (𝓕 A τ1 τ1' P1)
      (𝓕 A τ2 τ2' P2)
  | consTArrowTArrow _ τ1 τ2 τ3 τ4 P31 P24 =>
    between_TArrow
      (𝓕 A τ3 τ1 P31)
      (𝓕 A τ2 τ4 P24)
  | consExposeRecursion _ τi τf PτinS PτfnS Pτiτf =>
    between_TRec (𝓕 (LogBodies τi τf PτinS PτfnS :: _) τi τf Pτiτf)
  | consExposeRecursionLStar _ τ P => Unit
  | consExposeRecursionRStar _ τ P => Unit
  | consExposeExtraRecursionRStar _ i τb τb' P P' x x0 => Unit
  | consExposeExtraRecursionLStar _ i τb τb' P P' x x0 => Unit
  | consUseRecursion _ i x => Var i
  | consUseRecursionLStar _ i x => Var i
  | consUseRecursionRStar _ i x => Var i
  | consUseExtraRecursionLStar _ i x => Var i
  | consUseExtraRecursionRStar _ i x => Var i
  end.

Definition closed_gradual_pair_to_type (ττ' : cast_calculus.types.type * cast_calculus.types.type) : type :=
  match ττ' with
  | pair τ τ' => TArrow (backtranslate_type τ) (backtranslate_type τ')
  end.

Definition assumptions_to_context (A : list Assumption) : list type :=
  map closed_gradual_pair_to_type (assumptions_to_closed_gradual_pairs A).

Definition initial_type (τi τf : cast_calculus.types.type) (A : list Assumption) : type :=
  backtranslate_type $ fst (close_up (τi, τf) (assumptions_to_closed_gradual_pairs A)).

Definition final_type (τi τf : cast_calculus.types.type) (A : list Assumption) : type :=
  backtranslate_type $ snd (close_up (τi, τf) (assumptions_to_closed_gradual_pairs A)).

Lemma 𝓕_typed (A : list Assumption) (PA : UBAssumptions A) (τi τf : cast_calculus.types.type) (P : A ⊢ τi ~ τf) :
  (assumptions_to_context A) ⊢ₛ (𝓕 A τi τf P) : ((initial_type τi τf A) → (final_type τi τf A)).
Proof.
  induction P; intros.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - simpl. apply between_T
    apply Lam_typed.
    apply App_typed with (τ1 := initial_type (types.TRec τi) (types.TRec τf) A).
    apply App_typed with (τ1 := ((initial_type (types.TRec τi) (types.TRec τf) A
     → final_type (types.TRec τi) (types.TRec τf) A) → (initial_type (types.TRec τi) (types.TRec τf) A
     → final_type (types.TRec τi) (types.TRec τf) A))).
    apply Fix_typed.
    admit. (** initial and final types are closed!! *)
    apply Lam_typed.
    apply Lam_typed.
    assert (Paa : final_type (types.TRec τi) (types.TRec τf) A = TRec (final_type τi τf A)).
    admit.
    assert (Pbb : initial_type (types.TRec τi) (types.TRec τf) A = TRec (initial_type τi τf A)).
    admit.
    rewrite Paa.
    apply Fold_typed.
    rewrite Pbb.
    apply App_typed with (τ1 := initial_type τi τf A).
    apply up_type_three.
    assert (HHH : ((final_type τi τf A) = (final_type τi τf A).[TRec (final_type τi τf A)/])).
    admit.
    rewrite -HHH.
    admit.
    admit.
    admit.
  - admit.
  - admit.
  - admit.
  - admit.

  - (** var var *)
    simpl. apply Var_typed.
    (** spec here!!! *)
    admit.


  - apply extract_typed.
  - apply embed_typed.
  - apply factorization_up_typed with (τG := τG); (try done || by eapply get_shape_is_ground).
    by apply IHP.
  - apply factorization_down_typed with (τG := τG); (try done || by eapply get_shape_is_ground).
    by apply IHP.
  - apply identity_typed.
  - apply identity_typed.
  - apply between_TSum_typed.
    by apply IHP1.
    by apply IHP2.
  - apply between_TProd_typed.
    by apply IHP1.
    by apply IHP2.
  - apply between_TArrow_typed.
    by apply IHP1.
    by apply IHP2.
  - simpl. apply Lam_typed.
    apply App_typed with (τ1 := TRec << τi >>).
    apply App_typed with (τ1 := ((TRec << τi >> → TRec << τf >>) → (TRec << τi >> → TRec << τf >>))).
    apply Fix_typed. admit.
    apply Lam_typed. apply Lam_typed. apply Fold_typed.




Fixpoint 𝓕 (A : list Assumption) (Σ : list nat) (τi τf : cast_calculus.types.type) (P : A ⊢ τi ~ τf) : expr :=
