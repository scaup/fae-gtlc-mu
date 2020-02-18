From fae_gtlc_mu.cast_calculus Require Export types consistency.structural.definition.
From fae_gtlc_mu.stlc_mu Require Export typing lang lib.fix.
From fae_gtlc_mu.backtranslation.cast_help Require Export universe embed extract between factorize.
From fae_gtlc_mu.backtranslation Require Export types de_bruijn_hell.

(** emulation of a cast between an arbitrary pair of consistent types *)
(* recursively defined on the alternative consistency relation *)

Fixpoint 𝓕 (A : list Assumption) (τi τf : cast_calculus.types.type) (P : A ⊢ τi ~ τf) : expr :=
  match P with
  | consStarTGround _ τ G => extract τ G
  | consTGroundStar _ τ G => embed τ G
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
  | consTRecTRecNoStars _ τi τf PτinS PτfnS Pτiτf =>
    between_TRec (𝓕 (NoStars NotYet τi τf PτinS PτfnS :: _) τi τf Pτiτf)
  | consTRecTRecStarOnLeft _ τr x => Unit
  | consTRecTRecStarOnRight _ τl x => Unit
  | consTVars _ i τl τr Pl Pr x => Unit
  | consTVarStar _ i τl τr Pl Pr x x0 => Unit
  | consStarTVar _ i τl τr Pl Pr x x0 => Unit
  | consTVarStarUse _ i τr x => Unit
  | consStarTVarUse _ i τl x => Unit
  end.

Lemma 𝓕_typed (A : list Assumption) (τi τf : cast_calculus.types.type) (P : A ⊢ τi ~ τf) :
  (assumptions_to_static_context A) ⊢ₛ (𝓕 A τi τf P) : ((back_type A τi) → (back_type A τf)).
(* From fae_gtlc_mu.cast_calculus Require Import types. (* make use of subs notation in gtlc *) *)
Proof.
  induction P; intros.
  - rewrite back_star_type back_ground_type.
    apply extract_typed.
    auto.
  - rewrite back_star_type back_ground_type.
    apply embed_typed.
    auto.
  - rewrite back_star_type.
    rewrite (back_ground_type τG) in IHP.
    apply factorization_up_typed with (τG := τG); try done.
    by eapply get_shape_is_ground.
  - rewrite back_star_type.
    rewrite (back_ground_type τG) in IHP.
    apply factorization_down_typed with (τG := τG). apply IHP.
      by eapply get_shape_is_ground.
  - apply identity_typed.
  - apply identity_typed.
  - repeat rewrite back_type_TSum.
    apply between_TSum_typed.
    by apply IHP1.
    by apply IHP2.
  - repeat rewrite back_type_TProd.
    apply between_TProd_typed.
    by apply IHP1.
    by apply IHP2.
  - repeat rewrite back_type_TArrow.
    apply between_TArrow_typed.
    by apply IHP1.
    by apply IHP2.
  - repeat rewrite back_type_TRec.
    rewrite back_type_unfolded_l back_type_unfolded_r in IHP.
    apply between_TRec_typed.
    apply TRec_back_body_is_closed.
    apply TRec_back_body_is_closed.
    assert (H : ((assumptions_to_static_context (NoStars NotYet τl τr Pl Pr :: A))) = (TRec ((back_body A τl) → TRec (back_body A τr)) :: assumptions_to_static_context A)).
    { admit. }
    apply IHP.
    rewrite H in IHP.

  - simpl. apply Lam_typed.
    apply App_typed with (τ1 := TRec << τi >>).
    apply App_typed with (τ1 := ((TRec << τi >> → TRec << τf >>) → (TRec << τi >> → TRec << τf >>))).
    apply Fix_typed. admit.
    apply Lam_typed. apply Lam_typed. apply Fold_typed.

