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
  (** exposing recursive calls *)
  | consTRecTRecNoStars _ τi τf PτinS PτfnS Pτiτf =>
    between_TRec (𝓕 (NoStars NotYet τi τf PτinS PτfnS :: _) τi τf Pτiτf)
  | consTRecTRecStarOnLeft _ τr x =>
    between_TRec (𝓕 (StarOnLeft τr :: _) ⋆ τr x)
  | consTRecTRecStarOnRight _ τl x =>
    between_TRec (𝓕 (StarOnRight τl :: _) τl ⋆ x)
  (* exposing new recursive call because previous one was not usable *)
  | consTVarStar _ i τl τr Pl Pr x x0 => Unit
  | consStarTVar _ i τl τr Pl Pr x x0 => Unit
  (** using previously exposed recursive calls *)
  | consTVars _ i τl τr Pl Pr x => Unit
  | consTVarStarUse _ i τr x => Unit
  | consStarTVarUse _ i τl x => Unit
  end.

Lemma 𝓕_typed (A : list Assumption) (τi τf : cast_calculus.types.type) (P : A ⊢ τi ~ τf) :
  (assumptions_to_static_context A) ⊢ₛ (𝓕 A τi τf P) : ((back_type A τi Left) → (back_type A τf Right)).
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
  - repeat rewrite back_ground_type; simpl.
    apply identity_typed.
    constructor. constructor.
  - repeat rewrite back_star_type; simpl.
    apply identity_typed.
  - repeat rewrite back_type_TSum.
    apply between_TSum_typed.
    by apply IHP1.
    by apply IHP2.
  - repeat rewrite back_type_TProd.
    apply between_TProd_typed.
    by apply IHP1.
    by apply IHP2.
  - repeat rewrite back_type_TArrow.
    simpl.
    apply between_TArrow_typed.
    by apply IHP1.
    by apply IHP2.
  - repeat rewrite back_type_TRec.
    rewrite back_type_unfolded_l back_type_unfolded_r in IHP.
    simpl.
    apply between_TRec_typed.
    apply TRec_back_body_is_closed.
    apply TRec_back_body_is_closed.
    assert (H : ((assumptions_to_static_context (NoStars NotYet τl τr Pl Pr :: A))) = (TArrow (TRec (back_body A τl Left)) (TRec (back_body A τr Right)) :: assumptions_to_static_context A)).
    { admit. }
    rewrite H in IHP.
    rewrite -{2}back_type_TRec.
    rewrite -{2}(back_type_TRec A τr).
    apply IHP.
  - rewrite back_ground_type; try by constructor. simpl.
    rewrite back_type_TRec.
    assert (H : ((assumptions_to_static_context (StarOnLeft τr :: A))) = (TArrow (TRec Universe) (TRec (back_body A τr Right)) :: assumptions_to_static_context A)).
    { admit. }
    apply between_TRec_typed. intro τ. by asimpl.
    apply TRec_back_body_is_closed.
    rewrite H in IHP.
    rewrite back_type_unfolded_r' in IHP.
    rewrite back_star_type in IHP.
    rewrite -{2}back_type_TRec.
    apply IHP.
  - rewrite (back_ground_type _ _ Right); try by constructor.
    rewrite (back_star_type Right) in IHP.
    simpl.
    assert (H : ((assumptions_to_static_context (StarOnRight τl :: A))) = (TArrow (TRec (back_body A τl Left)) (TRec Universe) :: assumptions_to_static_context A)).
    { admit. }
    rewrite H in IHP.
    rewrite (back_type_TRec _ _ Left).
    apply between_TRec_typed.
    apply TRec_back_body_is_closed.
    intro τ; by asimpl.
    rewrite back_type_unfolded_l' in IHP.
    rewrite -{2}back_type_TRec.
    apply IHP.
  - rewrite (back_ground_type _ _ Right); try by constructor. simpl.




    assert (H : ((assumptions_to_static_context (StarOnRight τl :: (update A i (NoStars Done τl τr Pl Pr))))) = (TArrow (TRec (back_body A τl Left)) (TRec Universe) :: assumptions_to_static_context A)).
    { admit. }
    repeat rewrite H in IHP.
    


