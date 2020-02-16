From Autosubst Require Export Autosubst.
From fae_gtlc_mu.cast_calculus Require Export types.
From fae_gtlc_mu.cast_calculus.consistency.structural Require Export assumption.
From fae_gtlc_mu Require Import prelude.
Require Coq.Logic.JMeq.

Reserved Notation "A ⊢ τ ~ τ'" (at level 4, τ, τ' at next level).
Inductive cons_struct (A : list Assumption) : type -> type -> Type :=
  (** ground and star *)
  (* downcasting from star to ground *)
  | consStarTGround τ :
      Ground τ →
      A ⊢ ⋆ ~ τ
  (* upcasting from ground to star *)
  | consTGroundStar τ :
      Ground τ →
      A ⊢ τ ~ ⋆
  (** factorization through ground types *)
  | consTauStar τ τG :
      UB (length A) τ ->
      (Ground τ -> False) ->
      (not (τ = ⋆)) →
      (get_shape τ = Some τG) ->
      A ⊢ τ ~ τG ->
      A ⊢ τ ~ ⋆
  | consStarTau τ τG :
      UB (length A) τ ->
      (Ground τ -> False) ->
      (not (τ = ⋆)) →
      (get_shape τ = Some τG) ->
      A ⊢ τG ~ τ ->
      A ⊢ ⋆ ~ τ
  (** identiy casts between Base and ⋆ *)
  | consBaseBase :
      A ⊢ TUnit ~ TUnit
  | consStarStar :
      A ⊢ ⋆ ~ ⋆
  (** between types of same structure *)
  (* between + types *)
  | consTSumTSum τ1 τ1' τ2 τ2' :
      A ⊢ τ1 ~ τ1' ->
      A ⊢ τ2 ~ τ2' ->
      A ⊢ (τ1 + τ2)%type ~ (τ1' + τ2')%type
  (* between × types *)
  | consTProdTProd τ1 τ1' τ2 τ2' :
      A ⊢ τ1 ~ τ1' ->
      A ⊢ τ2 ~ τ2' ->
      A ⊢ (τ1 × τ2) ~ (τ1' × τ2')
  (* between → types *)
  | consTArrowTArrow τ1 τ2 τ3 τ4 :
      A ⊢ τ3 ~ τ1 ->
      A ⊢ τ2 ~ τ4 ->
      A ⊢ (TArrow τ1 τ2) ~ (TArrow τ3 τ4)
  (* between μ types; exposing recursive call *)
  | consTRecTRecNoStars τl τr (Pl : not_star τl) (Pr : not_star τr) :
      (NoStars NotYet τl τr Pl Pr :: A) ⊢ τl ~ τr -> (* in case next recursion does not work out, we can... *)
      A ⊢ (TRec τl) ~ (TRec τr)
  | consTRecTRecStarOnLeft τr :
      (StarOnLeft τr :: A) ⊢ ⋆ ~ τr -> (* recursive call way always be applicable.. *)
      A ⊢ (TRec ⋆) ~ (TRec τr)
  | consTRecTRecStarOnRight τl :
      (StarOnRight τl :: A) ⊢ τl ~ ⋆ -> (* recursive call way always be applicable.. *)
      A ⊢ (TRec τl) ~ (TRec ⋆)
  (* using recurion; two variables *)
  | consTVars i τl τr Pl Pr :
      (A !! i) = Some (NoStars NotYet τl τr Pl Pr) -> (* we need this specific information when proving well-typedness !! *)
      A ⊢ (TVar i) ~ (TVar i)
  (* exposing new recursive call because previous one was not usable *)
  | consTVarStar i τl τr Pl Pr :
      (A !! i) = Some (NoStars NotYet τl τr Pl Pr) ->
      (StarOnRight τl :: update A i (NoStars Done τl τr Pl Pr)) ⊢ τl ~ ⋆ ->
      A ⊢ (TVar i) ~ (TRec ⋆)
  | consStarTVar i τl τr Pl Pr :
      (A !! i) = Some (NoStars NotYet τl τr Pl Pr) ->
      (StarOnLeft τr :: update A i (NoStars Done τl τr Pl Pr)) ⊢ ⋆ ~ τr ->
      A ⊢ (TRec ⋆) ~ (TVar i)
  (* using recurion; one variable, one star *)
  | consTVarStarUse i τl :
      (A !! i) = Some (StarOnRight τl) ->
      A ⊢ (TVar i) ~ (TRec ⋆)
  | consStarTVarUse i τr :
      (A !! i) = Some (StarOnLeft τr) ->
      A ⊢ (TRec ⋆) ~ (TVar i)
where "A ⊢ τ ~ τ'" := (cons_struct A τ τ').
