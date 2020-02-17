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
  (** exposing recursive calls *)
  (* between μ types; we always *expose* a recursive call here *)
  | consTRecTRecNoStars τl τr (Pl : not_star τl) (Pr : not_star τr) :
      (NoStars NotYet τl τr Pl Pr :: A) ⊢ τl ~ τr -> (* we add the assumption to our list (the two type bodies) *)
      (* Sometimes, this recursive call we not be useful though (e.g. μ.(TUnit + N × 0) ~ μ.(TUnit + N × ⋆)) *)
      (* In these cases, we need to expose an eXtra recursive call. *)
      (* See XUnfolding and consTVarStar and consStarTVar *)
      A ⊢ (TRec τl) ~ (TRec τr)
  | consTRecTRecStarOnLeft τr :
      (StarOnLeft τr :: A) ⊢ ⋆ ~ τr -> (* we add the assumption to our list *)
      (* We will always be able to use the recursive call *)
      A ⊢ (TRec ⋆) ~ (TRec τr)
  | consTRecTRecStarOnRight τl :
      (StarOnRight τl :: A) ⊢ τl ~ ⋆ -> (* we add the assumption to our list *)
      (* We will always be able to use the recursive call *)
      A ⊢ (TRec τl) ~ (TRec ⋆)
  (* exposing new recursive call because previous one was not usable *)
  | consTVarStar i τl τr Pl Pr :
      (A !! i) = Some (NoStars NotYet τl τr Pl Pr) ->
      (StarOnRight τl :: update A i (NoStars Done τl τr Pl Pr)) ⊢ τl ~ ⋆ ->
      A ⊢ (TVar i) ~ (TRec ⋆)
  | consStarTVar i τl τr Pl Pr :
      (A !! i) = Some (NoStars NotYet τl τr Pl Pr) ->
      (StarOnLeft τr :: update A i (NoStars Done τl τr Pl Pr)) ⊢ ⋆ ~ τr ->
      A ⊢ (TRec ⋆) ~ (TVar i)
  (** using previously exposed recursive calls *)
  (* *using* previously exposed recursion ; two variables *)
  | consTVars i τl τr Pl Pr :
      (A !! i) = Some (NoStars NotYet τl τr Pl Pr) -> (* we need this specific information when proving well-typedness !! *)
      A ⊢ (TVar i) ~ (TVar i)
  (* using recurion; one variable, one star *)
  | consTVarStarUse i τl :
      (A !! i) = Some (StarOnRight τl) ->
      A ⊢ (TVar i) ~ (TRec ⋆)
  | consStarTVarUse i τr :
      (A !! i) = Some (StarOnLeft τr) ->
      A ⊢ (TRec ⋆) ~ (TVar i)
where "A ⊢ τ ~ τ'" := (cons_struct A τ τ').

(* UBA A implies that A is appropriately bounded *)
Inductive UBA : list Assumption -> Type :=
  | emptyUBA :
      UBA []
  | consUBANostars A F τl τr Pl Pr (pUBl : UB (S (length A)) τl) (pUBr : UB (S (length A)) τr) (pUBA : UBA A) :
      UBA (NoStars F τl τr Pl Pr :: A)
  | consUBAStarOnLeft A τl (pUBl : UB (S (length A)) τl) (pUBA : UBA A) :
      UBA (StarOnLeft τl :: A)
  | consUBAStarOnRight A τr (pUBr : UB (S (length A)) τr) (pUBA : UBA A) :
      UBA (StarOnLeft τr :: A).

(** Notes *) (*
In the end, we are only concerned with [] ⊢ τ ~ τ' (τ and τ' closed).
We need to consider derivation trees for this however (we are defining the backtranslation by induction on this relation)..

The assumptions, (A : list Assumption), in this tree will satisfy very particular properties however.
Every type will be "well-bounded"; that is, we will have UBA A.

Given a derivation A ⊢ τl ~ τr as a subderivation of [] ⊢ τ ~ τ', we will also have that τ and τ' satisfy UB (length A).

These properties do not follow for an arbitrary derivation A ⊢ τ1 ~ τ2; we need to impose them explicitly (using UBA and UB 0).

Maybe later, it'll be more practical to make this properties intrinsic to the inductive type instead of carrying them around with us the whole time...? *)
