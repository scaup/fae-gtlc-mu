From Autosubst Require Export Autosubst.
From fae_gtlc_mu.cast_calculus Require Export types.
(* From fae_gtlc_mu.cast_calculus.consistency.structural Require Export assumption. *)
From fae_gtlc_mu Require Import prelude.
Require Coq.Logic.JMeq.

Reserved Notation "A ⊢ τ ~ τ'" (at level 4, τ, τ' at next level).
Inductive cons_struct (A : list (type * type)) : type -> type -> Type :=
  (** ground and star *)
  (* downcasting from star to ground *)
  | consStarTGround τG
      (G : Ground τG) :
      A ⊢ ⋆ ~ τG
  (* upcasting from ground to star *)
  | consTGroundStar τG
      (G : Ground τG) :
      A ⊢ τG ~ ⋆
  (** factorization through ground types *)
  | consTauStar τ τG
      (pUBτ : UB (length A) τ)
      (pτnG : (Ground τ -> False))
      (pτnStar : not (τ = ⋆))
      (pτSτG : (get_shape τ = Some τG))
      (pτConsτG : A ⊢ τ ~ τG) :
      A ⊢ τ ~ ⋆
  | consStarTau τ τG
      (pUBτ : UB (length A) τ)
      (pτnG : (Ground τ -> False))
      (pτnStar : not (τ = ⋆))
      (pτSτG : (get_shape τ = Some τG))
      (pτGConsτ : A ⊢ τG ~ τ) :
      A ⊢ ⋆ ~ τ
  (** identiy casts between Base and ⋆ *)
  | consBaseBase :
      A ⊢ TUnit ~ TUnit
  | consStarStar :
      A ⊢ ⋆ ~ ⋆
  (** between types of same structure *)
  (* between + types *)
  | consTSumTSum τ1 τ1' τ2 τ2'
      (pCons1 : A ⊢ τ1 ~ τ1')
      (pCons2 : A ⊢ τ2 ~ τ2') :
      A ⊢ (τ1 + τ2)%type ~ (τ1' + τ2')%type
  (* between × types *)
  | consTProdTProd τ1 τ1' τ2 τ2'
      (pCons1 : A ⊢ τ1 ~ τ1')
      (pCons2 : A ⊢ τ2 ~ τ2') :
      A ⊢ (τ1 × τ2) ~ (τ1' × τ2')
  (* between → types *)
  | consTArrowTArrow τ1 τ2 τ3 τ4
      (pCons31 : A ⊢ τ3 ~ τ1)
      (pCons24 : A ⊢ τ2 ~ τ4) :
      A ⊢ (TArrow τ1 τ2) ~ (TArrow τ3 τ4)
  (** exposing recursive calls *)
  | consTRecTRecExposeCall τl τr
      (pμτlμτrnotA : (TRec τl, TRec τr) ∉ A)
      (pUnfτlUnfτr : ((TRec τl, TRec τr) :: A) ⊢ τl.[TRec τl/] ~ τr.[TRec τr/]) :
      A ⊢ (TRec τl) ~ (TRec τr)
  (** using recursive calls *)
  | consTRecTRecUseCall τl τr i
      (pμτlμtrinA : A !! i = Some (TRec τl, TRec τr)) :
      A ⊢ (TRec τl) ~ (TRec τr)
where "A ⊢ τ ~ τ'" := (cons_struct A τ τ').

(** Notes *) (*
In the end, we are only concerned with [] ⊢ τ ~ τ' (τ and τ' closed).
We need to consider derivation trees for this however (we are defining the backtranslation by induction on this relation)..

The assumptions, (A : list Assumption), in this tree will satisfy very particular properties however.
Every type will be "well-bounded"; that is, we will have UBA A.

Given a derivation A ⊢ τl ~ τr as a subderivation of [] ⊢ τ ~ τ', we will also have that τ and τ' satisfy UB (length A).

These properties do not follow for an arbitrary derivation A ⊢ τ1 ~ τ2; we need to impose them explicitly (using UBA and UB 0).

Maybe later, it'll be more practical to make this properties intrinsic to the inductive type instead of carrying them around with us the whole time...? *)
