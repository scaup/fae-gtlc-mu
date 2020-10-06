From Autosubst Require Export Autosubst.
From fae_gtlc_mu.cast_calculus Require Export types.
From fae_gtlc_mu Require Import prelude.
Require Coq.Logic.JMeq.

Inductive alternative_consistency (A : list (type * type)) : type → type -> Type :=
  (** ground and star *)
  (* downcasting from star to ground *)
  | atomic_Unknown_Ground τG
      (G : Ground τG) :
      alternative_consistency A TUnknown τG
  (* upcasting from ground to star *)
  | atomic_Ground_Unknown τG
      (G : Ground τG) :
      alternative_consistency A τG TUnknown
  (** factorization through ground types, first direction *)
  | factorUp_Ground τ τG
      (pτnG : (Ground τ -> False))
      (pτnStar : not (τ = TUnknown))
      (pτSτG : (get_shape τ = Some τG))
      (pτConsτG : alternative_consistency A τ τG)
      (pτGConsStar : alternative_consistency A τG TUnknown)
    : alternative_consistency A τ TUnknown
  (** factorization through ground types, second direction *)
  | factorDown_Ground τ τG
      (pτnG : (Ground τ -> False))
      (pτnStar : not (τ = TUnknown))
      (pτSτG : (get_shape τ = Some τG))
      (pStarConsτG : alternative_consistency A TUnknown τG)
      (pτGConsτ : alternative_consistency A τG τ) :
      alternative_consistency A TUnknown τ
  (** identiy casts between Base and TUnknown *)
  | atomic_Base :
      alternative_consistency A TUnit TUnit
  | consStarStar :
      alternative_consistency A TUnknown TUnknown
  (** between types of same structure *)
  (* Sum *)
  | throughSum τ1 τ1' τ2 τ2'
      (pCons31 : alternative_consistency A τ1 τ1')
      (pCons24 : alternative_consistency A τ2 τ2') :
      alternative_consistency A (TSum τ1 τ2) (TSum τ1' τ2')
  (* Prod *)
  | throughProd τ1 τ1' τ2 τ2'
      (pCons31 : alternative_consistency A τ1 τ1')
      (pCons24 : alternative_consistency A τ2 τ2') :
      alternative_consistency A (TProd τ1 τ2) (TProd τ1' τ2')
  (* Arrow *)
  | throughArrow τ1 τ1' τ2 τ2'
      (pCons31 : alternative_consistency A τ1' τ1)
      (pCons24 : alternative_consistency A τ2 τ2') :
      alternative_consistency A (TArrow τ1 τ2) (TArrow τ1' τ2')
  (** exposing recursive calls *)
  | exposeRecursiveCAll τl τr
      (pμτlμτrnotA : (TRec τl, TRec τr) ∉ A)
      (pUnfτlUnfτr : alternative_consistency ((TRec τl, TRec τr) :: A) τl.[TRec τl/] τr.[TRec τr/]) :
      alternative_consistency A (TRec τl) (TRec τr)
  (** using recursive calls *)
  | atomic_UseRecursion τl τr i
      (pμτlμtrinA : A !! i = Some (TRec τl, TRec τr)) :
      alternative_consistency A (TRec τl) (TRec τr).

(* Notation "A ⊢ τ ~ τ'" := (alternative_consistency A τ τ') (at level 4, τ, τ' at next level). *)
