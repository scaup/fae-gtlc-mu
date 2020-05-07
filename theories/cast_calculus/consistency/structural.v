From Autosubst Require Export Autosubst.
From fae_gtlc_mu.cast_calculus Require Export types.
From fae_gtlc_mu Require Import prelude.
Require Coq.Logic.JMeq.

Inductive cons_struct (A : list (type * type)) : type → type -> Type :=
  (** ground and star *)
  (* downcasting from star to ground *)
  | consStarTGround τG
      (G : Ground τG) :
      cons_struct A TUnknown τG
  (* upcasting from ground to star *)
  | consTGroundStar τG
      (G : Ground τG) :
      cons_struct A τG TUnknown
  (** factorization through ground types, first direction *)
  | consTauStar τ τG
      (pτnG : (Ground τ -> False))
      (pτnStar : not (τ = TUnknown))
      (pτSτG : (get_shape τ = Some τG))
      (pτConsτG : cons_struct A τ τG)
      (pτGConsStar : cons_struct A τG TUnknown)
    : cons_struct A τ TUnknown
  (** factorization through ground types, second direction *)
  | consStarTau τ τG
      (pτnG : (Ground τ -> False))
      (pτnStar : not (τ = TUnknown))
      (pτSτG : (get_shape τ = Some τG))
      (pStarConsτG : cons_struct A TUnknown τG)
      (pτGConsτ : cons_struct A τG τ) :
      cons_struct A TUnknown τ
  (** identiy casts between Base and TUnknown *)
  | consBaseBase :
      cons_struct A TUnit TUnit
  | consStarStar :
      cons_struct A TUnknown TUnknown
  (** between types of same structure *)
  (* Sum *)
  | consTSumTSum τ1 τ1' τ2 τ2'
      (pCons31 : cons_struct A τ1 τ1')
      (pCons24 : cons_struct A τ2 τ2') :
      cons_struct A (TSum τ1 τ2) (TSum τ1' τ2')
  (* Prod *)
  | consTProdTProd τ1 τ1' τ2 τ2'
      (pCons31 : cons_struct A τ1 τ1')
      (pCons24 : cons_struct A τ2 τ2') :
      cons_struct A (TProd τ1 τ2) (TProd τ1' τ2')
  (* Arrow *)
  | consTArrowTArrow τ1 τ1' τ2 τ2'
      (pCons31 : cons_struct A τ1' τ1)
      (pCons24 : cons_struct A τ2 τ2') :
      cons_struct A (TArrow τ1 τ2) (TArrow τ1' τ2')
  (** exposing recursive calls *)
  | consTRecTRecExposeCall τl τr
      (pμτlμτrnotA : (TRec τl, TRec τr) ∉ A)
      (pUnfτlUnfτr : cons_struct ((TRec τl, TRec τr) :: A) τl.[TRec τl/] τr.[TRec τr/]) :
      cons_struct A (TRec τl) (TRec τr)
  (** using recursive calls *)
  | consTRecTRecUseCall τl τr i
      (pμτlμtrinA : A !! i = Some (TRec τl, TRec τr)) :
      cons_struct A (TRec τl) (TRec τr).

(* Notation "A ⊢ τ ~ τ'" := (cons_struct A τ τ') (at level 4, τ, τ' at next level). *)
