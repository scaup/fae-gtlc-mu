From stdpp Require Import base list.
From Autosubst Require Export Autosubst.
Require Export Utf8_core.

From fae_gtlc_mu.equivalence Require Import types.

Inductive cons_struct_pre (A : list (type * type)) : type -> type -> Type :=
  (** ground and star *)
  (* downcasting from star to ground *)
  | consStarTGround τG
      (G : Ground τG) :
      cons_struct_pre A TUnknown τG
  (* upcasting from ground to star *)
  | consTGroundStar τG
      (G : Ground τG) :
      cons_struct_pre A τG TUnknown
  (** factorization through ground types, first direction *)
  | consTauGroundArrow (τ1 τ2 : type)
      (pτnG : τ1 ≠ TUnknown ∨ τ2 ≠ TUnknown)
      (pC1 : cons_struct_pre A TUnknown τ1)
      (pC2 : cons_struct_pre A τ2 TUnknown) :
      cons_struct_pre A (TArrow τ1 τ2) TUnknown
  | consTauGroundRecUseCall (τb : type) i
      (pτnG : τb ≠ TUnknown)
      (pμτlμtrinA : A !! i = Some (TRec τb, TRec TUnknown)) :
      cons_struct_pre A (TRec τb) TUnknown
  | consTauGroundRecExposeCall (τb : type)
      (pτnG : τb ≠ TUnknown)
      (pμτlμτrnotA : (TRec τb, TRec TUnknown) ∉ A)
      (pUnfτlUnfτr : cons_struct_pre ((TRec τb, TRec TUnknown) :: A) τb.[TRec τb/] TUnknown) :
      cons_struct_pre A (TRec τb) TUnknown
  (** factorization through ground types, second direction *)
  | consGroundArrowTau (τ1 τ2 : type)
      (pτnG : τ1 ≠ TUnknown ∨ τ2 ≠ TUnknown)
      (pC1 : cons_struct_pre A τ1 TUnknown)
      (pC2 : cons_struct_pre A TUnknown τ2) :
      cons_struct_pre A TUnknown (TArrow τ1 τ2)
  | consGroundRecTauUseCall (τb : type) i
      (pτnG : τb ≠ TUnknown)
      (pμτlμtrinA : A !! i = Some (TRec TUnknown, TRec τb)) :
      cons_struct_pre A TUnknown (TRec τb)
  | consGroundRecTauExposeCall (τb : type)
      (pτnG : τb ≠ TUnknown)
      (pμτlμτrnotA : (TRec TUnknown , TRec τb) ∉ A)
      (pUnfτlUnfτr : cons_struct_pre ((TRec TUnknown, TRec τb) :: A) TUnknown τb.[TRec τb/]) :
      cons_struct_pre A TUnknown (TRec τb)
  (** identiy casts between Base and TUnknown *)
  | consBaseBase :
      cons_struct_pre A TUnit TUnit
  | consStarStar :
      cons_struct_pre A TUnknown TUnknown
  (** between types of same structure *)
  | consTArrowTArrow τ1 τ1' τ2 τ2'
      (pCons31 : cons_struct_pre A τ1' τ1)
      (pCons24 : cons_struct_pre A τ2 τ2') :
      cons_struct_pre A (TArrow τ1 τ2) (TArrow τ1' τ2')
  (** exposing recursive calls *)
  | consTRecTRecExposeCall τl τr
      (pμτlμτrnotA : (TRec τl, TRec τr) ∉ A)
      (pUnfτlUnfτr : cons_struct_pre ((TRec τl, TRec τr) :: A) τl.[TRec τl/] τr.[TRec τr/]) :
      cons_struct_pre A (TRec τl) (TRec τr)
  (** using recursive calls *)
  | consTRecTRecUseCall τl τr i
      (pμτlμtrinA : A !! i = Some (TRec τl, TRec τr)) :
      cons_struct_pre A (TRec τl) (TRec τr).
