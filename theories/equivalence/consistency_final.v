From stdpp Require Import base list.
From Autosubst Require Export Autosubst.
Require Export Utf8_core.

From fae_gtlc_mu.equivalence Require Import types consistency_intermediate.

Definition get_shape (τ : type) : option type :=
  match τ with
  | TUnit => None
  | TArrow x x0 => Some (TArrow TUnknown TUnknown)
  | TRec τ => Some (TRec TUnknown)
  | TVar x => None
  | TUnknown => None
  end.

Lemma get_shape_is_ground {τ τG : type} : get_shape τ = Some τG -> Ground τG.
Proof.
  intro.
  destruct τ; simplify_eq; destruct τG; inversion H; constructor.
Qed.

Inductive cons_struct (A : list (type * type)) : type -> type -> Type :=
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

Lemma cons_struct_pre_cons_struct A τ τ' : cons_struct_pre A τ τ' → cons_struct A τ τ'.
Proof.
  intro p. induction p; try by constructor.
  - eapply consTauStar.
    admit. admit. by simpl.
    + by apply consTArrowTArrow.
    + apply consTGroundStar. constructor.
  - eapply consTauStar.
    admit. auto. by simpl.
    + by eapply consTRecTRecUseCall.
    + apply consTGroundStar. constructor.
  - eapply consTauStar.
    admit. auto. by simpl.
    + by eapply consTRecTRecExposeCall.
    + apply consTGroundStar. constructor.
  - eapply consStarTau.
    admit. admit. by simpl.
    + apply consStarTGround. constructor.
    + by apply consTArrowTArrow.
  - eapply consStarTau.
    admit. auto. by simpl.
    + apply consStarTGround. constructor.
    + by eapply consTRecTRecUseCall.
  - eapply consStarTau.
    admit. auto. by simpl.
    + apply consStarTGround. constructor.
    + by eapply consTRecTRecExposeCall.
  - apply consStarStar.
  - by eapply consTRecTRecUseCall.
Admitted.
