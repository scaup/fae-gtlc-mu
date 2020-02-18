From Autosubst Require Export Autosubst.
From fae_gtlc_mu.stlc_mu Require Export typing.
From fae_gtlc_mu.backtranslation Require Export types cast_help.universe.
From fae_gtlc_mu.cast_calculus Require Export types consistency.structural.assumption consistency.structural.definition.
From fae_gtlc_mu Require Import prelude.

(* A lot of the properties will depend upon which forms A can take as a list of assumptions *as part of a derivation*... *)
(* Either make these properties intrinsic or specify the properties later extrinsically... *)

Definition assumptions_to_gradual_context (A : list Assumption) : list cast_calculus.types.type.
  (* goes through the list performs the substitutions throughout, prepending TRec, making them all closed recursive types *)
Admitted.

Definition assumptions_to_static_context (A : list Assumption) : list stlc_mu.typing.type.
  (* does back-translation afterwards *)
Admitted.

Lemma assumptions_to_gradual_context_is_closed (A : list Assumption) :
  ForallT Is_Closed (assumptions_to_gradual_context A).
  (* proof of the latter; we need to know though that A comes from a derivation (either intrinsically or extrinsic with extra property) *)
Proof.
Admitted.

Definition back_type (A : list Assumption) (τ : cast_calculus.types.type) : stlc_mu.typing.type.
  (* τ will contain these type variables, performs the substitutions from (assumptions_to_context A), and then backtranslates it *)
Admitted.

Lemma back_type_is_closed (A : list Assumption) τ : stlc_mu.typing.Is_Closed (back_type A τ).
Admitted.

(* a type τ is a "body", if TRec τ is closed *)
Definition back_body (A : list Assumption) (τ : cast_calculus.types.type) : stlc_mu.typing.type.
Admitted.

Lemma back_body_type_checks_out (A : list Assumption) (τ : cast_calculus.types.type) :
  back_type A (TRec τ) = stlc_mu.typing.TRec (back_body A τ).
Admitted.

Lemma TRec_back_body_is_closed (A : list Assumption) (τ : cast_calculus.types.type) :
  stlc_mu.typing.Is_Closed (stlc_mu.typing.TRec (back_body A τ)).
Admitted.

(* extra limitation required on A, τ1 and τ2 *)
Lemma back_type_TSum (A : list Assumption) (τ1 τ2 : cast_calculus.types.type) :
  back_type A (TSum τ1 τ2) = stlc_mu.typing.TSum (back_type A τ1) (back_type A τ2).
  (* proof should be easy; substitutions and def of back-translation go through TSum *)
Admitted.

(* extra limitation required on A, τ1 and τ2 *)
Lemma back_type_TProd (A : list Assumption) (τ1 τ2 : cast_calculus.types.type) :
  back_type A (TProd τ1 τ2) = stlc_mu.typing.TProd (back_type A τ1) (back_type A τ2).
Admitted.

(* extra limitation required on A, τ1 and τ2 *)
Lemma back_type_TArrow (A : list Assumption) (τ1 τ2 : cast_calculus.types.type) :
  back_type A (TArrow τ1 τ2) = stlc_mu.typing.TArrow (back_type A τ1) (back_type A τ2).
Admitted.

Lemma back_type_TRec (A : list Assumption) (τb : cast_calculus.types.type) :
  back_type A (TRec τb) = stlc_mu.typing.TRec (back_body A τb).
Admitted.

Lemma back_type_unfolded_l (A : list Assumption) (F : XUnfolding) (τbl τbr : cast_calculus.types.type) (Pl : not_star τbl) (Pr : not_star τbr) :
  back_type (NoStars F τbl τbr Pl Pr :: A) τbl = (back_body A τbl).[back_type A τbl/].
Admitted.

Lemma back_type_unfolded_r (A : list Assumption) (F : XUnfolding) (τbl τbr : cast_calculus.types.type) (Pl : not_star τbl) (Pr : not_star τbr) :
  back_type (NoStars F τbl τbr Pl Pr :: A) τbr = (back_body A τbr).[back_type A τbr/].
Admitted.

Lemma back_star_type {A : list Assumption} :
  back_type A ⋆ = Universe.
Admitted.

Lemma back_ground_type {A : list Assumption} (τ : cast_calculus.types.type) (G : Ground τ) :
  back_type A τ = <<τ>>.
Admitted.
