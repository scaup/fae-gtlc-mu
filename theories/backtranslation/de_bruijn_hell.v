From Autosubst Require Export Autosubst.
From fae_gtlc_mu.stlc_mu Require Export typing.
From fae_gtlc_mu.backtranslation Require Export types cast_help.universe.
From fae_gtlc_mu.cast_calculus Require Export types consistency.structural.assumption consistency.structural.definition.
From fae_gtlc_mu Require Import prelude.

Inductive Side : Type := Left | Right.

Definition reverse (s : Side) :=
  match s with
  | Left => Right
  | Right => Left
  end.

Definition assumption_to_gradual_pair (a : Assumption) : cast_calculus.types.type * cast_calculus.types.type :=
  match a with
  | NoStars τl τr Pl Pr => (TRec τl, TRec τr)
  | StarOnLeft τr => (TRec ⋆, TRec τr)
  | StarOnRight τl => (TRec τl, TRec τl)
  end.



(* A lot of the properties will depend upon which forms A can take as a list of assumptions *as part of a derivation*... *)
(* Either make these properties intrinsic or specify the properties later extrinsically... *)

Definition assumptions_to_gradual_context (A : list Assumption) : list cast_calculus.types.type.
  (* goes through the list performs the substitutions throughout, prepending TRec, making them all closed recursive types *)
Admitted.

Definition assumptions_to_static_context (A : list Assumption) : list stlc_mu.typing.type.
  (* does back-translation afterwards *)
Admitted.

Definition assumptions_to_static_pairs (A : list Assumption) : list stlc_mu.typing.type * list stlc_mu.typing.type.
  (* does back-translation afterwards *)
Admitted.

Lemma assumptions_to_gradual_context_is_closed (A : list Assumption) :
  ForallT Is_Closed (assumptions_to_gradual_context A).
  (* proof of the latter; we need to know though that A comes from a derivation (either intrinsically or extrinsic with extra property) *)
Proof.
Admitted.

Definition back_type (A : list Assumption) (τ : cast_calculus.types.type) (s : Side) : stlc_mu.typing.type.
  (* τ will contain these type variables, performs the substitutions from (assumptions_to_context A), and then backtranslates it *)
  (* when τ is an arrow type, we need to interchange the substitutions.. *)
Admitted.

Lemma back_type_is_closed (A : list Assumption) τ (s : Side) : stlc_mu.typing.Is_Closed (back_type A τ s).
Admitted.

(* a type τ is a "body", if TRec τ is closed *)
Definition back_body (A : list Assumption) (τ : cast_calculus.types.type) (s : Side) : stlc_mu.typing.type.
Admitted.

Lemma back_body_type_checks_out (A : list Assumption) (τ : cast_calculus.types.type) (s : Side) :
  back_type A (TRec τ) s = stlc_mu.typing.TRec (back_body A τ s).
Admitted.

Lemma TRec_back_body_is_closed (A : list Assumption) (τ : cast_calculus.types.type) (s : Side) :
  stlc_mu.typing.Is_Closed (stlc_mu.typing.TRec (back_body A τ s)).
Admitted.

(* extra limitation required on A, τ1 and τ2 *)
Lemma back_type_TSum (A : list Assumption) (τ1 τ2 : cast_calculus.types.type) (s : Side) :
  back_type A (TSum τ1 τ2) s = stlc_mu.typing.TSum (back_type A τ1 s) (back_type A τ2 s).
  (* proof should be easy; substitutions and def of back-translation go through TSum *)
Admitted.

(* extra limitation required on A, τ1 and τ2 *)
Lemma back_type_TProd (A : list Assumption) (τ1 τ2 : cast_calculus.types.type) (s : Side) :
  back_type A (TProd τ1 τ2) s = stlc_mu.typing.TProd (back_type A τ1 s) (back_type A τ2 s).
Admitted.

(* extra limitation required on A, τ1 and τ2 *)
Lemma back_type_TArrow (A : list Assumption) (τ1 τ2 : cast_calculus.types.type) (s : Side) :
  back_type A (TArrow τ1 τ2) s = stlc_mu.typing.TArrow (back_type A τ1 (reverse s)) (back_type A τ2 s).
Admitted.

Lemma back_type_TRec (A : list Assumption) (τb : cast_calculus.types.type) (s : Side) :
  back_type A (TRec τb) s = stlc_mu.typing.TRec (back_body A τb s).
Admitted.

Lemma back_type_unfolded_l (A : list Assumption) (τbl τbr : cast_calculus.types.type) (Pl : not_star τbl) (Pr : not_star τbr) :
  back_type (NoStars τbl τbr Pl Pr :: A) τbl Left = (back_body A τbl Left).[back_type A (TRec τbl) Left/].
Admitted.

Lemma back_type_unfolded_r (A : list Assumption) (τbl τbr : cast_calculus.types.type) (Pl : not_star τbl) (Pr : not_star τbr) :
  back_type (NoStars τbl τbr Pl Pr :: A) τbr Right = (back_body A τbr Right).[back_type A (TRec τbr) Right/].
Admitted.

Lemma back_star_type {A : list Assumption} (s : Side) :
  back_type A ⋆ s = Universe.
Admitted.

Lemma back_ground_type {A : list Assumption} (τ : cast_calculus.types.type) (G : Ground τ) (s : Side) :
  back_type A τ s = <<τ>>.
Admitted.

Lemma back_type_unfolded_l' (A : list Assumption) (τbl : cast_calculus.types.type) :
  back_type (StarOnRight τbl :: A) τbl Left = (back_body A τbl Left).[back_type A (TRec τbl) Left/].
Admitted.

Lemma back_type_unfolded_r' (A : list Assumption) (τbr : cast_calculus.types.type) :
  back_type (StarOnLeft τbr :: A) τbr Right = (back_body A τbr Right).[back_type A (TRec τbr) Right/].
Admitted.

Definition change_Xunfolding (A : list Assumption) {τl τr : cast_calculus.types.type} {pl : not_star τl} {pr : not_star τr} {i : nat} (eq : (A !! i) = Some (NoStars τl τr pl pr)) : list Assumption :=
  update A i (NoStars τl τr pl pr).

Lemma change_Xunfolding_same_context {A : list Assumption} {τl τr : cast_calculus.types.type} {pl : not_star τl} {pr : not_star τr} {i : nat} (eq : (A !! i) = Some (NoStars τl τr pl pr)) :
  assumptions_to_static_context (change_Xunfolding A eq) = assumptions_to_static_context A.
Admitted.

Lemma back_type_var_l {A : list Assumption} {τl τr : cast_calculus.types.type} {pl : not_star τl} {pr : not_star τr} {i : nat} (eq : (A !! i) = Some (NoStars τl τr pl pr)) :
  back_type A (TVar i) Left = back_type A (TRec τl) Left.
Admitted.

Lemma back_type_var_r {A : list Assumption} {τl τr : cast_calculus.types.type} {pl : not_star τl} {pr : not_star τr} {i : nat} (eq : (A !! i) = Some (NoStars τl τr pl pr)) :
  back_type A (TVar i) Right = back_type A (TRec τr) Right.
Admitted.
