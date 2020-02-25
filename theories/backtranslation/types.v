From fae_gtlc_mu Require Import cast_calculus.types stlc_mu.typing backtranslation.cast_help.universe.

Reserved Notation "<< τ >>" (at level 4, τ at next level).
Fixpoint backtranslate_type (τ : cast_calculus.types.type) : type :=
  match τ with
  | cast_calculus.types.TUnit => TUnit
  | cast_calculus.types.TProd τ1 τ2 => TProd <<τ1>> <<τ2>>
  | cast_calculus.types.TSum τ1 τ2 => TSum <<τ1>> <<τ2>>
  | cast_calculus.types.TArrow τ1 τ2 => TArrow <<τ1>> <<τ2>>
  | cast_calculus.types.TRec τ => TRec <<τ>>
  | cast_calculus.types.TVar x => TVar x
  | cast_calculus.types.TUnknown => Universe
  end where "<< e >>" := (backtranslate_type e).

Lemma unfolding_backtranslation_commutes (τ : cast_calculus.types.type) :
  << (cast_calculus.types.unfoldish τ) >> = stlc_mu.typing.unfoldish << τ >>.
Proof.
Admitted.
