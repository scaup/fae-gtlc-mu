From fae_gtlc_mu.cast_calculus Require Export types.
From fae_gtlc_mu.backtranslation Require Import cast_help.universe.
From fae_gtlc_mu.stlc_mu Require Export types.
From fae_gtlc_mu Require Export prelude.

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
