From fae_gtlc_mu Require Export stlc_mu.typing.
From fae_gtlc_mu Require Export cast_calculus.types.

Reserved Notation "[| τ |]" (at level 4, τ at next level).
Fixpoint embed_type (τ : stlc_mu.types.type) : type :=
  match τ with
  | stlc_mu.types.TUnit => TUnit
  | stlc_mu.types.TProd τ1 τ2 => TProd [| τ1 |] [| τ2 |]
  | stlc_mu.types.TSum τ1 τ2 => TSum [| τ1 |] [| τ2 |]
  | stlc_mu.types.TArrow τ1 τ2 => TArrow [| τ1 |] [| τ2 |]
  | stlc_mu.types.TRec τb => TRec [| τb |]
  | stlc_mu.types.TVar x => TVar x
  end where "[| e |]" := (embed_type e).
