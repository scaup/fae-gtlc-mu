From fae_gtlc_mu Require Import stlc_mu.typing.
From fae_gtlc_mu Require Import cast_calculus.types.

Reserved Notation "[| τ |]" (at level 4, τ at next level).
Fixpoint embed_type (τ : stlc_mu.typing.type) : type :=
  match τ with
  | typing.TUnit => TUnit
  | typing.TProd τ1 τ2 => TProd [| τ1 |] [| τ2 |]
  | typing.TSum τ1 τ2 => TSum [| τ1 |] [| τ2 |]
  | typing.TArrow τ1 τ2 => TArrow [| τ1 |] [| τ2 |]
  | typing.TRec τb => TRec [| τb |]
  | typing.TVar x => TVar x
  end where "[| e |]" := (embed_type e).

Lemma embed_through_unfold τ : [| τ.[typing.TRec τ/] |] = [| τ |].[TRec [| τ |]/].
Admitted.
