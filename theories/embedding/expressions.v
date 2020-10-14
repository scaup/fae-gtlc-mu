From fae_gtlc_mu.stlc_mu Require lang.
From fae_gtlc_mu.cast_calculus Require Import lang.

Reserved Notation "[[ e ]]" (at level 4, e at next level).
Fixpoint embed_expr (e : stlc_mu.lang.expr) : expr :=
  match e with
  | stlc_mu.lang.Var x => Var x
  | stlc_mu.lang.Lam e => Lam [[ e ]]
  | stlc_mu.lang.App e1 e2 => App [[e1]] [[e2]]
  | stlc_mu.lang.Unit => Unit
  | stlc_mu.lang.Pair e1 e2 => Pair [[e1]] [[e2]]
  | stlc_mu.lang.Fst e => Fst [[e]]
  | stlc_mu.lang.Snd e => Snd [[e]]
  | stlc_mu.lang.InjL e => InjL [[e]]
  | stlc_mu.lang.InjR e => InjR [[e]]
  | stlc_mu.lang.Case e0 e1 e2 => Case [[e0]] [[e1]] [[e2]]
  | stlc_mu.lang.Fold e => Fold [[e]]
  | stlc_mu.lang.Unfold e => Unfold [[e]]
  end where "[[ e ]]" := (embed_expr e).
