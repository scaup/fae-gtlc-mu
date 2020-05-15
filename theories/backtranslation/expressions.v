From fae_gtlc_mu.cast_calculus Require Import lang consistency.standard consistency.equivalence.proof.
From fae_gtlc_mu.stlc_mu Require Import lang.
From fae_gtlc_mu.backtranslation Require Import cast_help.general.
From fae_gtlc_mu.cast_calculus Require Import types.

Reserved Notation "<< e >>" (at level 4, e at next level).
Fixpoint backtranslate_expr (e : cast_calculus.lang.expr) : expr :=
  match e with
  | cast_calculus.lang.Var x => Var x
  | cast_calculus.lang.Lam e => Lam << e >>
  | cast_calculus.lang.App e1 e2 => App <<e1>> <<e2>>
  | cast_calculus.lang.Unit => Unit
  | cast_calculus.lang.Pair e1 e2 => Pair <<e1>> <<e2>>
  | cast_calculus.lang.Fst e => Fst <<e>>
  | cast_calculus.lang.Snd e => Snd <<e>>
  | cast_calculus.lang.InjL e => InjL <<e>>
  | cast_calculus.lang.InjR e => InjR <<e>>
  | cast_calculus.lang.Case e0 e1 e2 => Case <<e0>> <<e1>> <<e2>>
  | cast_calculus.lang.Fold e => Fold <<e>>
  | cast_calculus.lang.Unfold e => Unfold <<e>>
  | Cast e τi τf =>
    match (cons_stand_open_dec τi τf, decide (TClosed τi) , decide (TClosed τf)) with
    | (inleft pC , left pi, left pf) => (𝓕c (cons_co τi pi τf pf pC) []) <<e>>
    | _ => Unit
    end
  | CastError => Ω
  end where "<< e >>" := (backtranslate_expr e).
