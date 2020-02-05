From fae_gtlc_mu.cast_calculus Require Import lang.
From fae_gtlc_mu.stlc_mu Require Import lang lib.universe lib.cast_emulations.
(* From fae_gtlc_mu Require Import stlc_mu.typing cast_calculus.typing. *)

(* expr defaults to stlc_mu.lang..., because it is loaded later *)

(** n keeps track under how many binders we have gone through *)
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
  | Cast e τi τf => match 
    (𝓕 τi τf ) <<e>>
  | Blame => Ω
  end where "<< e >>" := (backtranslate_expr e).
