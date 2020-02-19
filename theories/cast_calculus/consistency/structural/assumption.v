From Autosubst Require Export Autosubst.
From fae_gtlc_mu.cast_calculus Require Export types.
From fae_gtlc_mu Require Import prelude.
Require Coq.Logic.JMeq.

(* Inductive XUnfolding : Type := Done | NotYet. *)

Definition not_star (τ : type) : Type := (not (τ = ⋆)).

Inductive XUnfolding : Type := NotYet | ForStarOnLeft | ForStarOnRight.

Inductive Assumption : Type :=
  | NoStars (F : XUnfolding) (τl τr : type) (Pl : not_star τl) (Pr : not_star τr)
  | StarOnLeft (τr : type)
  | StarOnRight (τl : type).

(*
Why separate constructors?
No notion of unfolding needed in StarOnLeft or StarOnRight
 *)
