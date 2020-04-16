From iris Require Import base.
From stdpp Require Import base list.
From Autosubst Require Export Autosubst.
Require Export Utf8_core.
From fae_gtlc_mu.equivalence Require Import types.

Fixpoint closures (τ : type) : list type :=
  match τ with
  | TUnit => []
  | TArrow τ1 τ2 => closures τ1 ++ closures τ2
  | TRec τb => TRec τb :: map (fun x => x.[TRec τb/]) (closures τb)
  | TVar x => []
  | TUnknown => []
  end.

Lemma closures_unfold_subset τb : closures τb.[TRec τb/] ⊆ closures (TRec τb).
Proof.
Admitted.
