From Autosubst Require Export Autosubst.
From fae_gtlc_mu.cast_calculus Require Export types.
(* From fae_gtlc_mu.cast_calculus.consistency.structural Require Export assumption. *)
From fae_gtlc_mu Require Import prelude.
Require Coq.Logic.JMeq.

(** This has nothing to do with the proof;
just a test to see what the problem is with unfolding types... *)

Notation "⋆" := TUnknown : type_scope.
(** even this is really hard to prove :( *)
Infix "×" := TProd (at level 150) : type_scope.
Infix "+" := TSum.
Infix "→" := TArrow : type_scope.

Reserved Notation "A ⊢ τ " (at level 4, τ at next level).
Inductive unary (A : list type) : type -> Type :=
  | unary_unit :
      A ⊢  TUnit
  | unary_star :
      A ⊢ ⋆
  | unary_prod τ1 τ2 :
      A ⊢ τ1 -> A ⊢ τ2 ->
      A ⊢ (τ1 × τ2)
  | unary_sum τ1 τ2 :
      A ⊢ τ1 -> A ⊢ τ2 ->
      A ⊢ (τ1 + τ2)
  | unary_arrow τ1 τ2 :
      A ⊢ τ1 -> A ⊢ τ2 ->
      A ⊢ (τ1 → τ2)
  | unary_rec_in_assumptions τ :
      ((TRec τ) ∈ A) ->
      A ⊢ (TRec τ)
  | unary_rec_not_in_assumptions τ :
      (not ((TRec τ) ∈ A)) ->
      (TRec τ :: A) ⊢ τ.[TRec τ/] ->
      A ⊢ (TRec τ)
where "A ⊢ τ" := (unary A τ).

Lemma well_founded (τ : type) (pτclosed : UB 0 τ) : [] ⊢ τ.
Proof.
Admitted.
