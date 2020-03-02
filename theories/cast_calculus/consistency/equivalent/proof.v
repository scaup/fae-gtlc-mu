From Autosubst Require Export Autosubst.
From fae_gtlc_mu Require Import prelude.
From fae_gtlc_mu.cast_calculus Require Import types.
From fae_gtlc_mu.cast_calculus.consistency Require Import standard structural.definition equivalent.symmetric.

Lemma standard_implies_structural_consistency (τ τ' : type) (Pc : cons_stand 0 τ τ') : [] ⊢ τ ~ τ'.
Admitted.
