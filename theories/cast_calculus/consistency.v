From Autosubst Require Export Autosubst.
From fae_gtlc_mu.cast_calculus Require Export types types_lemmas.
From fae_gtlc_mu.cast_calculus Require Import types_notations.
From fae_gtlc_mu Require Import prelude.

Inductive consistency_open : type -> type -> Type :=
| GenSymUnit :
    consistency_open TUnit TUnit
| GenSymUnknownL τ :
    consistency_open TUnknown τ
| GenSymUnknownR τ :
    consistency_open τ TUnknown
| GenSymSum
    (τ1 τ1' τ2 τ2' : type)
    (s1 : consistency_open τ1 τ1')
    (s2 : consistency_open τ2 τ2')
  : consistency_open (τ1 + τ2)%types (τ1' + τ2')%types
| GenSymProd
    (τ1 τ1' τ2 τ2' : type)
    (s1 : consistency_open τ1 τ1')
    (s2 : consistency_open τ2 τ2')
  : consistency_open (τ1 × τ2)%types (τ1' × τ2')%types
| GenSymArrow τ1 τ1' τ2 τ2'
    (s1 : consistency_open τ1 τ1')
    (s2 : consistency_open τ2 τ2')
  : consistency_open (TArrow τ1 τ2) (TArrow τ1' τ2')
| GenSymVar i :
    consistency_open (TVar i) (TVar i)
| GenSymRec τ τ' (P : consistency_open τ τ') :
    consistency_open (TRec τ) (TRec τ').

Definition consistency τ (pτ : Closed τ) τ' (pτ' : Closed τ') : Type := consistency_open τ τ'.
