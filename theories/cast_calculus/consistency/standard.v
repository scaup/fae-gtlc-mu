From Autosubst Require Export Autosubst.
From fae_gtlc_mu Require Import prelude cast_calculus.types.
Require Coq.Logic.JMeq.

Reserved Notation "n |> τ ~ τ'" (at level 4, τ, τ' at next level).
Inductive cons_stand : nat -> type -> type -> Type :=
| GenSymUnit n : cons_stand n TUnit TUnit
| GenSymUnknownL n (τ : type) : (UB n τ) -> cons_stand n ⋆ τ
| GenSymUnknownR n (τ : type) : (UB n τ) -> cons_stand n τ ⋆
| GenSymSum n
    (τ1 τ1' τ2 τ2' : type)
    (s1 : cons_stand n τ1 τ1')
    (s2 : cons_stand n τ2 τ2')
  : cons_stand n (τ1 + τ2)%type (τ1' + τ2')%type
| GenSymProd n
    (τ1 τ1' τ2 τ2' : type)
    (s1 : cons_stand n τ1 τ1')
    (s2 : cons_stand n τ2 τ2')
  : cons_stand n (τ1 × τ2) (τ1' × τ2')
| GenSymArrow n
    (τ1 τ1' τ2 τ2' : type)
    (s1 : cons_stand n τ1 τ1')
    (s2 : cons_stand n τ2 τ2')
  : cons_stand n (TArrow τ1 τ2) (TArrow τ1' τ2')
| GenSymVar n (i : nat) :
    i < n ->
    cons_stand n (TVar i) (TVar i)
| GenSymRec n (τ τ' : type) (P : cons_stand (S n) τ τ') :
    cons_stand n (TRec τ) (TRec τ')
where "n |> τ ~ τ'" := (cons_stand n τ τ').
