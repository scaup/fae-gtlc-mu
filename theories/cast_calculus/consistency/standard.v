From Autosubst Require Export Autosubst.
From fae_gtlc_mu Require Import prelude cast_calculus.types.
Require Coq.Logic.JMeq.

Inductive cons_stand : type -> type -> Type :=
| GenSymUnit : cons_stand TUnit TUnit
| GenSymUnknownL (τ : type) : cons_stand ⋆ τ
| GenSymUnknownR (τ : type) : cons_stand τ ⋆
| GenSymSum
    (τ1 τ1' τ2 τ2' : type)
    (s1 : cons_stand τ1 τ1')
    (s2 : cons_stand τ2 τ2')
  : cons_stand (τ1 + τ2)%type (τ1' + τ2')%type
| GenSymProd
    (τ1 τ1' τ2 τ2' : type)
    (s1 : cons_stand τ1 τ1')
    (s2 : cons_stand τ2 τ2')
  : cons_stand (τ1 × τ2) (τ1' × τ2')
| GenSymArrow
    (τ1 τ1' τ2 τ2' : type)
    (s1 : cons_stand τ1 τ1')
    (s2 : cons_stand τ2 τ2')
  : cons_stand (TArrow τ1 τ2) (TArrow τ1' τ2')
| GenSymVar (i : nat) :
    cons_stand (TVar i) (TVar i)
| GenSymRec (τ τ' : type) (P : cons_stand τ τ') :
    cons_stand (TRec τ) (TRec τ').


Lemma cons_stand_dec τ1 τ2 : TDecision (cons_stand τ1 τ2).
Proof.
Admitted.
