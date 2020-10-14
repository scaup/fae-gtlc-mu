From fae_gtlc_mu.stlc_mu Require Import types types_notations.
Require Import fae_gtlc_mu.prelude.

Definition Universe_body : type :=
  (
    TUnit +
    (TVar 0 + TVar 0) +
    (TVar 0 × TVar 0) +
    (TArrow (TVar 0) (TVar 0)) +
    (TVar 0)
  )%types.

(* + is left associative; (a + b + c) = ((a + b) + c) *)

Definition Universe : type :=
  TRec Universe_body.

Definition Universe_unfolded : type :=
  Universe_body.[Universe/]%types.

Lemma Universe_closed : Closed Universe.
Proof. intro σ. by asimpl. Qed.
