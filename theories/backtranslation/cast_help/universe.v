From fae_gtlc_mu.stlc_mu Require Import types types_notations.
Require Import fae_gtlc_mu.prelude.

(* This file defines the static type duped Universe (eq. 1 in paper) into which values of the unknown type will be backtranslated. *)

Definition Universe_body : type :=
  (
    TUnit +
    (TVar 0 + TVar 0) +
    (TVar 0 × TVar 0) +
    (TArrow (TVar 0) (TVar 0)) +
    (TVar 0)
  )%types.

Definition Universe : type :=
  TRec Universe_body.

Lemma Universe_closed : Closed Universe.
Proof. intro σ. by asimpl. Qed.
