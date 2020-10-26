From fae_gtlc_mu.stlc_mu Require Import lang typing typing_lemmas types_notations.

(* Identity functions *)

Definition identity : val :=
  LamV (Var 0).

Lemma identity_typed Γ (τ : type) (pτ : Closed τ) : Γ ⊢ₛ identity : (TArrow τ τ).
Proof.
  intros.
  eapply Lam_typed; auto. by apply Var_typed.
Qed.
