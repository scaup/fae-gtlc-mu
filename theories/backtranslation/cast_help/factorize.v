From fae_gtlc_mu.cast_calculus Require Export types.
From fae_gtlc_mu.stlc_mu Require Export typing lang lib.fix.
From fae_gtlc_mu.backtranslation.cast_help Require Export universe embed extract.

(** Trivial stuff *)

Definition identity : val :=
  LamV (Var 0).

Lemma identity_typed Γ τ (pτ : TClosed τ) : Γ ⊢ₛ identity : (TArrow τ τ).
Proof.
  intros.
  eapply Lam_typed; auto. by apply Var_typed.
Qed.

(** Factorisations *)

Definition factorization (f g : expr) : val :=
  LamV (
      g.[ren (+1)] (f.[ren (+1)] (Var 0))
    ).

Lemma factorization_subst_rewrite (f g : expr) σ : (# (factorization f g)).[σ] = factorization f.[σ] g.[σ].
Proof. by asimpl. Qed.

Lemma factorization_typed Γ {f g : expr} τ1 τ2 τ3
      (df : Γ ⊢ₛ f : TArrow τ1 τ2)
      (dg : Γ ⊢ₛ g : TArrow τ2 τ3) :
  Γ ⊢ₛ factorization f g : TArrow τ1 τ3.
Proof.
  apply Lam_typed; auto.
  apply (TArrow_closed1 (typed_closed df)).
  apply App_typed with (τ1 := τ2).
  apply up_type_one. apply dg.
  apply App_typed with (τ1 := τ1).
  apply up_type_one. apply df.
  apply Var_typed; auto.
  apply (TArrow_closed1 (typed_closed df)).
Qed.
