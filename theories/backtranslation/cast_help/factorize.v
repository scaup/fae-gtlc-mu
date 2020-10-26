From fae_gtlc_mu.stlc_mu Require Import lang typing typing_lemmas types_notations.

(** Factorisations *)

Definition factorization (f g : expr) : val :=
  LamV (
      g.[ren (+1)] (f.[ren (+1)] (Var 0))
    ).

Lemma factorization_subst_rewrite (f g : expr) σ : (of_val (factorization f g)).[σ] = factorization f.[σ] g.[σ].
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
