From fae_gtlc_mu.cast_calculus Require Export types consistency.structural.definition.
From fae_gtlc_mu.stlc_mu Require Export typing lang lib.fix.
From fae_gtlc_mu.stlc_mu.lib Require Export universe embed extract.
From fae_gtlc_mu.backtranslation Require Export types.

(** Trivial stuff *)

Definition identity : expr :=
  Lam (Var 0).

Lemma identity_typed (τ : type) Γ : Γ ⊢ₛ identity : (τ → τ).
Proof.
  intros.
  apply Lam_typed. by apply Var_typed.
Qed.

(** Factorisations *)

Definition factorization_up (f : expr) (τG : cast_calculus.types.type) (G : Ground τG) : expr :=
  Lam (
      embed τG G ((rename (+1) f) (Var 0))
    ).

Lemma factorization_up_typed Γ {f : expr} (τ τG : cast_calculus.types.type) (G : Ground τG) (p1 : (Ground τ -> False)) (p2 : not (τ = ⋆)) (d : Γ ⊢ₛ f : (<<τ>> → <<τG>>)) :
  Γ ⊢ₛ factorization_up f τG G : (<<τ>> → Universe).
Proof.
  apply Lam_typed.
  apply App_typed with (τ1 := << τG >>).
  apply embed_typed.
  apply App_typed with (τ1 := << τ >>).
  apply up_type_one. apply d.
  by apply Var_typed.
Qed.

Definition factorization_down (f : expr) (τG : cast_calculus.types.type) (G : Ground τG) : expr :=
  Lam (
      (rename (+1) f) (extract τG G (Var 0))
    ).

Lemma factorization_down_typed Γ {f : expr} (τ τG : cast_calculus.types.type) (G : Ground τG) (p1 : notT (Ground τ)) (p2 : not (τ = ⋆)) (d : Γ ⊢ₛ f : (<<τG>> → <<τ>>)) :
  Γ ⊢ₛ factorization_down f τG G : (Universe → <<τ>>).
Proof.
  apply Lam_typed.
  apply App_typed with (τ1 := << τG >>).
  apply up_type_one. apply d.
  apply App_typed with (τ1 := Universe).
  apply extract_typed.
  by apply Var_typed.
Qed.
