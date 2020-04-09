From fae_gtlc_mu.cast_calculus Require Export types.
From fae_gtlc_mu.stlc_mu Require Export typing lang lib.fix.
From fae_gtlc_mu.backtranslation.cast_help Require Export universe embed extract.

(** Trivial stuff *)

Definition identity : expr :=
  Lam (Var 0).

Lemma identity_typed (τ : type) Γ : Γ ⊢ₛ identity : (TArrow τ τ).
Proof.
  intros.
  apply Lam_typed. by apply Var_typed.
Qed.

(** Factorisations *)

Definition factorization_up (f : expr) (τG : cast_calculus.types.type) (G : Ground τG) : expr :=
  Lam (
      embed τG G ((rename (+1) f) (Var 0))
    ).

Lemma factorization_up_subst_rewrite (f : expr) (τG : cast_calculus.types.type) (G : Ground τG) σ : (factorization_up f τG G).[σ] = factorization_up f.[σ] τG G.
Proof.
  rewrite /factorization_up.
  asimpl. by rewrite embed_no_subs.
Qed.

Lemma factorization_up_typed Γ {f : expr} (τ : type(* backtranslation of something that is not a ground type, nor star *)) (τG : cast_calculus.types.type) (G : Ground τG) (d : Γ ⊢ₛ f : (TArrow τ <<τG>>)) :
  Γ ⊢ₛ factorization_up f τG G : (TArrow τ Universe).
Proof.
  apply Lam_typed.
  apply App_typed with (τ1 := << τG >>).
  apply embed_typed.
  apply App_typed with (τ1 := τ ).
  apply up_type_one. apply d.
  by apply Var_typed.
Qed.

Definition factorization_down (f : expr) (τG : cast_calculus.types.type) (G : Ground τG) : expr :=
  Lam (
      (rename (+1) f) (extract τG G (Var 0))
    ).

Lemma factorization_down_subst_rewrite (f : expr) (τG : cast_calculus.types.type) (G : Ground τG) σ : (factorization_down f τG G).[σ] = factorization_down f.[σ] τG G.
Proof.
  rewrite /factorization_down.
  asimpl. by rewrite extract_no_subs.
Qed.

Lemma factorization_down_typed Γ {f : expr} (τ : type(* backtranslation of something that is not a ground type, nor star *)) (τG : cast_calculus.types.type) (G : Ground τG) (d : Γ ⊢ₛ f : (TArrow <<τG>> τ)) :
  Γ ⊢ₛ factorization_down f τG G : (TArrow Universe τ).
Proof.
  apply Lam_typed.
  apply App_typed with (τ1 := << τG >>).
  apply up_type_one. apply d.
  apply App_typed with (τ1 := Universe).
  apply extract_typed.
  by apply Var_typed.
Qed.
