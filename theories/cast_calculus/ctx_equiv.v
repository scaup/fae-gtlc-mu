From fae_gtlc_mu.cast_calculus Require Import lang typing contexts.

Definition ctx_equiv (Γ : list type)
    (e e' : expr) (τ : type) := Γ ⊢ₜ e : τ ∧ Γ ⊢ₜ e' : τ ∧
  ∀ K, typed_ctx K Γ τ [] TUnit →
  (Halts (fill_ctx K e) <-> Halts (fill_ctx K e')).
Notation "Γ ⊨ e '=ctx-grad=' e' : τ" :=
  (ctx_equiv Γ e e' τ) (at level 74, e, e', τ at next level).
