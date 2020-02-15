From fae_gtlc_mu.cast_calculus Require Export types consistency.structural.
From fae_gtlc_mu.stlc_mu Require Export typing lang lib.fix lib.universe.
From fae_gtlc_mu.backtranslation Require Export types.

(** Embeddings *)

Definition embed_TUnit : expr :=
  Lam (Fold (InjL (InjL (InjL (InjL (Var 0)))))).

Lemma embed_TUnit_typed Γ :
  Γ ⊢ₛ embed_TUnit : (TUnit → Universe).
Proof.
  apply Lam_typed, Fold_typed.
  repeat apply InjL_typed.
  by apply Var_typed.
Qed.

Definition embed_Ground_TSum : expr :=
  Lam (Fold ((InjL (InjL (InjL (InjR (Var 0))))))).

Definition embed_Ground_TSum_typed Γ :
  Γ ⊢ₛ embed_Ground_TSum : ((Universe + Universe) → Universe)%type.
Proof.
  apply Lam_typed.
  apply Fold_typed.
  repeat apply InjL_typed. apply InjR_typed.
  by apply Var_typed.
Qed.

Definition embed_Ground_TProd : expr :=
  Lam (Fold (InjL (InjL (InjR (Var 0))))).

Definition embed_Ground_TProd_typed Γ :
  Γ ⊢ₛ embed_Ground_TProd : ((Universe × Universe) → Universe).
Proof.
  apply Lam_typed, Fold_typed.
  repeat apply InjL_typed. asimpl. repeat apply InjR_typed.
  by apply Var_typed.
Qed.

Definition embed_Ground_TArrow : expr :=
  Lam (Fold (InjL (InjR (Var 0)))).

Definition embed_Ground_TArrow_typed Γ :
  Γ ⊢ₛ embed_Ground_TArrow : ((Universe → Universe) → Universe).
Proof.
  apply Lam_typed, Fold_typed.
  repeat apply InjL_typed. asimpl. repeat apply InjR_typed.
  by apply Var_typed.
Qed.

(* Takes something of μ.Universe, unfolds it so it is in Universe, and then puts in the last branch of the universe *)
Definition embed_Ground_TRec : expr :=
  Lam (Fold (InjR (Unfold (Var 0)))).

Definition embed_Ground_TRec_typed Γ :
  Γ ⊢ₛ embed_Ground_TRec : (TRec Universe → Universe).
Proof.
  apply Lam_typed. apply Fold_typed.
  apply InjR_typed.
  asimpl.
  apply Unfold_typed_help; first by trivial.
  by apply Var_typed.
Qed.

Definition embed (τ : cast_calculus.types.type) (G : Ground τ) : expr :=
  match G with
  | Ground_TUnit => embed_TUnit
  | Ground_TProd => embed_Ground_TProd
  | Ground_TSum => embed_Ground_TSum
  | Ground_TArrow => embed_Ground_TArrow
  | Ground_TRec => embed_Ground_TRec
  end.

Lemma embed_typed {τG : cast_calculus.types.type} {G : Ground τG} Γ :
  Γ ⊢ₛ (embed τG G) : (<<τG>> → Universe).
Proof.
  destruct G.
    + apply embed_TUnit_typed.
    + apply embed_Ground_TProd_typed.
    + apply embed_Ground_TSum_typed.
    + apply embed_Ground_TArrow_typed.
    + apply embed_Ground_TRec_typed.
Qed.
