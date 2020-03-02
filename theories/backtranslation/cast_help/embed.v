From fae_gtlc_mu.cast_calculus Require Export types.
From fae_gtlc_mu.stlc_mu Require Export typing lang lib.fix.
From fae_gtlc_mu.backtranslation Require Export universe types.

(** Embeddings *)

Definition embedV_TUnit (v : val) : val :=
  (FoldV (InjLV (InjLV (InjLV (InjLV v))))).

Definition embed_TUnit : expr :=
  Lam (Fold (InjL (InjL (InjL (InjL (Var 0)))))).

Lemma embed_TUnit_typed Γ :
  Γ ⊢ₛ embed_TUnit : (TArrow TUnit Universe).
Proof.
  apply Lam_typed, Fold_typed.
  repeat apply InjL_typed.
  by apply Var_typed.
Qed.

Definition embedV_Ground_TSum (s : val) : val :=
  (FoldV ((InjLV (InjLV (InjLV (InjRV s)))))).

Definition embed_Ground_TSum : expr :=
  Lam (Fold ((InjL (InjL (InjL (InjR (Var 0))))))).

Definition embed_Ground_TSum_typed Γ :
  Γ ⊢ₛ embed_Ground_TSum : (TArrow (Universe + Universe) Universe)%type.
Proof.
  apply Lam_typed.
  apply Fold_typed.
  repeat apply InjL_typed. apply InjR_typed.
  by apply Var_typed.
Qed.

Definition embedV_Ground_TProd (p : val) : val :=
  (FoldV (InjLV (InjLV (InjRV p)))).

Definition embed_Ground_TProd : expr :=
  Lam (Fold (InjL (InjL (InjR (Var 0))))).

Definition embed_Ground_TProd_typed Γ :
  Γ ⊢ₛ embed_Ground_TProd : (TArrow (Universe × Universe) Universe).
Proof.
  apply Lam_typed, Fold_typed.
  repeat apply InjL_typed. asimpl. repeat apply InjR_typed.
  by apply Var_typed.
Qed.

Definition embedV_Ground_TArrow (v : val) : val :=
  FoldV (InjLV (InjRV v)).

Definition embed_Ground_TArrow : expr :=
  Lam (Fold (InjL (InjR (Var 0)))).

Definition embed_Ground_TArrow_typed Γ :
  Γ ⊢ₛ embed_Ground_TArrow : (TArrow (TArrow Universe Universe) Universe).
Proof.
  apply Lam_typed, Fold_typed.
  repeat apply InjL_typed. asimpl. repeat apply InjR_typed.
  by apply Var_typed.
Qed.

(* Takes something of μ.Universe, unfolds it so it is in Universe, and then puts in the last branch of the universe *)

Definition embed_Ground_TRec : expr :=
  Lam (Fold (InjR (Unfold (Var 0)))).

Definition embed_Ground_TRec_typed Γ :
  Γ ⊢ₛ embed_Ground_TRec : (TArrow (TRec Universe) Universe).
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
  Γ ⊢ₛ (embed τG G) : (TArrow <<τG>> Universe).
Proof.
  destruct G.
    + apply embed_TUnit_typed.
    + apply embed_Ground_TProd_typed.
    + apply embed_Ground_TSum_typed.
    + apply embed_Ground_TArrow_typed.
    + apply embed_Ground_TRec_typed.
Qed.
