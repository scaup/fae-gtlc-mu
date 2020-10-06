From fae_gtlc_mu.cast_calculus Require Export types typing lang.
From fae_gtlc_mu.stlc_mu Require Import types_notations.
From fae_gtlc_mu.backtranslation Require Export universe types cast_help.fix.

(** Embeddings *)

Definition embedV_TUnit (v : val) : val :=
  (FoldV (InjLV (InjLV (InjLV (InjLV v))))).

Definition embed_TUnit : val :=
  LamV (Fold (InjL (InjL (InjL (InjL (Var 0)))))).

Lemma embed_TUnit_typed Γ :
  Γ ⊢ₛ embed_TUnit : (TArrow TUnit Universe).
Proof.
  apply Lam_typed, Fold_typed. apply TUnit_Closed.
  repeat apply InjL_typed.
  all:try (intro σ; by asimpl).
  by apply Var_typed.
Qed.

Definition embedV_Ground_TSum (s : val) : val :=
  (FoldV ((InjLV (InjLV (InjLV (InjRV s)))))).

Definition embed_Ground_TSum : val :=
  LamV (Fold ((InjL (InjL (InjL (InjR (Var 0))))))).

Definition embed_Ground_TSum_typed Γ :
  Γ ⊢ₛ embed_Ground_TSum : (TArrow (Universe + Universe) Universe)%type.
Proof.
  eapply (Lam_typed _ _ _ _).
  apply Fold_typed.
  repeat eapply (InjL_typed _ _ _ _ _).
  eapply (InjR_typed _ _ _ _).
  by apply Var_typed.
  Unshelve. all:try (intro σ; by asimpl).
Qed.

Definition embedV_Ground_TProd (p : val) : val :=
  (FoldV (InjLV (InjLV (InjRV p)))).

Definition embed_Ground_TProd : val :=
  LamV (Fold (InjL (InjL (InjR (Var 0))))).

Definition embed_Ground_TProd_typed Γ :
  Γ ⊢ₛ embed_Ground_TProd : (TArrow (Universe × Universe) Universe).
Proof.
  apply Lam_typed, Fold_typed; try closed_solver.
  repeat apply InjL_typed; try closed_solver.
  apply InjR_typed; try closed_solver.
  by eapply Var_typed; try closed_solver.
Qed.

Definition embedV_Ground_TArrow (v : val) : val :=
  FoldV (InjLV (InjRV v)).

Definition embed_Ground_TArrow : val :=
  LamV (Fold (InjL (InjR (Var 0)))).

Definition embed_Ground_TArrow_typed Γ :
  Γ ⊢ₛ embed_Ground_TArrow : (TArrow (TArrow Universe Universe) Universe).
Proof.
  eapply Lam_typed, Fold_typed; try closed_solver.
  repeat eapply InjL_typed; try closed_solver. eapply InjR_typed; try closed_solver.
  by apply Var_typed.
Qed.

(* Takes something of μ.Universe, unfolds it so it is in Universe, and then puts in the last branch of the universe *)

Definition embed_Ground_TRec : val :=
  LamV (Fold (InjR (Unfold (Var 0)))).

Definition embed_Ground_TRec_typed Γ :
  Γ ⊢ₛ embed_Ground_TRec : (TArrow (TRec Universe) Universe).
Proof.
  apply Lam_typed; try closed_solver. apply Fold_typed; try closed_solver.
  apply InjR_typed; try closed_solver.
  apply Unfold_typed_help; first by trivial.
  by apply Var_typed.
Qed.

Definition embedV_TUnknown (u : val) : val := (** a bit different from the other ones... u : Universe instead of u : μX.Universe *)
  (FoldV (InjRV u)).

Definition embed (τ : cast_calculus.types.type) (G : Ground τ) : val :=
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

Lemma embed_no_subs {τ : cast_calculus.types.type} {G : Ground τ} σ : (# (embed τ G)).[σ] = embed τ G.
Proof.
  destruct G; by asimpl.
Qed.
