From fae_gtlc_mu.cast_calculus Require Export types.
From fae_gtlc_mu.stlc_mu Require Export typing lang lib.fix.
From fae_gtlc_mu.backtranslation Require Export universe types.

(** Embeddings *)

Definition embedV_TUnit (v : val) : val :=
  (FoldV (InjLV (InjLV (InjLV (InjLV v))))).

Definition embed_TUnit : val :=
  LamV (Fold (InjL (InjL (InjL (InjL (Var 0)))))).

Lemma embed_TUnit_typed Γ pΓ :
  Γ & pΓ ⊢ₛ embed_TUnit : (TArrow TUnit Universe) & (TArrow_closed TUnit_TClosed Universe_closed).
Proof.
  eapply Lam_typed, Fold_typed.
  repeat eapply InjL_typed.
  by eapply Var_typed.
  Unshelve. all:intro σ; by asimpl.
Qed.

Definition embedV_Ground_TSum (s : val) : val :=
  (FoldV ((InjLV (InjLV (InjLV (InjRV s)))))).

Definition embed_Ground_TSum : val :=
  LamV (Fold ((InjL (InjL (InjL (InjR (Var 0))))))).

Definition embed_Ground_TSum_typed Γ pΓ :
  Γ & pΓ ⊢ₛ embed_Ground_TSum : (TArrow (Universe + Universe) Universe)%type &
                                (TArrow_closed (TSum_closed Universe_closed Universe_closed) Universe_closed).
Proof.
  eapply Lam_typed.
  eapply Fold_typed.
  repeat eapply InjL_typed. eapply InjR_typed.
  by apply Var_typed.
  Unshelve. all:intro σ; by asimpl.
Qed.

Definition embedV_Ground_TProd (p : val) : val :=
  (FoldV (InjLV (InjLV (InjRV p)))).

Definition embed_Ground_TProd : val :=
  LamV (Fold (InjL (InjL (InjR (Var 0))))).

Definition embed_Ground_TProd_typed Γ pΓ :
  Γ & pΓ ⊢ₛ embed_Ground_TProd : (TArrow (Universe × Universe) Universe) &
                                 ltac:(apply (TArrow_closed (TProd_closed Universe_closed Universe_closed) Universe_closed)).
Proof.
  eapply Lam_typed, Fold_typed.
  repeat eapply InjL_typed. asimpl. repeat eapply InjR_typed.
  by apply Var_typed.
  Unshelve. all:intro σ; by asimpl.
Qed.

Definition embedV_Ground_TArrow (v : val) : val :=
  FoldV (InjLV (InjRV v)).

Definition embed_Ground_TArrow : val :=
  LamV (Fold (InjL (InjR (Var 0)))).

Definition embed_Ground_TArrow_typed Γ pΓ :
  Γ & pΓ ⊢ₛ embed_Ground_TArrow : (TArrow (TArrow Universe Universe) Universe) &
                                  (TArrow_closed (TArrow_closed Universe_closed Universe_closed) Universe_closed).
Proof.
  eapply Lam_typed, Fold_typed.
  repeat eapply InjL_typed. asimpl. repeat eapply InjR_typed.
  by apply Var_typed.
  Unshelve. all:intro σ; by asimpl.
Qed.

(* Takes something of μ.Universe, unfolds it so it is in Universe, and then puts in the last branch of the universe *)

Definition embed_Ground_TRec : val :=
  LamV (Fold (InjR (Unfold (Var 0)))).

Definition embed_Ground_TRec_typed Γ pΓ :
  Γ & pΓ ⊢ₛ embed_Ground_TRec : (TArrow (TRec Universe) Universe) &
                                (TArrow_closed (TRec_closed Universe_closed) Universe_closed).
Proof.
  eapply Lam_typed. eapply Fold_typed.
  eapply InjR_typed.
  asimpl.
  eapply Unfold_typed_help with (τb := Universe). by rewrite Universe_closed.
  by apply Var_typed.
  Unshelve. all:intro σ; by asimpl.
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

Lemma embed_typed {τG : cast_calculus.types.type} {G : Ground τG} Γ pΓ :
  Γ & pΓ ⊢ₛ (embed τG G) : (TArrow <<τG>> Universe) &
                           (TArrow_closed (back_Ground_closed G) Universe_closed).
Proof.
  destruct G; eapply PI_typed.
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

