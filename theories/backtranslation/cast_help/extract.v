From fae_gtlc_mu.cast_calculus Require Export types.
From fae_gtlc_mu.stlc_mu Require Export typing lang lib.fix.
From fae_gtlc_mu.backtranslation Require Export types cast_help.universe.

(** Extractions *)

Definition Ω : expr :=
  (
    (Lam ((Unfold (Var 0)) (Var 0)))
      (Fold (Lam ((Unfold (Var 0)) (Var 0))))
  ).

Lemma Ω_closed : EClosed Ω.
Proof. by asimpl. Qed.

Definition Ω_typed Γ τ (pτ : TClosed τ) : Γ ⊢ₛ Ω : τ.
Proof.
  apply App_typed with (τ1 := (TRec (TArrow (TVar 0) τ))).
  - eapply (Lam_typed _ _ _ _).
    apply App_typed with (τ1 := TRec (TArrow (TVar 0) τ)).
    + apply Unfold_typed_eq with (τb := (TArrow (TVar 0) τ)).
      asimpl. by rewrite pτ. by eapply (Var_typed _ _ _ _).
    + by eapply (Var_typed _ _ _ _).
  - apply Fold_typed. asimpl.
    eapply (Lam_typed _ _ _ _).
    apply App_typed with (τ1 := TRec (TArrow (TVar 0) τ)).
    + apply Unfold_typed_eq with (τb := (TArrow (TVar 0) τ)).
      by asimpl. by eapply (Var_typed _ _ _ _).
    + by eapply (Var_typed _ _ _ _).
    Unshelve. all:intro σ; asimpl; by repeat rewrite pτ.
Qed.

Definition extract_TUnit : val :=
  LamV (Case (Unfold (Var 0))
            (Case (Var 0)
                  (Case (Var 0)
                        (Case (Var 0)
                              (Var 0)
                              (Ω)
                        )
                        (Ω)
                  )
                  (Ω)
            )
            (Ω)
      ).

Definition extract_TUnit_typed Γ : Γ ⊢ₛ extract_TUnit : (TArrow Universe TUnit).
Proof.
  eapply (Lam_typed _ _ _ _).
  apply Case_typed with (τ1 := (TUnit + (TVar 0 + TVar 0) + (TVar 0 × TVar 0) + (TArrow (TVar 0) (TVar 0))).[Universe/]%type)
                         (τ2 := Universe).
  - eapply Unfold_typed_help_2 with (τ := Universe_body). by asimpl.
    by apply Var_typed.
  - apply Case_typed with (τ1 := (TUnit + (TVar 0 + TVar 0) + (TVar 0 × TVar 0)).[Universe/]%type)
                          (τ2 := (TArrow (TVar 0) (TVar 0)).[Universe/]%type).
    + by apply Var_typed.
    + eapply Case_typed.
      * by eapply (Var_typed _ _ _ _).
      * eapply Case_typed.
        -- by eapply (Var_typed _ _ _ _).
        -- by eapply (Var_typed _ _ _ _).
        -- by apply Ω_typed.
      * by apply Ω_typed.
    + by apply Ω_typed.
  - by apply Ω_typed.
    Unshelve. all: intro σ; by asimpl.
Qed.

Definition extract_Ground_TSum : val :=
  LamV (Case (Unfold (Var 0))
            (Case (Var 0)
                  (Case (Var 0)
                        (Case (Var 0)
                              (Ω)
                              (Var 0)
                        )
                        (Ω)
                  )
                  (Ω)
            )
            (Ω)
      ).

Definition extract_Ground_TSum_typed Γ : Γ ⊢ₛ extract_Ground_TSum : (TArrow Universe (Universe + Universe))%type.
Proof.
  eapply (Lam_typed _ _ _ _).
  apply Case_typed with (τ1 := (TUnit + (TVar 0 + TVar 0) + (TVar 0 × TVar 0) + (TArrow (TVar 0) (TVar 0))).[Universe/]%type)
                         (τ2 := Universe).
  - eapply Unfold_typed_help_2 with (τ := Universe_body). by asimpl. by apply Var_typed.
  - eapply Case_typed. by eapply (Var_typed _ _ _ _).
    + eapply Case_typed.
      * by eapply (Var_typed _ _ _ _).
      * eapply Case_typed.
        -- by eapply (Var_typed _ _ _ _).
        -- by apply Ω_typed.
        -- by eapply (Var_typed _ _ _ _).
      * by apply Ω_typed.
    + by apply Ω_typed.
  - by apply Ω_typed.
    Unshelve. all: intro σ; by asimpl.
Qed.

Definition extract_Ground_TProd : val :=
  LamV (Case (Unfold (Var 0))
            (Case (Var 0)
                  (Case (Var 0)
                        (Ω)
                        (Var 0)
                  )
                  (Ω)
            )
            (Ω)
      ).

Definition extract_Ground_TProd_typed Γ : Γ ⊢ₛ extract_Ground_TProd : (TArrow Universe (Universe × Universe)).
Proof.
  eapply (Lam_typed _ _ _ _).
  apply Case_typed with (τ1 := (TUnit + (TVar 0 + TVar 0) + (TVar 0 × TVar 0) + (TArrow (TVar 0) (TVar 0))).[Universe/]%type)
                         (τ2 := Universe).
  - eapply Unfold_typed_help_2 with (τ := Universe_body). by asimpl. by apply Var_typed.
  - eapply Case_typed. by eapply (Var_typed _ _ _ _).
    + eapply Case_typed.
      * by eapply (Var_typed _ _ _ _).
      * by apply Ω_typed.
      * by eapply (Var_typed _ _ _ _).
    + by apply Ω_typed.
  - by apply Ω_typed.
    Unshelve. all: intro σ; by asimpl.
Qed.

Definition extract_Ground_TArrow : val :=
  LamV (Case (Unfold (Var 0))
            (Case (Var 0)
                  (Ω)
                  (Var 0)
            )
            (Ω)
      ).

Definition extract_Ground_TArrow_typed Γ : Γ ⊢ₛ extract_Ground_TArrow : (TArrow Universe (TArrow Universe Universe)).
Proof.
  eapply (Lam_typed _ _ _ _).
  apply Case_typed with (τ1 := (TUnit + (TVar 0 + TVar 0) + (TVar 0 × TVar 0) + (TArrow (TVar 0) (TVar 0))).[Universe/]%type)
                         (τ2 := Universe).
  - eapply Unfold_typed_help_2 with (τ := Universe_body). by asimpl. by apply Var_typed.
  - eapply Case_typed. by eapply (Var_typed _ _ _ _).
    + by apply Ω_typed.
    + by apply Var_typed.
  - by apply Ω_typed.
    Unshelve. all: intro σ; by asimpl.
Qed.

Definition extract_Ground_TRec : val :=
  LamV (Case (Unfold (Var 0))
            (Ω)
            (Fold (Var 0))
      ).

Definition extract_Ground_TRec_typed Γ : Γ ⊢ₛ extract_Ground_TRec : (TArrow Universe (TRec Universe)).
Proof.
  eapply (Lam_typed _ _ _ _).
  apply Case_typed with (τ1 := (TUnit + (TVar 0 + TVar 0) + (TVar 0 × TVar 0) + (TArrow (TVar 0) (TVar 0))).[Universe/]%type)
                        (τ2 := Universe).
  - eapply Unfold_typed_help_2 with (τ := Universe_body). by asimpl. by apply Var_typed.
  - by apply Ω_typed.
  - apply Fold_typed. by apply Var_typed.
  Unshelve. apply Universe_closed.
Qed.

Definition extract (τ : cast_calculus.types.type) (G : Ground τ) : val :=
  match G with
  | Ground_TUnit => extract_TUnit
  | Ground_TProd => extract_Ground_TProd
  | Ground_TSum => extract_Ground_TSum
  | Ground_TArrow => extract_Ground_TArrow
  | Ground_TRec => extract_Ground_TRec
  end.

Lemma extract_typed {τG : cast_calculus.types.type} {G : Ground τG} Γ:
  Γ ⊢ₛ (extract τG G) : (TArrow Universe <<τG>>).
Proof.
  destruct G.
    + apply extract_TUnit_typed.
    + apply extract_Ground_TProd_typed.
    + apply extract_Ground_TSum_typed.
    + apply extract_Ground_TArrow_typed.
    + apply extract_Ground_TRec_typed.
Qed.

Lemma extract_no_subs {τ : cast_calculus.types.type} {G : Ground τ} σ : (# (extract τ G)).[σ] = extract τ G.
Proof.
  destruct G; by asimpl.
Qed.
