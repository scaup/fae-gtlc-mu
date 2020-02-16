From fae_gtlc_mu.cast_calculus Require Export types consistency.structural.definition.
From fae_gtlc_mu.stlc_mu Require Export typing lang lib.fix lib.universe.
From fae_gtlc_mu.backtranslation Require Export types.

(** Extractions *)

Definition Ω : expr :=
  (
    (Lam ((Unfold (Var 0)) (Var 0)))
      (Fold (Lam ((Unfold (Var 0)) (Var 0))))
  ).

Definition Ω_typed Γ τ : (Is_Closed τ) -> (Γ ⊢ₛ Ω : τ).
Proof.
  intro P.
  apply App_typed with (τ1 := (TRec (TVar 0 → τ))).
  - apply Lam_typed.
    apply App_typed with (τ1 := TRec (TVar 0 → τ)).
    + apply Unfold_typed_help_2 with (τ := (TVar 0 → τ)).
      asimpl. by rewrite P. by apply Var_typed.
    + by apply Var_typed.
  - apply Fold_typed. asimpl. rewrite P.
    apply Lam_typed.
    apply App_typed with (τ1 := TRec (TVar 0 → τ)).
    + apply Unfold_typed_help_2 with (τ := (TVar 0 → τ)).
      asimpl. by rewrite P. by apply Var_typed.
    + by apply Var_typed.
Qed.

Definition extract_TUnit : expr :=
  Lam (Case (Unfold (Var 0))
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

Definition extract_TUnit_typed Γ : Γ ⊢ₛ extract_TUnit : (Universe → TUnit).
Proof.
  apply Lam_typed.
  apply Case_typed with (τ1 := (TUnit + (TVar 0 + TVar 0) + (TVar 0 × TVar 0) + (TVar 0 → TVar 0)).[Universe/]%type)
                         (τ2 := Universe).
  - eapply Unfold_typed_help_2 with (τ := Universe_body). by asimpl.
    by apply Var_typed.
  - apply Case_typed with (τ1 := (TUnit + (TVar 0 + TVar 0) + (TVar 0 × TVar 0)).[Universe/]%type)
                          (τ2 := (TVar 0 → TVar 0).[Universe/]%type).
    + by apply Var_typed.
    + eapply Case_typed.
      * by apply Var_typed.
      * eapply Case_typed.
        -- by apply Var_typed.
        -- by apply Var_typed.
        -- by apply Ω_typed.
      * by apply Ω_typed.
    + by apply Ω_typed.
  - by apply Ω_typed.
Qed.

Definition extract_Ground_TSum : expr :=
  Lam (Case (Unfold (Var 0))
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

Definition extract_Ground_TSum_typed Γ : Γ ⊢ₛ extract_Ground_TSum : (Universe → (Universe + Universe))%type.
Proof.
  apply Lam_typed.
  apply Case_typed with (τ1 := (TUnit + (TVar 0 + TVar 0) + (TVar 0 × TVar 0) + (TVar 0 → TVar 0)).[Universe/]%type)
                         (τ2 := Universe).
  - eapply Unfold_typed_help_2 with (τ := Universe_body). by asimpl. by apply Var_typed.
  - eapply Case_typed. by apply Var_typed.
    + eapply Case_typed.
      * by apply Var_typed.
      * eapply Case_typed.
        -- by apply Var_typed.
        -- by apply Ω_typed.
        -- by apply Var_typed.
      * by apply Ω_typed.
    + by apply Ω_typed.
  - by apply Ω_typed.
Qed.

Definition extract_Ground_TProd : expr :=
  Lam (Case (Unfold (Var 0))
            (Case (Var 0)
                  (Case (Var 0)
                        (Ω)
                        (Var 0)
                  )
                  (Ω)
            )
            (Ω)
      ).

Definition extract_Ground_TProd_typed Γ : Γ ⊢ₛ extract_Ground_TProd : (Universe → (Universe × Universe)).
Proof.
  apply Lam_typed.
  apply Case_typed with (τ1 := (TUnit + (TVar 0 + TVar 0) + (TVar 0 × TVar 0) + (TVar 0 → TVar 0)).[Universe/]%type)
                         (τ2 := Universe).
  - eapply Unfold_typed_help_2 with (τ := Universe_body). by asimpl. by apply Var_typed.
  - eapply Case_typed. by apply Var_typed.
    + eapply Case_typed.
      * by apply Var_typed.
      * by apply Ω_typed.
      * by apply Var_typed.
    + by apply Ω_typed.
  - by apply Ω_typed.
Qed.

Definition extract_Ground_TArrow : expr :=
  Lam (Case (Unfold (Var 0))
            (Case (Var 0)
                  (Ω)
                  (Var 0)
            )
            (Ω)
      ).

Definition extract_Ground_TArrow_typed Γ : Γ ⊢ₛ extract_Ground_TArrow : (Universe → (Universe → Universe)).
Proof.
  apply Lam_typed.
  apply Case_typed with (τ1 := (TUnit + (TVar 0 + TVar 0) + (TVar 0 × TVar 0) + (TVar 0 → TVar 0)).[Universe/]%type)
                         (τ2 := Universe).
  - eapply Unfold_typed_help_2 with (τ := Universe_body). by asimpl. by apply Var_typed.
  - eapply Case_typed. by apply Var_typed.
    + by apply Ω_typed.
    + by apply Var_typed.
  - by apply Ω_typed.
Qed.

Definition extract_Ground_TRec : expr :=
  Lam (Case (Unfold (Var 0))
            (Ω)
            (Fold (Var 0))
      ).

Definition extract_Ground_TRec_typed Γ : Γ ⊢ₛ extract_Ground_TRec : (Universe → TRec Universe).
Proof.
  apply Lam_typed.
  apply Case_typed with (τ1 := (TUnit + (TVar 0 + TVar 0) + (TVar 0 × TVar 0) + (TVar 0 → TVar 0)).[Universe/]%type)
                         (τ2 := Universe).
  - eapply Unfold_typed_help_2 with (τ := Universe_body). by asimpl. by apply Var_typed.
  - by apply Ω_typed.
  - apply Fold_typed. by apply Var_typed.
Qed.

Definition extract (τ : cast_calculus.types.type) (G : Ground τ) : expr :=
  match G with
  | Ground_TUnit => extract_TUnit
  | Ground_TProd => extract_Ground_TProd
  | Ground_TSum => extract_Ground_TSum
  | Ground_TArrow => extract_Ground_TArrow
  | Ground_TRec => extract_Ground_TRec
  end.

Lemma extract_typed {τG : cast_calculus.types.type} {G : Ground τG} Γ :
  Γ ⊢ₛ (extract τG G) : (Universe → <<τG>>).
Proof.
  destruct G.
    + apply extract_TUnit_typed.
    + apply extract_Ground_TProd_typed.
    + apply extract_Ground_TSum_typed.
    + apply extract_Ground_TArrow_typed.
    + apply extract_Ground_TRec_typed.
Qed.
