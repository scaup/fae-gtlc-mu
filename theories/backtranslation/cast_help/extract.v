From fae_gtlc_mu.cast_calculus Require Export types.
From fae_gtlc_mu.stlc_mu Require Export typing lang lib.fix.
From fae_gtlc_mu.backtranslation Require Export types cast_help.universe.

(** Extractions *)

Definition Ω : expr :=
  (
    (Lam ((Unfold (Var 0)) (Var 0)))
      (Fold (Lam ((Unfold (Var 0)) (Var 0))))
  ).

Definition Ω_typed Γ pΓ τ pτ : Γ & pΓ ⊢ₛ Ω : τ & pτ.
Proof.
  eapply App_typed with (τ1 := (TRec (TArrow (TVar 0) τ))).
  - eapply Lam_typed.
    eapply App_typed with (τ1 := TRec (TArrow (TVar 0) τ)).
    + eapply Unfold_typed_help with (τb := (TArrow (TVar 0) τ)).
      asimpl. by rewrite pτ. by apply Var_typed.
    + by apply Var_typed.
  - eapply Fold_typed. asimpl.
    eapply Lam_typed.
    eapply App_typed with (τ1 := TRec (TArrow (TVar 0) τ)).
    + eapply Unfold_typed_help with (τb := (TArrow (TVar 0) τ)).
      by asimpl. by apply Var_typed.
    + by apply Var_typed.
    Unshelve. 1-13:intro σ; asimpl; by repeat rewrite pτ.
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

Definition extract_TUnit_typed Γ pΓ: Γ & pΓ ⊢ₛ extract_TUnit : (TArrow Universe TUnit) &
                                                                (TArrow_closed Universe_closed TUnit_TClosed).
Proof.
  eapply Lam_typed.
  eapply Case_typed with (τ1 := (TUnit + (TVar 0 + TVar 0) + (TVar 0 × TVar 0) + (TArrow (TVar 0) (TVar 0))).[Universe/]%type)
                         (τ2 := Universe).
  - eapply Unfold_typed_help with (τb := Universe_body). by asimpl.
    by apply Var_typed.
  - eapply Case_typed with (τ1 := (TUnit + (TVar 0 + TVar 0) + (TVar 0 × TVar 0)).[Universe/]%type)
                          (τ2 := (TArrow (TVar 0) (TVar 0)).[Universe/]%type).
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
  Unshelve. all:intro σ; by asimpl.
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

Definition extract_Ground_TSum_typed Γ pΓ: Γ & pΓ ⊢ₛ extract_Ground_TSum : (TArrow Universe (Universe + Universe))%type &
                                                                           (TArrow_closed Universe_closed (TSum_closed Universe_closed Universe_closed)).
Proof.
  eapply Lam_typed.
  eapply Case_typed with (τ1 := (TUnit + (TVar 0 + TVar 0) + (TVar 0 × TVar 0) + (TArrow (TVar 0) (TVar 0))).[Universe/]%type)
                         (τ2 := Universe).
  - eapply Unfold_typed_help with (τb := Universe_body). by asimpl. by apply Var_typed.
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
  Unshelve. all:intro σ; by asimpl.
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

Definition extract_Ground_TProd_typed Γ pΓ: Γ & pΓ ⊢ₛ extract_Ground_TProd : (TArrow Universe (Universe × Universe)) &
 (TArrow_closed Universe_closed (TProd_closed Universe_closed Universe_closed)).
Proof.
  eapply Lam_typed.
  eapply Case_typed with (τ1 := (TUnit + (TVar 0 + TVar 0) + (TVar 0 × TVar 0) + (TArrow (TVar 0) (TVar 0))).[Universe/]%type)
                         (τ2 := Universe).
  - eapply Unfold_typed_help with (τb := Universe_body). by asimpl. by apply Var_typed.
  - eapply Case_typed. by apply Var_typed.
    + eapply Case_typed.
      * by apply Var_typed.
      * by apply Ω_typed.
      * by apply Var_typed.
    + by apply Ω_typed.
  - by apply Ω_typed.
  Unshelve. all:intro σ; by asimpl.
Qed.


Definition extract_Ground_TArrow : val :=
  LamV (Case (Unfold (Var 0))
            (Case (Var 0)
                  (Ω)
                  (Var 0)
            )
            (Ω)
      ).

Definition extract_Ground_TArrow_typed Γ pΓ: Γ & pΓ ⊢ₛ extract_Ground_TArrow : (TArrow Universe (TArrow Universe Universe)) &
TArrow_closed Universe_closed (TArrow_closed Universe_closed Universe_closed).
Proof.
  eapply Lam_typed.
  eapply Case_typed with (τ1 := (TUnit + (TVar 0 + TVar 0) + (TVar 0 × TVar 0) + (TArrow (TVar 0) (TVar 0))).[Universe/]%type)
                         (τ2 := Universe).
  - eapply Unfold_typed_help with (τb := Universe_body). by asimpl. by apply Var_typed.
  - eapply Case_typed. by apply Var_typed.
    + by apply Ω_typed.
    + by apply Var_typed.
  - by apply Ω_typed.
  Unshelve. all:intro σ; by asimpl.
Qed.


Definition extract_Ground_TRec : val :=
  LamV (Case (Unfold (Var 0))
            (Ω)
            (Fold (Var 0))
      ).

Definition extract_Ground_TRec_typed Γ pΓ: Γ & pΓ ⊢ₛ extract_Ground_TRec : (TArrow Universe (TRec Universe)) &
TArrow_closed Universe_closed (TRec_closed Universe_closed).
Proof.
  eapply Lam_typed.
  eapply Case_typed with (τ1 := (TUnit + (TVar 0 + TVar 0) + (TVar 0 × TVar 0) + (TArrow (TVar 0) (TVar 0))).[Universe/]%type)


                        (τ2 := Universe).
  - eapply Unfold_typed_help with (τb := Universe_body). by asimpl. by apply Var_typed.
  - by apply Ω_typed.
  - eapply Fold_typed. by apply Var_typed.
    Unshelve. 1-7:intro σ; by asimpl.
Qed.

Definition extract (τ : cast_calculus.types.type) (G : Ground τ) : val :=
  match G with
  | Ground_TUnit => extract_TUnit
  | Ground_TProd => extract_Ground_TProd
  | Ground_TSum => extract_Ground_TSum
  | Ground_TArrow => extract_Ground_TArrow
  | Ground_TRec => extract_Ground_TRec
  end.

Lemma extract_typed {τG : cast_calculus.types.type} {G : Ground τG} Γ pΓ:
  Γ & pΓ ⊢ₛ (extract τG G) : (TArrow Universe <<τG>>) &
TArrow_closed Universe_closed (back_Ground_closed G).
Proof.
  destruct G; eapply PI_typed.
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
