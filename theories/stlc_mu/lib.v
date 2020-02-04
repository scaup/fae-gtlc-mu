From fae_gtlc_mu Require Export stlc_mu.lang.
From fae_gtlc_mu Require Export stlc_mu.typing.

Infix "→" := TArrow : type_scope.

Definition Universe_body : type :=
  (
    TUnit +
    (TVar 0 + TVar 0) +
    (TVar 0 × TVar 0) +
    (TVar 0 → TVar 0) +
    (TVar 0)
  )%type.

(* + is left associative; (a + b + c) = ((a + b) + c) *)

Definition Universe : type :=
  TRec Universe_body.

Definition Universe_unfolded : type :=
  Universe_body.[Universe/]%type.

Definition Inj_TUnit : expr :=
  Lam (Fold ((InjL (InjL (InjL (InjL (Var 0))))))).

Definition Inj_TUnit_typed : [] ⊢ₛ Inj_TUnit : (TUnit → Universe).
Proof.
  apply Lam_typed, Fold_typed.
  repeat apply InjL_typed.
  by apply Var_typed.
Qed.

Definition Inj_TSum : expr :=
  Lam (Fold ((InjL (InjL (InjL (InjR (Var 0))))))).

Definition Inj_TSum_typed : [] ⊢ₛ Inj_TSum : ((Universe + Universe) → Universe)%type.
Proof.
  apply Lam_typed.
  apply Fold_typed.
  repeat apply InjL_typed. apply InjR_typed.
  by apply Var_typed.
Qed.

Definition Inj_TProd : expr :=
  Lam (Fold (InjL (InjL (InjR (Var 0))))).

Definition Inj_TProd_typed : [] ⊢ₛ Inj_TProd : ((Universe × Universe) → Universe).
Proof.
  apply Lam_typed, Fold_typed.
  repeat apply InjL_typed. asimpl. repeat apply InjR_typed.
  by apply Var_typed.
Qed.

Definition Inj_TRec : expr :=
  Lam (Fold (InjR (Unfold (Var 0)))).

Definition Inj_TRec_typed : [] ⊢ₛ Inj_TRec : (TRec Universe → Universe).
Proof.
  apply Lam_typed. apply Fold_typed.
  apply InjR_typed.
  asimpl.
  apply Unfold_typed_help; first by trivial.
  by apply Var_typed.
Qed.

Coercion App : expr >-> Funclass.

Definition Ω : expr :=
  (
    (Lam ((Unfold (Var 0)) (Var 0)))
      (Fold (Lam ((Unfold (Var 0)) (Var 0))))
  ).

Definition Is_Closed τ := forall τ', τ.[τ'/] = τ.

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

Definition Fix : expr :=
  Lam (
      (Lam (Var 1 ((Unfold (Var 0)) (Var 0))))
        (Fold (Lam (Var 1 ((Unfold (Var 0)) (Var 0)))))
  ).

Definition Fix_typed Γ τ : (Is_Closed τ) -> (Γ ⊢ₛ Fix : ((τ → τ) → τ)).
Proof.
  intro P.
  apply Lam_typed.
  apply App_typed with (τ1 := (TRec (TVar 0 → τ))).
  - apply Lam_typed.
    apply App_typed with (τ1 := τ); first by apply Var_typed.
    apply App_typed with (τ1 := TRec (TVar 0 → τ)).
    + apply Unfold_typed_help_2 with (τ := (TVar 0 → τ)).
      asimpl. by rewrite P. by apply Var_typed.
    + by apply Var_typed.
  - apply Fold_typed. asimpl. rewrite P.
    apply Lam_typed.
    apply App_typed with (τ1 := τ); first by apply Var_typed.
    apply App_typed with (τ1 := TRec (TVar 0 → τ)).
    + apply Unfold_typed_help_2 with (τ := (TVar 0 → τ)).
      asimpl. by rewrite P. by apply Var_typed.
    + by apply Var_typed.
Qed.

Definition Match_TUnit : expr :=
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

Definition Match_TUnit_typed : [] ⊢ₛ Match_TUnit : (Universe → TUnit).
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

Definition Match_TSum : expr :=
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

Definition Match_TSum_typed : [] ⊢ₛ Match_TSum : (Universe → (Universe + Universe))%type.
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

Definition Match_TProd : expr :=
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

Definition Match_TProd_typed : [] ⊢ₛ Match_TProd : (Universe → (Universe × Universe)).
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

Definition Match_TArrow : expr :=
  Lam (Case (Unfold (Var 0))
            (Case (Var 0)
                  (Ω)
                  (Var 0)
            )
            (Ω)
      ).

Definition Match_TArrow_typed : [] ⊢ₛ Match_TArrow : (Universe → (Universe → Universe)).
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

Definition Match_TRec : expr :=
  Lam (Case (Unfold (Var 0))
            (Ω)
            (Fold (Var 0))
      ).

Definition Match_TRec_typed : [] ⊢ₛ Match_TRec : (Universe → TRec Universe).
Proof.
  apply Lam_typed.
  apply Case_typed with (τ1 := (TUnit + (TVar 0 + TVar 0) + (TVar 0 × TVar 0) + (TVar 0 → TVar 0)).[Universe/]%type)
                         (τ2 := Universe).
  - eapply Unfold_typed_help_2 with (τ := Universe_body). by asimpl. by apply Var_typed.
  - by apply Ω_typed.
  - apply Fold_typed. by apply Var_typed.
Qed.
