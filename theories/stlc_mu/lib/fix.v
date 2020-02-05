From fae_gtlc_mu Require Export stlc_mu.lang.
From fae_gtlc_mu Require Export stlc_mu.typing.

Coercion App : expr >-> Funclass.
Infix "→" := TArrow : type_scope.

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
