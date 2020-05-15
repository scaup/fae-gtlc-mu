From fae_gtlc_mu Require Export stlc_mu.lang.
From fae_gtlc_mu Require Export stlc_mu.typing.

Definition Fix (f : expr) : expr :=
  (Unfold (Fold (Lam ((f.[ren (+1)]) (Lam ((Unfold (Var 1)) (Var 1) (Var 0)))))))
    (Fold (Lam (f.[ren (+1)] (Lam ((Unfold (Var 1)) (Var 1) (Var 0)))))).

Lemma Fix_typed Γ τa τr f :
  (Γ ⊢ₛ f : TArrow (TArrow τa τr) (TArrow τa τr))
  -> (Γ ⊢ₛ Fix f : TArrow τa τr).
Proof.
  intros H.
  assert (pτa : TClosed τa). { intro σ.
    assert (x : TClosed (TArrow (TArrow τa τr) (TArrow τa τr))). by eapply typed_closed.
    specialize (x σ). inversion x. by repeat rewrite H1. }
  assert (pτr : TClosed τr). { intro σ.
    assert (x : TClosed (TArrow (TArrow τa τr) (TArrow τa τr))). by eapply typed_closed.
    specialize (x σ). inversion x. by repeat rewrite H2. }
  apply App_typed with (τ1 := (TRec (TArrow (TVar 0) (TArrow τa τr)))).
  - apply Unfold_Fold_typed.
    eapply (Lam_typed _ _ _ _).
    apply App_typed with (τ1 := TArrow τa τr). asimpl. by apply up_type_one.
    eapply (Lam_typed _ _ _ _).
    apply App_typed with (τ1 := τa).
    + apply App_typed with (τ1 := TRec (TArrow (TVar 0) (TArrow τa τr))).
      eapply (Unfold_typed_eq _ _ (TArrow (TVar 0) (TArrow τa τr)) _ _).
      by eapply (Var_typed _ _ _ _).
      by eapply (Var_typed _ _ _ _).
    + by eapply (Var_typed _ _ _ _).
  - apply Fold_typed. asimpl.
    eapply (Lam_typed _ _ _ _).
    apply App_typed with (τ1 := (TArrow τa τr)). apply up_type_one. eapply (rewrite_typed H _).
    eapply (Lam_typed _ _ _ _).
    apply App_typed with (τ1 := τa).
    apply App_typed with (τ1 := TRec (TArrow (TVar 0) (TArrow τa τr))).
    + eapply (Unfold_typed_eq _ _ (TArrow (TVar 0) (TArrow τa τr)) _ _).
      by eapply (Var_typed _ _ _ _).
    + by eapply (Var_typed _ _ _ _).
    + by eapply (Var_typed _ _ _ _).
  Unshelve. all: ((try intro σ); asimpl; by repeat rewrite pτa pτr).
Qed.


Lemma Fix_subs_rewrite f σ : (Fix f).[σ] = Fix (f.[σ]).
Proof.
  rewrite /Fix.
  by asimpl.
Qed.

