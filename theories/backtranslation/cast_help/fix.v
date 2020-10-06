From fae_gtlc_mu.stlc_mu Require Export lang typing typing_lemmas.
From fae_gtlc_mu.stlc_mu Require Import typing_lemmas.

Definition Fix (f : expr) : expr :=
  (Unfold (Fold (Lam ((f.[ren (+1)]) (Lam ((Unfold (Var 1)) (Var 1) (Var 0)))))))
    (Fold (Lam (f.[ren (+1)] (Lam ((Unfold (Var 1)) (Var 1) (Var 0)))))).

Lemma Unfold_Fold_typed Γ e τ :
  Γ ⊢ₛ e : τ → Γ ⊢ₛ Unfold (Fold e) : τ.
Proof.
  intro.
  rewrite -(typed_closed H (TRec τ .: ids)).
  apply Unfold_typed.
  apply Fold_typed.
  by rewrite (typed_closed H (TRec τ .: ids)).
Qed.

Lemma Unfold_typed_eq Γ e τb τ' : (τb.[TRec τb/] = τ') →
  Γ ⊢ₛ e : (TRec τb) →
  Γ ⊢ₛ Unfold e : τ'.
Proof. intros eq d. rewrite -eq. by apply Unfold_typed. Qed.

Lemma rewrite_typed {Γ e τ τ'} :
  Γ ⊢ₛ e : τ → τ = τ' → Γ ⊢ₛ e : τ'.
Proof. intros P eq. by simplify_eq. Qed.

Lemma Fix_typed Γ τa τr f :
  (Γ ⊢ₛ f : TArrow (TArrow τa τr) (TArrow τa τr))
  -> (Γ ⊢ₛ Fix f : TArrow τa τr).
Proof.
  intros H.
  assert (pτa : Closed τa). { intro σ.
    assert (x : Closed (TArrow (TArrow τa τr) (TArrow τa τr))). by eapply typed_closed.
    specialize (x σ). inversion x. by repeat rewrite H1. }
  assert (pτr : Closed τr). { intro σ.
    assert (x : Closed (TArrow (TArrow τa τr) (TArrow τa τr))). by eapply typed_closed.
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
