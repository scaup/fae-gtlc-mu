From fae_gtlc_mu Require Export stlc_mu.lang.
From fae_gtlc_mu Require Export stlc_mu.typing.

Definition Fix (f : expr) : expr :=
  (Unfold (Fold (Lam ((rename (+1) f) (Lam ((Unfold (Var 1)) (Var 1) (Var 0)))))))
    (Fold (Lam (rename (+1) f (Lam ((Unfold (Var 1)) (Var 1) (Var 0)))))).

(* Program Definition tau1 τa: ctype := [(TRec (TArrow (TVar 0) (TArrow τa τr))) % _]. *)

Lemma Fix_typed Γ pΓ τa pτa τr pτr f :
  (Γ & pΓ ⊢ₛ f : (TArrow (TArrow τa τr) (TArrow τa τr)) & (TArrow_closed (TArrow_closed pτa pτr) (TArrow_closed pτa pτr)))
  -> (Γ & pΓ ⊢ₛ Fix f : (TArrow τa τr) & (TArrow_closed pτa pτr)).
Proof.
  intros H.
  eapply App_typed with (τ1 := (TRec (TArrow (TVar 0) (TArrow τa τr)))).
  - apply Unfold_Fold_typed.
    eapply Lam_typed.
    eapply App_typed with (τ1 := TArrow τa τr). asimpl. by eapply up_type_one.
    eapply Lam_typed.
    eapply App_typed with (τ1 := τa).
    + eapply App_typed with (τ1 := TRec (TArrow (TVar 0) (TArrow τa τr))).
      asimpl. eapply Unfold_typed_help with (τb := TArrow (TVar 0) (TArrow τa τr)).
      asimpl. by rewrite pτa pτr. by apply Var_typed. by apply Var_typed.
    + by apply Var_typed.
  - eapply Fold_typed. asimpl.
    eapply Lam_typed.
    eapply App_typed with (τ1 := (TArrow τa τr)). eapply up_type_one. eapply (rewrite_typed H). by rewrite pτa pτr.
    eapply Lam_typed.
    eapply App_typed with (τ1 := τa).
    eapply App_typed with (τ1 := TRec (TArrow (TVar 0) (TArrow τa τr))).
    + eapply Unfold_typed_help with (τb := (TArrow (TVar 0) (TArrow τa τr))).
      asimpl. by rewrite pτa pτr. by apply Var_typed.
    + by apply Var_typed.
    + by apply Var_typed.
      Unshelve. 1-24:intro σ; asimpl; by repeat rewrite pτa pτr.
Qed.


Lemma Fix_subs_rewrite f σ : (Fix f).[σ] = Fix (f.[σ]).
Proof.
  rewrite /Fix.
  by asimpl.
Qed.
