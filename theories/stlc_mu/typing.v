From fae_gtlc_mu.stlc_mu Require Export types lang.
From fae_gtlc_mu Require Export prelude.
From Coq Require Import List.

Reserved Notation "Γ ⊢ₛ e : τ" (at level 74, e, τ at next level).

(** Typing derivations *)
Inductive typed (Γ : list type) : expr → type → Prop :=
  | Var_typed x τ (pτ : Closed τ) : (Γ !! x = Some τ) → Γ ⊢ₛ Var x : τ
  | Unit_typed : Γ ⊢ₛ Unit : TUnit
  | Pair_typed e1 e2 τ1 τ2 :
     Γ ⊢ₛ e1 : τ1 → Γ ⊢ₛ e2 : τ2 → Γ ⊢ₛ Pair e1 e2 : TProd τ1 τ2
  | Fst_typed e τ1 τ2 : Γ ⊢ₛ e : TProd τ1 τ2 → Γ ⊢ₛ Fst e : τ1
  | Snd_typed e τ1 τ2 : Γ ⊢ₛ e : TProd τ1 τ2 → Γ ⊢ₛ Snd e : τ2
  | InjL_typed e τ1 τ2 (pτ2 : Closed τ2) : Γ ⊢ₛ e : τ1 → Γ ⊢ₛ InjL e : TSum τ1 τ2
  | InjR_typed e τ1 (pτ1 : Closed τ1) τ2 : Γ ⊢ₛ e : τ2 → Γ ⊢ₛ InjR e : TSum τ1 τ2
  | Case_typed e0 e1 e2 τ1 τ2 ρ :
     Γ ⊢ₛ e0 : TSum τ1 τ2 → τ1 :: Γ ⊢ₛ e1 : ρ → τ2 :: Γ ⊢ₛ e2 : ρ →
     Γ ⊢ₛ Case e0 e1 e2 : ρ
  | Lam_typed e τ1 (pτ1 : Closed τ1) τ2 : τ1 :: Γ ⊢ₛ e : τ2 → Γ ⊢ₛ Lam e : TArrow τ1 τ2
  | App_typed e1 e2 τ1 τ2 : Γ ⊢ₛ e1 : TArrow τ1 τ2 → Γ ⊢ₛ e2 : τ1 → Γ ⊢ₛ App e1 e2 : τ2
  | Fold_typed e τ : Γ ⊢ₛ e : τ.[TRec τ/] → Γ ⊢ₛ Fold e : TRec τ
  | Unfold_typed e τ : Γ ⊢ₛ e : TRec τ → Γ ⊢ₛ Unfold e : τ.[TRec τ/]
where "Γ ⊢ₛ e : τ" := (typed Γ e τ).

From fae_gtlc_mu.stlc_mu Require Export types_lemmas.

Lemma typed_closed {Γ} {e} {τ} : Γ ⊢ₛ e : τ → Closed τ.
Proof.
  intro d. induction d.
  - auto.
  - apply TUnit_Closed.
  - by apply TProd_closed.
  - by eapply TProd_closed1.
  - by eapply TProd_closed2.
  - by eapply TSum_closed.
  - by eapply TSum_closed.
  - auto.
  - by apply TArrow_closed.
  - by eapply TArrow_closed2.
  - by apply closed_Fold_typed_help.
  - by apply TRec_closed_unfold.
Qed.
