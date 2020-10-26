From fae_gtlc_mu.cast_calculus Require Export types lang consistency.
From fae_gtlc_mu Require Export prelude.
From Coq Require Import List.

Reserved Notation "Γ ⊢ₜ e : τ" (at level 74, e, τ at next level).

(** Typing derivations *)
Inductive typed (Γ : list type) : expr → type → Prop :=
  | Var_typed x τ (pτ : Closed τ) : (Γ !! x = Some τ) → Γ ⊢ₜ Var x : τ
  | Unit_typed : Γ ⊢ₜ Unit : TUnit
  | Pair_typed e1 e2 τ1 τ2 :
     Γ ⊢ₜ e1 : τ1 → Γ ⊢ₜ e2 : τ2 → Γ ⊢ₜ Pair e1 e2 : TProd τ1 τ2
  | Fst_typed e τ1 τ2 : Γ ⊢ₜ e : TProd τ1 τ2 → Γ ⊢ₜ Fst e : τ1
  | Snd_typed e τ1 τ2 : Γ ⊢ₜ e : TProd τ1 τ2 → Γ ⊢ₜ Snd e : τ2
  | InjL_typed e τ1 τ2 (pτ2 : Closed τ2) : Γ ⊢ₜ e : τ1 → Γ ⊢ₜ InjL e : TSum τ1 τ2
  | InjR_typed e τ1 (pτ1 : Closed τ1) τ2 : Γ ⊢ₜ e : τ2 → Γ ⊢ₜ InjR e : TSum τ1 τ2
  | Case_typed e0 e1 e2 τ1 τ2 ρ :
     Γ ⊢ₜ e0 : TSum τ1 τ2 → τ1 :: Γ ⊢ₜ e1 : ρ → τ2 :: Γ ⊢ₜ e2 : ρ →
     Γ ⊢ₜ Case e0 e1 e2 : ρ
  | Lam_typed e τ1 (pτ1 : Closed τ1) τ2 : τ1 :: Γ ⊢ₜ e : τ2 → Γ ⊢ₜ Lam e : TArrow τ1 τ2
  | App_typed e1 e2 τ1 τ2 : Γ ⊢ₜ e1 : TArrow τ1 τ2 → Γ ⊢ₜ e2 : τ1 → Γ ⊢ₜ App e1 e2 : τ2
  | Fold_typed e τ : Γ ⊢ₜ e : τ.[TRec τ/] → Γ ⊢ₜ Fold e : TRec τ
  | Unfold_typed e τ : Γ ⊢ₜ e : TRec τ → Γ ⊢ₜ Unfold e : τ.[TRec τ/]
  (* typing for CAST *)
  | Cast_typed e τi τf (pτf : Closed τf) (pC : consistency_open τi τf) :
      Γ ⊢ₜ e : τi →
      Γ ⊢ₜ Cast e τi τf : τf
  (* typing for BLAME *)
  | CastError_typed τ : Closed τ → Γ ⊢ₜ CastError : τ
where "Γ ⊢ₜ e : τ" := (typed Γ e τ).

From fae_gtlc_mu.cast_calculus Require Export types_lemmas.

(* Our typing derivations are defined such that for any τ, if something is well-typed of type τ, τ is closed (i.e. τ does not contain free variables). *)
Lemma typed_closed {Γ} {e} {τ} : Γ ⊢ₜ e : τ → Closed τ.
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
  - auto.
  - auto.
Qed.
