From Autosubst Require Export Autosubst.
From fae_gtlc_mu Require Export prelude.
From fae_gtlc_mu.cast_calculus Require Export lang types.
From fae_gtlc_mu Require Export cast_calculus.types.

Reserved Notation "Γ ⊢ₜ e : τ" (at level 74, e, τ at next level).

Definition Is_Closed (τ : type) := forall τ', τ.[τ'/] = τ.

Inductive typed (Γ : list type) : expr → type → Prop :=
  | Var_typed x τ : (Γ !! x = Some τ) → Γ ⊢ₜ Var x : τ
  | Unit_typed : Γ ⊢ₜ Unit : TUnit
  | Pair_typed e1 e2 τ1 τ2 :
     Γ ⊢ₜ e1 : τ1 → Γ ⊢ₜ e2 : τ2 → Γ ⊢ₜ Pair e1 e2 : TProd τ1 τ2
  | Fst_typed e τ1 τ2 : Γ ⊢ₜ e : TProd τ1 τ2 → Γ ⊢ₜ Fst e : τ1
  | Snd_typed e τ1 τ2 : Γ ⊢ₜ e : TProd τ1 τ2 → Γ ⊢ₜ Snd e : τ2
  | InjL_typed e τ1 τ2 : Γ ⊢ₜ e : τ1 → Γ ⊢ₜ InjL e : TSum τ1 τ2
  | InjR_typed e τ1 τ2 : Γ ⊢ₜ e : τ2 → Γ ⊢ₜ InjR e : TSum τ1 τ2
  | Case_typed e0 e1 e2 τ1 τ2 ρ :
     Γ ⊢ₜ e0 : TSum τ1 τ2 → τ1 :: Γ ⊢ₜ e1 : ρ → τ2 :: Γ ⊢ₜ e2 : ρ →
     Γ ⊢ₜ Case e0 e1 e2 : ρ
  | Lam_typed e τ1 τ2 : τ1 :: Γ ⊢ₜ e : τ2 → Γ ⊢ₜ Lam e : TArrow τ1 τ2
  | App_typed e1 e2 τ1 τ2 : Γ ⊢ₜ e1 : TArrow τ1 τ2 → Γ ⊢ₜ e2 : τ1 → Γ ⊢ₜ App e1 e2 : τ2
  | Fold_typed e τ : Γ ⊢ₜ e : τ.[TRec τ/] → Γ ⊢ₜ Fold e : TRec τ
  | Unfold_typed e τ : Γ ⊢ₜ e : TRec τ → Γ ⊢ₜ Unfold e : τ.[TRec τ/]
  (* typing for CAST *)
  | Cast_typed e τi τf : Is_Closed τi -> Is_Closed τf -> open_sym τi τf → Γ ⊢ₜ e : τi → Γ ⊢ₜ Cast e τi τf : τf
  (* typing for BLAME *)
  | Blame_typed τ : Is_Closed τ → Γ ⊢ₜ Blame : τ
  (* maybe adjust later to allow... *)
where "Γ ⊢ₜ e : τ" := (typed Γ e τ).

Lemma typed_subst_invariant Γ e τ s1 s2 :
  Γ ⊢ₜ e : τ → (∀ x, x < length Γ → s1 x = s2 x) → e.[s1] = e.[s2].
Proof.
  intros Htyped; revert s1 s2.
  assert (∀ x Γ, x < length (subst (ren (+1)) <$> Γ) → x < length Γ).
  { intros ??. by rewrite fmap_length. }
  assert (∀ {A} `{Ids A} `{Rename A} (s1 s2 : nat → A) x,
    (x ≠ 0 → s1 (pred x) = s2 (pred x)) → up s1 x = up s2 x).
  { intros A H1 H2. rewrite /up=> s1 s2 [|x] //=; auto with f_equal lia. }
  induction Htyped => s1 s2 Hs; f_equal/=; eauto using lookup_lt_Some with lia.
Qed.

Fixpoint env_subst (vs : list val) : var → expr :=
  match vs with
  | [] => ids
  | v :: vs' => #v .: env_subst vs'
  end.

Lemma env_subst_lookup vs x v :
  vs !! x = Some v → env_subst vs x = of_val v.
Proof.
  revert vs; induction x => vs.
  - by destruct vs; inversion 1.
  - destruct vs as [|w vs]; first by inversion 1.
    rewrite -lookup_tail /=.
    apply IHx.
Qed.

Lemma Unfold_typed_help Γ e τ : (τ.[TRec τ/] = τ) → Γ ⊢ₜ e : TRec τ → Γ ⊢ₜ Unfold e : τ.
Proof.
  intros eq d.
  rewrite -eq. by apply Unfold_typed.
Qed.

Lemma Unfold_typed_help_2 Γ e τ τ' : (τ.[TRec τ/] = τ') → Γ ⊢ₜ e : TRec τ → Γ ⊢ₜ Unfold e : τ'.
Proof.
  intros eq d.
  rewrite -eq. by apply Unfold_typed.
Qed.
