From Autosubst Require Export Autosubst.
From fae_gtlc_mu Require Export prelude.
From fae_gtlc_mu Require Export stlc_mu.lang.

Inductive type :=
  | TUnit : type
  | TProd : type → type → type
  | TSum : type → type → type
  | TArrow : type → type → type
  | TRec (τ : {bind 1 of type})
  | TVar (x : var).

Notation "( τ1 → .. → τm → τn )" := (TArrow τ1 .. (TArrow τm τn) .. ) : type_scope. (* does not work?? *)
Infix "×" := TProd (at level 150) : type_scope.
Infix "+" := TSum : type_scope.
(* Infix "→" := TArrow : type_scope. *)

Instance Ids_type : Ids type. derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.
Instance SubstLemmas_typer : SubstLemmas type. derive. Qed.

Reserved Notation "Γ ⊢ₛ e : τ" (at level 74, e, τ at next level).

Inductive typed (Γ : list type) : expr → type → Prop :=
  | Var_typed x τ : (Γ !! x = Some τ) → Γ ⊢ₛ Var x : τ
  | Unit_typed : Γ ⊢ₛ Unit : TUnit
  | Pair_typed e1 e2 τ1 τ2 :
     Γ ⊢ₛ e1 : τ1 → Γ ⊢ₛ e2 : τ2 → Γ ⊢ₛ Pair e1 e2 : TProd τ1 τ2
  | Fst_typed e τ1 τ2 : Γ ⊢ₛ e : TProd τ1 τ2 → Γ ⊢ₛ Fst e : τ1
  | Snd_typed e τ1 τ2 : Γ ⊢ₛ e : TProd τ1 τ2 → Γ ⊢ₛ Snd e : τ2
  | InjL_typed e τ1 τ2 : Γ ⊢ₛ e : τ1 → Γ ⊢ₛ InjL e : TSum τ1 τ2
  | InjR_typed e τ1 τ2 : Γ ⊢ₛ e : τ2 → Γ ⊢ₛ InjR e : TSum τ1 τ2
  | Case_typed e0 e1 e2 τ1 τ2 ρ :
     Γ ⊢ₛ e0 : TSum τ1 τ2 → τ1 :: Γ ⊢ₛ e1 : ρ → τ2 :: Γ ⊢ₛ e2 : ρ →
     Γ ⊢ₛ Case e0 e1 e2 : ρ
  | Lam_typed e τ1 τ2 : τ1 :: Γ ⊢ₛ e : τ2 → Γ ⊢ₛ Lam e : TArrow τ1 τ2
  | App_typed e1 e2 τ1 τ2 : Γ ⊢ₛ e1 : TArrow τ1 τ2 → Γ ⊢ₛ e2 : τ1 → Γ ⊢ₛ App e1 e2 : τ2
  | Fold_typed e τ : Γ ⊢ₛ e : τ.[TRec τ/] → Γ ⊢ₛ Fold e : TRec τ
  | Unfold_typed e τ : Γ ⊢ₛ e : TRec τ → Γ ⊢ₛ Unfold e : τ.[TRec τ/]
where "Γ ⊢ₛ e : τ" := (typed Γ e τ).

Lemma typed_subst_invariant Γ e τ s1 s2 :
  Γ ⊢ₛ e : τ → (∀ x, x < length Γ → s1 x = s2 x) → e.[s1] = e.[s2].
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

Lemma Unfold_typed_help Γ e τ : (τ.[TRec τ/] = τ) → Γ ⊢ₛ e : TRec τ → Γ ⊢ₛ Unfold e : τ.
Proof.
  intros eq d.
  rewrite -eq. by apply Unfold_typed.
Qed.

Lemma Unfold_typed_help_2 Γ e τ τ' : (τ.[TRec τ/] = τ') → Γ ⊢ₛ e : TRec τ → Γ ⊢ₛ Unfold e : τ'.
Proof.
  intros eq d.
  rewrite -eq. by apply Unfold_typed.
Qed.
