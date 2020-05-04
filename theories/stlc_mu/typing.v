From Autosubst Require Export Autosubst.
From fae_gtlc_mu Require Export prelude.
From fae_gtlc_mu.stlc_mu Require Export types lang.
From Coq Require Import List.

(* other options {{{

  Disadvantage here; in general we do not have [τ&pτ] = [τ&pτ'] without assuming proof irrelevance..

  Definition ctype := Ssig (fun τ => Squash (TClosed τ)).

  Only allows you to access the closed field in SProp...
  So typed must live in SProp as well.
  When doing induction on typed, we must be in SProp as well... etc.

  Add clause to allow for if Squash τ = τ', then we can interchange...

  Advantage here; works well for type checking; proofs will get shelved..
}}} *)

Reserved Notation "Γ & pΓ ⊢ₛ e : τ & pτ" (at level 74, pΓ, e, τ, pτ at next level).

Inductive typed (Γ : list type) (pΓ : Forall TClosed Γ) : expr → forall (τ : type), TClosed τ → Prop :=
  | Var_typed x τ pτ : (Γ !! x = Some τ) → Γ & pΓ ⊢ₛ Var x : τ & pτ
  | Unit_typed pu : (Γ & pΓ ⊢ₛ Unit : TUnit & pu)
  | Pair_typed e1 e2 τ1 pτ1 τ2 pτ2 pτ12 :
      Γ & pΓ ⊢ₛ e1 : τ1&pτ1 →
      Γ & pΓ ⊢ₛ e2 : τ2&pτ2 →
      Γ & pΓ ⊢ₛ Pair e1 e2 : TProd τ1 τ2 & pτ12
  | Fst_typed e τ1 pτ1 τ2 pτ12 :
      Γ & pΓ ⊢ₛ e : TProd τ1 τ2 & pτ12 →
      Γ & pΓ ⊢ₛ Fst e : τ1 & pτ1
  | Snd_typed e τ1 τ2 pτ2 pτ12 :
      Γ & pΓ ⊢ₛ e : TProd τ1 τ2 & pτ12 →
      Γ & pΓ ⊢ₛ Snd e : τ2 & pτ2
  | InjL_typed e τ1 pτ1 τ2 pτ12 :
      Γ & pΓ ⊢ₛ e : τ1&pτ1 →
      Γ & pΓ ⊢ₛ InjL e : TSum τ1 τ2 & pτ12
  | InjR_typed e τ1 τ2 pτ2 pτ12 :
      Γ & pΓ ⊢ₛ e : τ2 & pτ2 →
      Γ & pΓ ⊢ₛ InjR e : TSum τ1 τ2 & pτ12
  | Case_typed e0 e1 e2 τ1 pτ1 τ2 pτ2 pτ12 τ pτ :
      Γ & pΓ ⊢ₛ e0 : TSum τ1 τ2 & pτ12 →
      τ1 :: Γ & (Forall_cons _ _ _ pτ1 pΓ) ⊢ₛ e1 : τ & pτ →
      τ2 :: Γ & (Forall_cons _ _ _ pτ2 pΓ) ⊢ₛ e2 : τ & pτ →
      Γ & pΓ ⊢ₛ Case e0 e1 e2 : τ & pτ
  | Lam_typed e τ1 pτ1 τ2 pτ2 pτ12 :
      τ1 :: Γ & (Forall_cons _ _ _ pτ1 pΓ) ⊢ₛ e : τ2 & pτ2 →
      Γ & pΓ ⊢ₛ Lam e : TArrow τ1 τ2 & pτ12
  | App_typed e1 e2 τ1 pτ1 τ2 pτ2 pτ12 :
      Γ & pΓ ⊢ₛ e1 : TArrow τ1 τ2 & pτ12 →
      Γ & pΓ ⊢ₛ e2 : τ1 & pτ1 →
      Γ & pΓ ⊢ₛ App e1 e2 : τ2 & pτ2
  | Fold_typed e τb pτbμτb pμτb :
      Γ & pΓ ⊢ₛ e : τb.[TRec τb/] & pτbμτb →
      Γ & pΓ ⊢ₛ Fold e : TRec τb & pμτb
  | Unfold_typed e τb pμτb pτbμτb :
      Γ & pΓ ⊢ₛ e : TRec τb & pμτb →
      Γ & pΓ ⊢ₛ Unfold e : τb.[TRec τb/] & pτbμτb
where "Γ & pΓ ⊢ₛ e : τ & pτ" := (typed Γ pΓ e τ pτ).

(* helper lemma's {{{ *)

Lemma PI_typed Γ pΓ e τ pτ pτ' : Γ & pΓ ⊢ₛ e : τ & pτ → Γ & pΓ ⊢ₛ e : τ & pτ'.
Proof. intro H. induction H; by econstructor. Qed.

Lemma PI_Γ_typed Γ pΓ pΓ' e τ pτ : Γ & pΓ ⊢ₛ e : τ & pτ → Γ & pΓ' ⊢ₛ e : τ & pτ.
Proof.
  intro H. induction H; by econstructor.
  Unshelve. auto. auto. auto.
Qed.

Lemma PI_Γ_typed' Γ pΓ' e τ pτ : forall pΓ, Γ & pΓ ⊢ₛ e : τ & pτ → Γ & pΓ' ⊢ₛ e : τ & pτ.
Proof. intros pΓ H. by eapply PI_Γ_typed. Qed.

Lemma Unfold_Fold_typed Γ pΓ e τ pτ :
  Γ & pΓ ⊢ₛ e : τ & pτ → Γ & pΓ ⊢ₛ Unfold (Fold e) : τ & pτ.
Proof.
  intro.
  assert (eq : τ = τ.[TRec τ/]). by rewrite pτ. generalize pτ. rewrite eq. intro pτμτ.
  assert (pμτ : TClosed (TRec τ)). intro σ. asimpl. by rewrite pτ.
  apply Unfold_typed with (pμτb := pμτ).
  apply Fold_typed with (pτbμτb := pτμτ).
  generalize pτμτ. rewrite -eq. intro pτ'.
  by eapply PI_typed.
Qed.

Lemma Unfold_typed_help Γ pΓ e τb μτb τ' pτ' : (τb.[TRec τb/] = τ') →
  Γ & pΓ ⊢ₛ e : (TRec τb) & μτb →
  Γ & pΓ ⊢ₛ Unfold e : τ' & pτ'.
Proof.
  intros eq d.
  generalize pτ'. rewrite -eq. intro pτ. eapply Unfold_typed.
  by eapply PI_typed.
  Unshelve. auto.
Qed.

Lemma rewrite_typed {Γ pΓ e τ pτ τ' pτ'} :
  Γ & pΓ ⊢ₛ e : τ & pτ → τ = τ' → Γ & pΓ ⊢ₛ e : τ' & pτ'.
Proof.
  intros P eq.
  generalize pτ'. rewrite -eq.
  intro. by eapply PI_typed.
Qed.

(* }}} *)

(* lemma's about substs in terms {{{ *)

Lemma typed_subst_invariant Γ pΓ e τ pτ s1 s2 :
  Γ & pΓ ⊢ₛ e : τ & pτ → (∀ x, x < length Γ → s1 x = s2 x) → e.[s1] = e.[s2].
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

Lemma typed_n_closed Γ pΓ τ pτ e : Γ & pΓ ⊢ₛ e : τ & pτ → (∀ f, e.[upn (length Γ) f] = e).
Proof.
  intros H. induction H => f; asimpl; simpl in *; auto with f_equal.
  apply lookup_lt_Some in H. rewrite iter_up. destruct lt_dec; auto with lia.
Qed.

Lemma n_closed_invariant n (e : expr) s1 s2 :
  (∀ f, e.[upn n f] = e) → (∀ x, x < n → s1 x = s2 x) → e.[s1] = e.[s2].
Proof.
  intros Hnc. specialize (Hnc (ren (+1))).
  revert n Hnc s1 s2.
  induction e => m Hmc s1 s2 H1; asimpl in *; try f_equal;
    try (match goal with H : _ |- _ => eapply H end; eauto;
         try inversion Hmc; try match goal with H : _ |- _ => by rewrite H end;
         fail).
  - apply H1. rewrite iter_up in Hmc. destruct lt_dec; try lia.
    asimpl in *. injection Hmc as Hmc. unfold var in *. omega.
  - unfold upn in *.
    change (e.[up (upn m (ren (+1)))]) with
    (e.[iter (S m) up (ren (+1))]) in *.
    apply (IHe (S m)).
    + inversion Hmc; match goal with H : _ |- _ => (by rewrite H) end.
    + intros [|[|x]] H2; [by cbv| |].
      asimpl; rewrite H1; auto with lia.
      asimpl; rewrite H1; auto with lia.
  - change (e1.[up (upn m (ren (+1)))]) with
    (e1.[iter (S m) up (ren (+1))]) in *.
    apply (IHe0 (S m)).
    + inversion Hmc; match goal with H : _ |- _ => (by rewrite H) end.
    + intros [|x] H2; [by cbv |].
      asimpl; rewrite H1; auto with lia.
  - change (e2.[up (upn m (ren (+1)))]) with
    (e2.[upn (S m) (ren (+1))]) in *.
    apply (IHe1 (S m)).
    + inversion Hmc; match goal with H : _ |- _ => (by rewrite H) end.
    + intros [|x] H2; [by cbv |].
      asimpl; rewrite H1; auto with lia.
Qed.

(** Weakening *)
Lemma context_gen_weakening ξ Γ' Γ α β e τ pτ :
  Γ' ++ Γ & α ⊢ₛ e : τ & pτ →
  Γ' ++ ξ ++ Γ & β ⊢ₛ e.[upn (length Γ') (ren (+ (length ξ)))] : τ & pτ.
Proof.
  intros H1.
  remember (Γ' ++ Γ) as Ξ. revert β. revert Γ' Γ ξ HeqΞ.
  induction H1 => Γ1 Γ2 ξ HeqΞ; subst; asimpl in *; eauto using typed.
  - rewrite iter_up; destruct lt_dec as [Hl | Hl].
    + eapply Var_typed. rewrite lookup_app_l; trivial. by rewrite lookup_app_l in H.
    + asimpl. eapply Var_typed. rewrite lookup_app_r; auto with lia.
      rewrite lookup_app_r; auto with lia.
      rewrite lookup_app_r in H; auto with lia.
      match goal with
        |- _ !! ?A = _ => by replace A with (x - length Γ1) by lia
      end.
  - econstructor; eauto. by apply (IHtyped2 (_::_)). by apply (IHtyped3 (_::_)).
  - eapply Lam_typed. by apply (IHtyped (_ :: _)).
    Unshelve. auto. auto. auto.
Qed.

Lemma context_weakening ξ Γ pΓ α e τ pτ :
  Γ & pΓ ⊢ₛ e : τ & pτ → ξ ++ Γ & α ⊢ₛ e.[(ren (+ (length ξ)))] : τ & pτ.
Proof. eapply (context_gen_weakening _ []). Qed.

Lemma up_type i Γ pΓ e τ pτ Γ' α : (length Γ' = i) -> (Γ & pΓ ⊢ₛ e : τ & pτ) -> (Γ' ++ Γ) & α ⊢ₛ e.[ren (+i)] : τ & pτ.
Proof.
  intros.
  simplify_eq.
  by eapply context_weakening.
Qed.

Lemma up_type_one Γ pΓ e τ pτ τ' pτ' :
  (Γ & pΓ ⊢ₛ e : τ & pτ) ->
  ((τ' :: Γ) & (List.Forall_cons TClosed _ _ pτ' pΓ) ⊢ₛ e.[ren (+1)] : τ & pτ).
Proof.
  intro.
  assert (T : τ' :: Γ = [τ'] ++ Γ). done. generalize (Forall_cons TClosed τ' Γ pτ' pΓ). rewrite T. intro α'.
  by eapply up_type.
Qed.

Lemma up_type_two Γ pΓ e τ pτ τ' τ'' α :
  (Γ & pΓ ⊢ₛ e : τ & pτ) ->
  τ' :: τ'' :: Γ & α ⊢ₛ e.[ren (+2)] : τ & pτ.
Proof.
  intros.
  assert (T : τ' :: τ'' :: Γ = [τ' ; τ''] ++ Γ). done. generalize α. rewrite T. intro.
  by eapply up_type.
Qed.

Lemma EClosed_typed e τ pτ :
  EClosed e → ([] & (Forall_nil TClosed) ⊢ₛ e : τ & pτ) → forall Γ pΓ, Γ & pΓ ⊢ₛ e : τ & pτ.
Proof.
  intros pe H Γ pΓ.
  cut (forall α, Γ ++ [] & α ⊢ₛ e.[(ren (+ (length Γ)))]: τ & pτ).
  by rewrite app_nil_r pe. intro. eapply context_weakening.
  apply H.
Qed.

(* }}} *)
