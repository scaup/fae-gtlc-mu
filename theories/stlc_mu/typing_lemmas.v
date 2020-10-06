From fae_gtlc_mu.stlc_mu Require Export typing.

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

Lemma typed_n_closed Γ τ e : Γ ⊢ₛ e : τ → (∀ f, e.[upn (length Γ) f] = e).
Proof.
  intros H. induction H => f; asimpl; simpl in *; auto with f_equal.
  apply lookup_lt_Some in H. rewrite iter_up. destruct lt_dec; auto with lia.
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
Lemma context_gen_weakening ξ Γ' Γ e τ :
  Γ' ++ Γ ⊢ₛ e : τ →
  Γ' ++ ξ ++ Γ ⊢ₛ e.[upn (length Γ') (ren (+ (length ξ)))] : τ.
Proof.
  intros H1.
  remember (Γ' ++ Γ) as Ξ. revert Γ' Γ ξ HeqΞ.
  induction H1 => Γ1 Γ2 ξ HeqΞ; subst; asimpl in *; eauto using typed.
  - rewrite iter_up; destruct lt_dec as [Hl | Hl].
    + constructor. auto. rewrite lookup_app_l; trivial. by rewrite lookup_app_l in H.
    + asimpl. constructor. auto. rewrite lookup_app_r; auto with lia.
      rewrite lookup_app_r; auto with lia.
      rewrite lookup_app_r in H; auto with lia.
      match goal with
        |- _ !! ?A = _ => by replace A with (x - length Γ1) by lia
      end.
  - econstructor; eauto. by apply (IHtyped2 (_::_)). by apply (IHtyped3 (_::_)).
  - constructor. auto. by apply (IHtyped (_ :: _)).
Qed.

Lemma context_weakening ξ Γ e τ :
  Γ ⊢ₛ e : τ → ξ ++ Γ ⊢ₛ e.[(ren (+ (length ξ)))] : τ.
Proof. eapply (context_gen_weakening _ []). Qed.

(* Lemma context_gen_reorder Γ'' Γ' Γ τ1 τ2 τe τ : *)
  (* Γ'' ++ [τ1] ++ Γ' ++ [τ2] ++ Γ ⊢ₛ e : τ → *)
  (* Γ'' ++ [τ2] ++ Γ' ++ [τ1] ++ Γ' ⊢ₛ e.[upn (length Γ') (ren (+ (length ξ)))] : τ. *)

Lemma closed_context_weakening ξ Γ e τ :
  (∀ f, e.[f] = e) → Γ ⊢ₛ e : τ → ξ ++ Γ ⊢ₛ e : τ.
Proof. intros H1 H2. erewrite <- H1. by eapply context_weakening. Qed.

Lemma up_type i Γ e τ Γ' : (length Γ' = i) -> (Γ ⊢ₛ e : τ) -> (Γ' ++ Γ) ⊢ₛ e.[ren (+i)] : τ.
Proof. intros. simplify_eq. by apply context_weakening. Qed.

Lemma up_type_one Γ e τ τ' : (Γ ⊢ₛ e : τ) -> τ' :: Γ ⊢ₛ e.[ren (+1)] : τ.
Proof. intro. assert (T : τ' :: Γ = [τ'] ++ Γ). done. rewrite T. by apply up_type. Qed.

Lemma up_type_two Γ e τ τ' τ'' : (Γ ⊢ₛ e : τ) -> τ' :: τ'' :: Γ ⊢ₛ e.[ren (+2)] : τ.
Proof. intros. assert (T : τ' :: τ'' :: Γ = [τ' ; τ''] ++ Γ). done. rewrite T. by apply up_type. Qed.

Lemma EClosed_typed (e : expr) τ :
  Closed e → ([] ⊢ₛ e : τ) → forall Γ, (Γ ⊢ₛ e : τ).
Proof.
  intros ec H Γ.
  cut (Γ ++ [] ⊢ₛ e.[(ren (+ (length Γ)))]: τ).
  rewrite app_nil_r. by rewrite ec. by eapply context_weakening.
Qed.
