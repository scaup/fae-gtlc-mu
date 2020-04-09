From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.base_logic Require Export invariants.
From fae_gtlc_mu.backtranslation.cast_help Require Export embed.
From fae_gtlc_mu.refinements Require Export prelude.
From fae_gtlc_mu.refinements.static_gradual Require Export resources_left resources_right.
From fae_gtlc_mu.cast_calculus Require Export types.
From iris.algebra Require Import list.
From stdpp Require Import tactics.
Import uPred.

(* Definition exprO := stlc_mu.lang.expr. *)
(* Definition exprO' := cast_calculus.lang.expr. *)

(* Definition valO := stlc_mu.lang.valO. *)
(* Definition valO' := cast_calculus.lang.valO'. *)

(* Coercion stlc_mu.lang.of_val : stlc_mu.lang.val >-> stlc_mu.lang.expr. *)
(* Coercion cast_calculus.lang.of_val : cast_calculus.lang.val >-> cast_calculus.lang.expr. *)

(* HACK: move somewhere else *)
Ltac auto_equiv :=
  (* Deal with "pointwise_relation" *)
  repeat lazymatch goal with
  | |- pointwise_relation _ _ _ _ => intros ?
  end;
  (* Normalize away equalities. *)
  repeat match goal with
  | H : _ ≡{_}≡ _ |-  _ => apply (discrete_iff _ _) in H
  | _ => progress simplify_eq
  end;
  (* repeatedly apply congruence lemmas and use the equalities in the hypotheses. *)
  try (f_equiv; fast_done || auto_equiv).

Definition logN : namespace := nroot .@ "logN".

(** interp : is a binary logical relation. *)
Section logrel.
  Context `{!heapG Σ, !gradRN Σ}.
  Notation D := (prodO stlc_mu.lang.valO cast_calculus.lang.valO -n> iPropO Σ).
  Implicit Types τi : D.
  Implicit Types Δ : listO D.
  (* Implicit Types interp : listO D → D. *)
  Notation RelV := (listO D -n> D). (* value relation on (open) types *)

  (* we get Initially from definition in fundamental_binary *)

  Definition interp_expr (interp_cor_val : RelV) (Δ : listO D)
      (ee : stlc_mu.lang.expr * cast_calculus.lang.expr) : iProp Σ := (∀ K',
    currently_half (fill K' (ee.2)) →
    WP ee.1 {{ v, ∃ v', currently_half (fill K' (of_val v')) ∗ interp_cor_val Δ (v, v') }})%I.
  Global Instance interp_expr_ne n :
    Proper (dist n ==> dist n ==> (=) ==> dist n) interp_expr.
  Proof. solve_proper. Qed.

  Program Definition ctx_lookup (x : var) : RelV := λne Δ,
    from_option id (cconst True)%I (Δ !! x).
  (* defaults to something which is trivially true if not in scope; OK, this will never happen in actual type derivations *)
  Solve Obligations with solve_proper.

  (** For the recursive call to structurally smaller types,
      we will use the names interp, interp1, interp2... *)

  Program Definition interp_unit : RelV := λne Δ ww,
    (⌜ww.1 = stlc_mu.lang.UnitV⌝ ∧ ⌜ww.2 = cast_calculus.lang.UnitV⌝)%I.
  Solve Obligations with solve_proper_alt.

  Program Definition interp_sum
      (interp1 interp2 : RelV) : RelV := λne Δ ww,
    ((∃ vv', ⌜ww = (stlc_mu.lang.InjLV (vv'.1), InjLV (vv'.2))⌝ ∧ interp1 Δ vv') ∨
     (∃ vv', ⌜ww = (stlc_mu.lang.InjRV (vv'.1), InjRV (vv'.2))⌝ ∧ interp2 Δ vv'))%I.
  Solve Obligations with repeat intros ?; simpl; auto_equiv.

  Program Definition interp_prod
      (interp1 interp2 : RelV) : RelV := λne Δ ww,
    (∃ v1v1' v2v2', ⌜ww = (stlc_mu.lang.PairV (v1v1'.1) (v2v2'.1), cast_calculus.lang.PairV (v1v1'.2) (v2v2'.2))⌝ ∧
                interp1 Δ v1v1' ∧ interp2 Δ v2v2')%I.
  Solve Obligations with repeat intros ?; simpl; auto_equiv.

  Program Definition interp_arrow
      (interp1 interp2 : RelV) : RelV := λne Δ ww,
    (□ ∀ vv, interp1 Δ vv →
             interp_expr
               interp2 Δ (stlc_mu.lang.App (stlc_mu.lang.of_val (ww.1)) (stlc_mu.lang.of_val (vv.1)),
                          cast_calculus.lang.App (cast_calculus.lang.of_val (ww.2)) (cast_calculus.lang.of_val (vv.2))))%I.
  Solve Obligations with repeat intros ?; simpl; auto_equiv.

  Program Definition interp_rec1 (* interp_rec1 interp Δ : D → D *)
      (interp : RelV) (Δ : listO D) (μ : D) : D := λne ww,
    (□ ∃ vv, ⌜ww = (stlc_mu.lang.FoldV (vv.1), cast_calculus.lang.FoldV (vv.2))⌝ ∧ ▷ interp (μ :: Δ) vv)%I.
  Solve Obligations with repeat intros ?; simpl; auto_equiv.

  Global Instance interp_rec1_contractive
    (interp : listO D -n> D) (Δ : listO D) : Contractive (interp_rec1 interp Δ).
  Proof. by solve_contractive. Qed.

  Lemma fixpoint_interp_rec1_eq (interp : RelV) Δ x :
    fixpoint (interp_rec1 interp Δ) x ≡ interp_rec1 interp Δ (fixpoint (interp_rec1 interp Δ)) x.
  Proof. exact: (fixpoint_unfold (interp_rec1 interp Δ) x). Qed.

  Lemma fixpoint_interp_rec1_eq2 (interp : RelV) Δ :
    fixpoint (interp_rec1 interp Δ) ≡ interp_rec1 interp Δ (fixpoint (interp_rec1 interp Δ)).
  Proof. exact: (fixpoint_unfold (interp_rec1 interp Δ)). Qed.

  (* Definition interp_rec (interp : RelV) Δ : D := *)
  (*   fixpoint (interp_rec1 interp Δ). *)

  (* Global Instance interp_rec_ne n : Proper (dist (A := RelV) n ==> dist (A := RelV) n) interp_rec. *)


  Program Definition interp_rec (interp : RelV) : RelV := λne Δ,
    fixpoint (interp_rec1 interp Δ).
  Next Obligation.
    intros interp n Δ1 Δ2 HΔ; apply fixpoint_ne => τi ww. solve_proper.
  Qed.

  Global Instance interp_rec_ne n : Proper (dist n ==> dist n) interp_rec.
  Proof.
    repeat intros ?.
    rewrite /interp_rec /=. apply (fixpoint_ne (interp_rec1 _ _)).
    repeat intros ?. unfold interp_rec1.
    simpl.
    auto_equiv.
  Qed.

  (* Unset Printing Notations. *)
  (* Set Printing Implicit. *)
  (* Set Printing Notations. *)
  (* Set Printing Coercions. *)

  (* Unset Printing Notations. *)


  (* Set Printing Implicit. *)
  (* Unset Printing Implicit. *)

  (* Set Printing All. *)

  Definition castupV_TUnit (v : val) : val :=
    (CastV v TUnit ⋆ (From_ground_to_unknown _ Ground_TUnit)).

  Definition castupV_TSum (v : val) : val :=
    (CastV v (TSum ⋆ ⋆) ⋆ (From_ground_to_unknown _ Ground_TSum)).

  Definition castupV_TProd (v : val) : val :=
    (CastV v (TProd ⋆ ⋆) ⋆ (From_ground_to_unknown _ Ground_TProd)).

  Definition castupV_TArrow (v : val) : val :=
    (CastV v (TArrow ⋆ ⋆) ⋆ (From_ground_to_unknown _ Ground_TArrow)).

  Definition castupV_TRec (v : val) : val :=
    (CastV v (TRec ⋆) ⋆ (From_ground_to_unknown _ Ground_TRec)).

  (* interp_unknown1 : RelV -n> RelV *)
  (* Program Definition interp_unknown1 : RelV -n> RelV := λne μR Δ ww', *)
  Program Definition interp_unknown1 : RelV -n> RelV := λne μR Δ ww',
   (□ (
          (∃ vv', ⌜ ww' = (embedV_TUnit (vv'.1) , castupV_TUnit vv'.2) ⌝ ∧
                ▷ interp_unit Δ vv' )
        ∨ (∃ pp', ⌜ ww' = (embedV_Ground_TProd (pp'.1) , castupV_TProd pp'.2) ⌝ ∧
                  ▷ interp_prod μR μR Δ pp')
        ∨ (∃ ss', ⌜ ww' = (embedV_Ground_TSum (ss'.1) , castupV_TSum ss'.2) ⌝ ∧
                  ▷ interp_sum μR μR Δ ss' )
        ∨ (∃ ff', ⌜ ww' = (embedV_Ground_TArrow (ff'.1) , castupV_TArrow ff'.2) ⌝ ∧
                  ▷ interp_arrow μR μR Δ ff' )
        ∨ (∃ ur', ⌜ ww' = (stlc_mu.lang.FoldV (stlc_mu.lang.InjRV (ur'.1)) , castupV_TRec ur'.2) ⌝ ∧
                  ▷ interp_rec μR Δ (stlc_mu.lang.FoldV ur'.1 , ur'.2))
      )
   )%I.
  Next Obligation.
    repeat intros ?; simpl; auto_equiv.
  Qed.
  Next Obligation.
    repeat intros ?.  simpl; auto_equiv.
    change (interp_rec μR x ≡{n}≡ interp_rec μR y). (*note*)
    by f_equiv.
  Qed.
  Next Obligation.
    repeat intros ?; simpl; auto_equiv.
    change (interp_rec x x0 ≡{n}≡ interp_rec y x0). (*not use autogenerated names*)
    f_equiv. by f_equiv.
  Qed.

  Global Instance interp_unknown1_contractive : Contractive (interp_unknown1).
  Proof.
    repeat intros ?.
    unfold interp_unknown1.
    simpl. do 1 f_equiv.
    repeat (f_equiv; first solve_contractive).
    f_equiv. simpl. repeat intros ?.
    f_equiv. f_equiv. intros ?. f_equiv. apply later_contractive.
    destruct n; first done.
    simpl in *. f_equiv.
    intros ?. f_equiv. intros ?. by repeat f_equiv.

    f_equiv. f_equiv. intros ?. f_equiv. apply later_contractive. destruct n; first done. simpl in *. by repeat f_equiv.
    f_equiv. f_equiv. intros ?. f_equiv. apply later_contractive. destruct n; first done. simpl in *. by repeat f_equiv.
    f_equiv. intros ?. f_equiv. apply later_contractive. destruct n; first done. simpl in *.
    f_equiv.
    change (interp_rec x x0 ≡{n}≡ interp_rec y x0). (*not use autogenerated names*)
    by do 2 f_equiv.
  Qed.

  (* Global Instance interp_unknown1_contractive : Contractive (interp_unknown1). *)
  (* Proof. *)
  (*   repeat intros ?. *)
  (*   unfold interp_unknown1. *)
  (*   simpl. do 1 f_equiv. *)
  (*   repeat (f_equiv; first solve_contractive). *)
  (*   f_equiv. simpl. repeat intros ?. *)
  (*   f_equiv. apply later_contractive. *)
  (*   destruct n; first done. *)
  (*   simpl in *. f_equiv. *)
  (*   change (interp_rec x x0 ≡{n}≡ interp_rec y x0). (*not use autogenerated names*) *)
  (*   by do 2 f_equiv. *)
  (* Qed. *)

  Definition interp_unknown : listO D -n> D := fixpoint (interp_unknown1).

  Lemma interp_unknown_unfold Δ vv : interp_unknown Δ vv ≡ interp_unknown1 (fixpoint interp_unknown1) Δ vv.
  Proof.
    f_equiv.
    f_equiv.
    apply fixpoint_unfold.
  Qed.

  Lemma interp_unknown_unfold' Δ : interp_unknown Δ ≡ interp_unknown1 (fixpoint interp_unknown1) Δ.
  Proof.
    f_equiv.
    apply fixpoint_unfold.
  Qed.

  (** Redefine it so it is more trivially contractive and independent from Δ *)
  (** Also do some unfolding in the meantime..; will make it easier *)
  Program Definition interp_unknown1' : D -n> D := λne μRc ww',
   (□ (
        (⌜ ww' = (embedV_TUnit (stlc_mu.lang.UnitV) , castupV_TUnit UnitV) ⌝)

      ∨ (∃ v1 v1' v2 v2', ⌜ ww' = (embedV_Ground_TProd (stlc_mu.lang.PairV v1 v2) , castupV_TProd (PairV v1' v2')) ⌝ ∧ (▷ μRc (v1, v1')) ∧ (▷ μRc (v2, v2'))
        )

      ∨ ((∃ v1 v1', ⌜ ww' = (embedV_Ground_TSum (stlc_mu.lang.InjLV v1) , castupV_TSum (InjLV v1')) ⌝ ∧ ▷ μRc (v1 , v1')) ∨
         (∃ v2 v2', ⌜ ww' = (embedV_Ground_TSum (stlc_mu.lang.InjRV v2) , castupV_TSum (InjRV v2')) ⌝ ∧ ▷ μRc (v2 , v2'))
        )
      ∨ (∃ f f', ⌜ ww' = (embedV_Ground_TArrow f , castupV_TArrow f') ⌝ ∧
                ▷ □ ( ∀ a  a', μRc (a , a') →
                             ∀ K', currently_half (fill K' (App f' a')) → WP (f a) {{ v , ∃ v', currently_half (fill K' (# v')) ∗ μRc (v , v') }} )
        )
      ∨ (∃ u u', ⌜ ww' = (stlc_mu.lang.FoldV (stlc_mu.lang.InjRV (u)) , castupV_TRec (FoldV u')) ⌝ ∧
                ▷ μRc (u , u')
        )
      )
   )%I.
  Solve Obligations with repeat intros ?; simpl; auto_equiv.

  Global Instance interp_unknown1'_contractive : Contractive (interp_unknown1').
  Proof. by solve_contractive. Qed.

  Definition interp_unknown_pre' : D := fixpoint (interp_unknown1').

  Lemma unfold_fixpoint_interp_unknown1' Δ vv : fixpoint interp_unknown1' vv ≡ interp_unknown1' (fixpoint interp_unknown1') vv.
  Proof.
    f_equiv; apply fixpoint_unfold.
  Qed.

  Program Definition interp_unknown' : listO D -n> D := λne Δ vv, (interp_unknown_pre' vv)%I.
  Solve Obligations with repeat intros ?; simpl; auto_equiv.

  Fixpoint interp (τ : cast_calculus.types.type) : listO D -n> D :=
    match τ return _ with
    | TUnit => interp_unit
    | TProd τ1 τ2 => interp_prod (interp τ1) (interp τ2)
    | TSum τ1 τ2 => interp_sum (interp τ1) (interp τ2)
    | TArrow τ1 τ2 => interp_arrow (interp τ1) (interp τ2)
    | TVar x => ctx_lookup x
    | TRec τ' => interp_rec (interp τ')
    | TUnknown => interp_unknown'
    end.
  Notation "⟦ τ ⟧" := (interp τ). (** the actual relations on values *)

  Definition interp_env (Γ : list type)
      (Δ : listO D) (vvs : list (stlc_mu.lang.val * cast_calculus.lang.val)) : iProp Σ :=
    (⌜length Γ = length vvs⌝ ∗ [∗] zip_with (λ τ, ⟦ τ ⟧ Δ) Γ vvs)%I.
  Notation "⟦ Γ ⟧*" := (interp_env Γ).

  Class env_Persistent Δ :=
    ctx_persistentP : Forall (λ τi, ∀ vv, Persistent (τi vv)) Δ.
  Global Instance ctx_persistent_nil : env_Persistent [].
  Proof. by constructor. Qed.
  Global Instance ctx_persistent_cons τi Δ :
    (∀ vv, Persistent (τi vv)) → env_Persistent Δ → env_Persistent (τi :: Δ).
  Proof. by constructor. Qed.
  Global Instance ctx_persistent_lookup Δ x vv :
    env_Persistent Δ → Persistent (ctx_lookup x Δ vv).
  Proof. intros HΔ; revert x; induction HΔ=>-[|?] /=; apply _. Qed.
  Global Instance interp_persistent τ Δ vv :
    env_Persistent Δ → Persistent (⟦ τ ⟧ Δ vv).
  Proof.
    revert vv Δ; induction τ=> vv Δ HΔ; simpl; try apply _.
    - rewrite /Persistent fixpoint_interp_rec1_eq.
      rewrite /interp_rec1.
      rewrite /= intuitionistically_into_persistently.
      by apply persistently_intro'.
    - rewrite /Persistent /interp_unknown_pre'.
      rewrite unfold_fixpoint_interp_unknown1'.
      rewrite /= intuitionistically_into_persistently.
      apply persistently_intro'.
      done. done.
  Qed.

  Global Instance interp_env_base_persistent Δ Γ vs :
  env_Persistent Δ → TCForall Persistent (zip_with (λ τ, ⟦ τ ⟧ Δ) Γ vs).
  Proof.
    intros HΔ. revert vs.
    induction Γ => vs; simpl; destruct vs; constructor; apply _.
  Qed.
  Global Instance interp_env_persistent Γ Δ vvs :
    env_Persistent Δ → Persistent (⟦ Γ ⟧* Δ vvs) := _.

  Lemma interp_weaken Δ1 Π Δ2 τ :
    ⟦ τ.[upn (length Δ1) (ren (+ length Π))] ⟧ (Δ1 ++ Π ++ Δ2)
    ≡ ⟦ τ ⟧ (Δ1 ++ Δ2).
  Proof.
    revert Δ1 Π Δ2. induction τ=> Δ1 Π Δ2; simpl; auto.
    - intros ww; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - intros ww; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - unfold interp_expr.
      intros ww; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - apply fixpoint_proper=> τi ww /=.
      properness; auto. apply (IHτ (_ :: _)).
    - rewrite iter_up; destruct lt_dec as [Hl | Hl]; simpl.
      { by rewrite !lookup_app_l. }
      (* FIXME: Ideally we wouldn't have to do this kinf of surgery. *)
      change (bi_ofeO (uPredI (iResUR Σ))) with (uPredO (iResUR Σ)).
      rewrite !lookup_app_r; [|lia ..]. do 2 f_equiv. lia.
  Qed.

  Lemma interp_subst_up Δ1 Δ2 τ τ' :
    ⟦ τ ⟧ (Δ1 ++ interp τ' Δ2 :: Δ2)
    ≡ ⟦ τ.[upn (length Δ1) (τ' .: ids)] ⟧ (Δ1 ++ Δ2).
  Proof.
    revert Δ1 Δ2; induction τ=> Δ1 Δ2; simpl; auto.
    - intros ww; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - intros ww; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - unfold interp_expr.
      intros ww; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - apply fixpoint_proper=> τi ww /=.
      properness; auto. apply (IHτ (_ :: _)).
    - rewrite iter_up; destruct lt_dec as [Hl | Hl]; simpl.
      { by rewrite !lookup_app_l. }
      (* FIXME: Ideally we wouldn't have to do this kinf of surgery. *)
      change (bi_ofeO (uPredI (iResUR Σ))) with (uPredO (iResUR Σ)).
      rewrite !lookup_app_r; [|lia ..].
      case EQ: (x - length Δ1) => [|n]; simpl.
      { symmetry. asimpl. apply (interp_weaken [] Δ1 Δ2 τ'). }
      change (bi_ofeO (uPredI (iResUR Σ))) with (uPredO (iResUR Σ)).
      rewrite !lookup_app_r; [|lia ..]. do 2 f_equiv. lia.
  Qed.

  Lemma interp_subst Δ2 τ τ' v : ⟦ τ ⟧ (⟦ τ' ⟧ Δ2 :: Δ2) v ≡ ⟦ τ.[τ'/] ⟧ Δ2 v.
  Proof. apply (interp_subst_up []). Qed.

  Lemma interp_env_length Δ Γ vvs : bi_entails (⟦ Γ ⟧* Δ vvs) (⌜length Γ = length vvs⌝).
  Proof. by iIntros "[% ?]". Qed.

  Lemma interp_env_Some_l Δ Γ vvs x τ :
    Γ !! x = Some τ → bi_entails (⟦ Γ ⟧* Δ vvs) (∃ vv, ⌜vvs !! x = Some vv⌝ ∧ ⟦ τ ⟧ Δ vv).
  Proof.
    iIntros (?) "[Hlen HΓ]"; iDestruct "Hlen" as %Hlen.
    destruct (lookup_lt_is_Some_2 vvs x) as [v Hv].
    { by rewrite -Hlen; apply lookup_lt_Some with τ. }
    iExists v; iSplit. done. iApply (big_sepL_elem_of with "HΓ").
    apply elem_of_list_lookup_2 with x.
    rewrite lookup_zip_with; by simplify_option_eq.
  Qed.

  Lemma interp_env_nil Δ : ⊢ ⟦ [] ⟧* Δ [].
  Proof. iSplit; simpl; auto. Qed.
  Lemma interp_env_cons Δ Γ vvs τ vv :
    ⟦ τ :: Γ ⟧* Δ (vv :: vvs) ⊣⊢ ⟦ τ ⟧ Δ vv ∗ ⟦ Γ ⟧* Δ vvs.
  Proof.
    rewrite /interp_env /= (assoc _ (⟦ _ ⟧ _ _)) -(comm _ ⌜_ = _⌝%I) -assoc.
    by apply sep_proper; [apply pure_proper; lia|].
  Qed.

  Lemma interp_env_ren Δ (Γ : list type) vvs τi :
    ⟦ subst (ren (+1)) <$> Γ ⟧* (τi :: Δ) vvs ⊣⊢ ⟦ Γ ⟧* Δ vvs.
  Proof.
    apply sep_proper; [apply pure_proper; by rewrite fmap_length|].
    revert Δ vvs τi; induction Γ=> Δ [|v vs] τi; csimpl; auto.
    apply sep_proper; auto. apply (interp_weaken [] [τi] Δ).
  Qed.

End logrel.

Typeclasses Opaque interp_env.
Notation "⟦ τ ⟧" := (interp τ).
Notation "⟦ τ ⟧ₑ" := (interp_expr (interp τ)).
Notation "⟦ Γ ⟧*" := (interp_env Γ).

From fae_gtlc_mu.cast_calculus Require Export types typing.

Section bin_log_def.
  Context `{!heapG Σ, !gradRN Σ}.
  Notation D := (prodO stlc_mu.lang.valO cast_calculus.lang.valO -n> iProp Σ).

  Definition bin_log_related
  (Γ : list cast_calculus.types.type) (e : stlc_mu.lang.expr) (e' : cast_calculus.lang.expr) (τ : cast_calculus.types.type) :=
    ∀ Δ vvs (ei' : cast_calculus.lang.expr), env_Persistent Δ →
    initially_inv ei' ∗ ⟦ Γ ⟧* Δ vvs ⊢
    ⟦ τ ⟧ₑ Δ (e.[stlc_mu.typing.env_subst (vvs.*1)], e'.[cast_calculus.typing.env_subst (vvs.*2)]).
End bin_log_def.

