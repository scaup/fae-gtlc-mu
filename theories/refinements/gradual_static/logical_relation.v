From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.base_logic Require Export invariants.
From fae_gtlc_mu.backtranslation.cast_help Require Export embed.
From fae_gtlc_mu.refinements Require Export prelude.
From fae_gtlc_mu.refinements.gradual_static Require Export resources_left resources_right.
From fae_gtlc_mu.cast_calculus Require Export types lang.
From iris.algebra Require Import list ofe.
From stdpp Require Import tactics.
Import uPred.

Canonical Structure typeO := leibnizO type.

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
  Context `{!implG Σ, !specG Σ}.
  Notation P := (prodO cast_calculus.lang.valO stlc_mu.lang.valO).
  Notation D := (prodO cast_calculus.lang.valO stlc_mu.lang.valO -n> iPropO Σ).
  Implicit Types τi : D.
  Implicit Types Δ : listO D.

  Definition castupV_TUnit (v : val) : val :=
    (CastV v TUnit ⋆ (TGround_TUnknown_icp Ground_TUnit)).

  Definition castupV_TSum (v : val) : val :=
    (CastV v (TSum ⋆ ⋆) ⋆ (TGround_TUnknown_icp Ground_TSum)).

  Definition castupV_TProd (v : val) : val :=
    (CastV v (TProd ⋆ ⋆) ⋆ (TGround_TUnknown_icp Ground_TProd)).

  Definition castupV_TArrow (v : val) : val :=
    (CastV v (TArrow ⋆ ⋆) ⋆ (TGround_TUnknown_icp Ground_TArrow)).

  Definition castupV_TRec (v : val) : val :=
    (CastV v (TRec ⋆) ⋆ (TGround_TUnknown_icp Ground_TRec)).

  From fae_gtlc_mu.stlc_mu Require Export lang.

  Definition interp_expr (interp_cor_val : P → iPropO Σ)
      (ee : cast_calculus.lang.expr * stlc_mu.lang.expr) : iProp Σ := (∀ K',
    currently_half (fill K' (ee.2)) →
    WP ee.1 ?{{ v, ∃ v', currently_half (fill K' (of_val v')) ∧ interp_cor_val (v, v') }})%I.

  Definition TClosed (τ : type) : Prop := forall σ, τ.[σ] = τ.

  (** only to be used with closed types *)

  Fixpoint interp_gen (Ψ : typeO -n> D) (τ : typeO) (ww : P) : iPropO Σ := (
    match τ with
    | TUnit => ⌜ww.1 = cast_calculus.lang.UnitV⌝ ∧ ⌜ww.2 = stlc_mu.lang.UnitV⌝
    | TProd τ1 τ2 => ∃ v1v1' v2v2', ⌜ww = (cast_calculus.lang.PairV (v1v1'.1) (v2v2'.1), stlc_mu.lang.PairV (v1v1'.2) (v2v2'.2))⌝ ∧
                                  interp_gen Ψ τ1 v1v1' ∧ interp_gen Ψ τ2 v2v2'
    | TSum τ1 τ2 => (∃ vv', ⌜ww = (cast_calculus.lang.InjLV (vv'.1), InjLV (vv'.2))⌝ ∧ interp_gen Ψ τ1 vv') ∨
                    (∃ vv', ⌜ww = (cast_calculus.lang.InjRV (vv'.1), InjRV (vv'.2))⌝ ∧ interp_gen Ψ τ2 vv')
    | TArrow τ1 τ2 => □ ∀ vv, interp_gen Ψ τ1 vv →
             interp_expr
               (interp_gen Ψ τ2) (cast_calculus.lang.App (cast_calculus.lang.of_val (ww.1)) (cast_calculus.lang.of_val (vv.1)),
                        stlc_mu.lang.App (stlc_mu.lang.of_val (ww.2)) (stlc_mu.lang.of_val (vv.2)))
    | TRec τb => □ ∃ w w', ⌜ww = (cast_calculus.lang.FoldV w, stlc_mu.lang.FoldV w')⌝ ∧ ▷ Ψ (τb.[TRec τb/]) (w, w')
    | TUnknown => ∃ v v', □ (
                               (⌜ ww = (castupV_TUnit v , embedV_TUnit v') ⌝                   ∧ ▷ Ψ TUnit (v, v') )
                             ∨ (⌜ ww = (castupV_TProd v, embedV_Ground_TProd v') ⌝            ∧ ▷ Ψ (TProd TUnknown TUnknown) (v , v'))
                             ∨ (⌜ ww = (castupV_TSum v , embedV_Ground_TSum v') ⌝              ∧ ▷ Ψ (TSum TUnknown TUnknown) (v , v'))
                             ∨ (⌜ ww = (castupV_TArrow v , embedV_Ground_TArrow v') ⌝          ∧ ▷ Ψ (TArrow TUnknown TUnknown) (v , v'))
                             ∨ (⌜ ww = (castupV_TRec (cast_calculus.lang.FoldV v), embedV_TUnknown v') ⌝ ∧ ▷ Ψ TUnknown (v , v')
                             (* ∨ (∃ u u', ⌜ ww = (embedV_TUnknown u, castupV_TRec (FoldV u')) ⌝ ∧ ▷ Ψ TUnknown (u , u') *)
                               )
      )
    | TVar x => False (** exfaslo ... *)
    end)%I.

  Program Definition interp_gen_ne (Ψ : typeO -n> D) : typeO -n> D := λne τ p, interp_gen Ψ τ p.
  Solve Obligations with repeat intros ?; simpl; auto_equiv.

  Global Instance interp_gen_ne_contractive : Contractive interp_gen_ne.
  Proof.
    intros n Ψ1 Ψ2  pnΨ τ. simpl.
    induction τ; intro p; simpl.
    - auto.
    - f_equiv. intro p1. f_equiv. intro p2. f_equiv. f_equiv.
      + exact (IHτ1 p1).
      + exact (IHτ2 p2).
    - f_equiv.
      + f_equiv. intro a. f_equiv. exact (IHτ1 a).
      + f_equiv. intro a. f_equiv. exact (IHτ2 a).
    - f_equiv. f_equiv. intro. f_equiv.
      + exact (IHτ1 a).
      + rewrite /interp_expr. simpl. f_equiv. intro K.
        f_equiv. f_equiv. intro v. f_equiv. intro v'.
        f_equiv. exact (IHτ2 (v, v')).
    - solve_contractive.
    - solve_contractive.
    - solve_contractive.
  Qed.

  Definition interp : typeO -n> D := fixpoint interp_gen_ne.

  Notation "⟦ τ ⟧" := (interp τ). (** the actual relations on values *)

  (* boring lemma's related to foldings {{{ *)

  Lemma unfold_interp : interp ≡ interp_gen_ne interp.
  Proof. apply fixpoint_unfold. Qed.

  Lemma unfold_interp_type τ : interp τ ≡ interp_gen_ne interp τ.
  Proof. f_equiv. apply unfold_interp. Qed.

  Lemma unfold_interp_type_pair τ vv : interp τ vv ≡ interp_gen interp τ vv.
  Proof. assert (H : interp_gen interp τ vv ≡ interp_gen_ne interp τ vv). auto_equiv. rewrite H. apply unfold_interp_type. Qed.

  Lemma interp_rw_TUnit ww : interp TUnit ww ≡
    (⌜ww.1 = cast_calculus.lang.UnitV⌝ ∧ ⌜ww.2 = stlc_mu.lang.UnitV⌝)%I.
  Proof. by rewrite (unfold_interp_type_pair TUnit). Qed.

  Lemma interp_rw_TProd τ1 τ2 ww : interp (TProd τ1 τ2) ww ≡
    (∃ v1v1' v2v2', ⌜ww = (cast_calculus.lang.PairV (v1v1'.1) (v2v2'.1), stlc_mu.lang.PairV (v1v1'.2) (v2v2'.2))⌝ ∧
                                  interp τ1 v1v1' ∧ interp τ2 v2v2')%I.
  Proof. rewrite (unfold_interp_type_pair (TProd τ1 τ2)). simpl. auto_equiv; by rewrite -unfold_interp_type_pair. Qed.

  Lemma interp_rw_TSum τ1 τ2 ww : interp (TSum τ1 τ2) ww ≡
    ((∃ vv', ⌜ww = (cast_calculus.lang.InjLV (vv'.1), InjLV (vv'.2))⌝ ∧ interp τ1 vv') ∨
                    (∃ vv', ⌜ww = (cast_calculus.lang.InjRV (vv'.1), InjRV (vv'.2))⌝ ∧ interp τ2 vv'))%I.
  Proof. rewrite (unfold_interp_type_pair (TSum τ1 τ2)). simpl. auto_equiv; by rewrite -unfold_interp_type_pair. Qed.

  Lemma interp_gen_interp_gen_ne Ψ τ ww : interp_gen Ψ τ ww ≡ interp_gen_ne Ψ τ ww.
  Proof. auto. Qed.

  Lemma interp_rw_TArrow τ1 τ2 ww : interp (TArrow τ1 τ2) ww ≡
    (□ ∀ vv, interp τ1 vv →
             interp_expr
               (interp τ2) (cast_calculus.lang.App (cast_calculus.lang.of_val (ww.1)) (cast_calculus.lang.of_val (vv.1)),
                        stlc_mu.lang.App (stlc_mu.lang.of_val (ww.2)) (stlc_mu.lang.of_val (vv.2))))%I.
  Proof. rewrite (unfold_interp_type_pair (TArrow τ1 τ2)). simpl.
         f_equiv. f_equiv.  intro. f_equiv. by rewrite -unfold_interp_type_pair.
         rewrite /interp_expr. auto_equiv. by rewrite unfold_interp_type_pair.
  Qed.

  Lemma interp_rw_TRec τb ww : interp (TRec τb) ww ≡
    (□ ∃ w w', ⌜ww = (cast_calculus.lang.FoldV w, stlc_mu.lang.FoldV w')⌝ ∧ ▷ interp (τb.[TRec τb/]) (w, w'))%I.
  Proof. rewrite (unfold_interp_type_pair). by simpl. Qed.

  Lemma interp_rw_TUnknown ww : interp TUnknown ww ≡
    (∃ v v', □ (
                 (⌜ ww = (castupV_TUnit v , embedV_TUnit v') ⌝                   ∧ ▷ interp TUnit (v, v') )
                 ∨ (⌜ ww = (castupV_TProd v, embedV_Ground_TProd v') ⌝            ∧ ▷ interp (TProd TUnknown TUnknown) (v , v'))
                 ∨ (⌜ ww = (castupV_TSum v , embedV_Ground_TSum v') ⌝              ∧ ▷ interp (TSum TUnknown TUnknown) (v , v'))
                 ∨ (⌜ ww = (castupV_TArrow v , embedV_Ground_TArrow v') ⌝          ∧ ▷ interp (TArrow TUnknown TUnknown) (v , v'))
                 ∨ (⌜ ww = (castupV_TRec (cast_calculus.lang.FoldV v), embedV_TUnknown v') ⌝ ∧ ▷ interp TUnknown (v , v')
                   )
      ))%I.
  Proof. rewrite (unfold_interp_type_pair). by simpl. Qed.

  (* }}} *)

  Global Instance interp_persistent τ vv :
    Persistent (⟦ τ ⟧ vv).
  Proof.
    revert vv. induction τ; intro p; rewrite unfold_interp_type_pair; simpl; try by apply _.
    - apply exist_persistent. intro q. apply exist_persistent. intro r.
      do 2 rewrite -unfold_interp_type_pair. apply _.
    - apply or_persistent; apply exist_persistent; intro q; rewrite -unfold_interp_type_pair; apply _.
  Qed.


  Definition interp_env (Γ : list type)
      (vvs : list (cast_calculus.lang.val * stlc_mu.lang.val)) : iProp Σ :=
    (⌜length Γ = length vvs⌝ ∧ [∧] zip_with (λ τ, ⟦ τ ⟧) Γ vvs)%I.
  Notation "⟦ Γ ⟧*" := (interp_env Γ).

  Global Instance interp_env_base_persistent Γ vs :
  TCForall Persistent (zip_with (λ τ, ⟦ τ ⟧) Γ vs).
  Proof.
    revert vs.
    induction Γ => vs; simpl; destruct vs; constructor; apply _.
  Qed.

  Global Instance interp_env_persistent_help Γ vvs :
    Persistent ([∧] zip_with (λ τ : typeO, ⟦ τ ⟧) Γ vvs).
  Proof.
    rewrite /interp_env.
    revert vvs.
    induction Γ => vs. apply _.
    destruct vs. simpl; apply _.
    simpl; apply _.
  Qed.

   Global Instance interp_env_persistent Γ vvs :
    Persistent (⟦ Γ ⟧* vvs).
  Proof.
    rewrite /interp_env. apply _.
  Qed.

  Lemma interp_env_length Γ vvs : ⟦ Γ ⟧* vvs ⊢ ⌜length Γ = length vvs⌝.
  Proof. by iIntros "[% ?]". Qed.

  Lemma interp_env_Some_l Γ vvs x τ :
    Γ !! x = Some τ → ⟦ Γ ⟧* vvs ⊢ (∃ vv, ⌜vvs !! x = Some vv⌝ ∧ ⟦ τ ⟧ vv).
  Proof.
    iIntros (?) "[Hlen HΓ]"; iDestruct "Hlen" as %Hlen.
    destruct (lookup_lt_is_Some_2 vvs x) as [v Hv].
    { by rewrite -Hlen; apply lookup_lt_Some with τ. }
    iExists v; iSplit. done. iApply (big_andL_elem_of with "HΓ").
    apply elem_of_list_lookup_2 with x.
    rewrite lookup_zip_with; by simplify_option_eq.
  Qed.

  Lemma interp_env_nil : ⊢ ⟦ [] ⟧* [].
  Proof. iSplit; simpl; auto. Qed.
  Lemma interp_env_cons Γ vvs τ vv :
    ⟦ τ :: Γ ⟧* (vv :: vvs) ⊣⊢ ⟦ τ ⟧ vv ∧ ⟦ Γ ⟧* vvs.
  Proof.
    rewrite /interp_env /= (assoc _ (⟦ _ ⟧ _)) -(comm _ ⌜_ = _⌝%I) -assoc.
    by apply and_proper; [apply pure_proper; lia|].
  Qed.

End logrel.

Typeclasses Opaque interp_env.
Notation "⟦ τ ⟧" := (interp τ).
Notation "⟦ τ ⟧ₑ" := (interp_expr (interp τ)).
Notation "⟦ Γ ⟧*" := (interp_env Γ).

From fae_gtlc_mu.stlc_mu Require Export types typing.
From fae_gtlc_mu.cast_calculus Require Export types typing.

Section bin_log_def.
  Context `{!implG Σ, !specG Σ}.
  Notation D := (prodO cast_calculus.lang.valO stlc_mu.lang.valO -n> iProp Σ).

  Definition bin_log_related
  (Γ : list cast_calculus.types.type) (e : cast_calculus.lang.expr) (e' : stlc_mu.lang.expr) (τ : cast_calculus.types.type) :=
    ∀ vvs (ei' : stlc_mu.lang.expr),
    initially_inv ei' ∧ ⟦ Γ ⟧* vvs ⊢
    ⟦ τ ⟧ₑ (e.[cast_calculus.typing.env_subst (vvs.*1)], e'.[stlc_mu.typing.env_subst (vvs.*2)]).
End bin_log_def.
