From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.base_logic Require Export invariants.
From fae_gtlc_mu.backtranslation.cast_help Require Export embed.
From fae_gtlc_mu.refinements Require Export prelude.
From fae_gtlc_mu.refinements.static_gradual Require Export resources_left resources_right.
From fae_gtlc_mu.cast_calculus Require Export types.
From iris.algebra Require Import list ofe.
From stdpp Require Import tactics.
Import uPred.

(* Definition exprO := stlc_mu.lang.expr. *)
(* Definition exprO' := cast_calculus.lang.expr. *)

(* Definition valO := stlc_mu.lang.valO. *)
(* Definition valO' := cast_calculus.lang.valO'. *)

(* Coercion stlc_mu.lang.of_val : stlc_mu.lang.val >-> stlc_mu.lang.expr. *)
(* Coercion cast_calculus.lang.of_val : cast_calculus.lang.val >-> cast_calculus.lang.expr. *)

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
  Notation P := (prodO stlc_mu.lang.valO cast_calculus.lang.valO).
  Notation D := (prodO stlc_mu.lang.valO cast_calculus.lang.valO -n> iPropO Σ).
  Implicit Types τi : D.
  Implicit Types Δ : listO D.
  (* Implicit Types interp : listO D → D. *)
  (* Notation RelV := (listO D -n> D). (* value relation on (open) types *) *)

  (* we get Initially from definition in fundamental_binary *)

  (* Definition interp_expr (interp_cor_val : D) *)
  (*     (ee : stlc_mu.lang.expr * cast_calculus.lang.expr) : iProp Σ := (∀ K', *)
  (*   currently_half (fill K' (ee.2)) → *)
  (*   WP ee.1 {{ v, ∃ v', currently_half (fill K' (of_val v')) ∗ interp_cor_val (v, v') }})%I. *)
  (* Global Instance interp_expr_ne n : *)
  (*   Proper (dist n ==> (=) ==> dist n) interp_expr. *)
  (* Proof. solve_proper. Qed. *)

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

  (* we can completely separate this definition... *)


  (* Program Definition interp_unknown : D -n> D := λne Ψ vv', *)
  (*  (□ ( *)
  (*       (⌜ vv' = (embedV_TUnit (stlc_mu.lang.UnitV) , castupV_TUnit UnitV) ⌝) *)

  (*     ∨ (∃ v1 v1' v2 v2', ⌜ vv' = (embedV_Ground_TProd (stlc_mu.lang.PairV v1 v2) , castupV_TProd (PairV v1' v2')) ⌝ ∧ (▷ Ψ (v1, v1')) ∧ (▷ Ψ (v2, v2')) *)
  (*       ) *)

  (*     ∨ ((∃ v1 v1', ⌜ vv' = (embedV_Ground_TSum (stlc_mu.lang.InjLV v1) , castupV_TSum (InjLV v1')) ⌝ ∧ ▷ Ψ (v1 , v1')) ∨ *)
  (*        (∃ v2 v2', ⌜ vv' = (embedV_Ground_TSum (stlc_mu.lang.InjRV v2) , castupV_TSum (InjRV v2')) ⌝ ∧ ▷ Ψ (v2 , v2')) *)
  (*       ) *)
  (*     ∨ (∃ f f', ⌜ vv' = (embedV_Ground_TArrow f , castupV_TArrow f') ⌝ ∧ *)
  (*               ▷ □ ( ∀ a  a', Ψ (a , a') → *)
  (*                            ∀ K', currently_half (fill K' (App f' a')) → WP (f a) {{ v , ∃ v', currently_half (fill K' (# v')) ∗ Ψ (v , v') }} ) *)
  (*       ) *)
  (*     ∨ (∃ u u', ⌜ vv' = (embedV_TUnknown u, castupV_TRec (FoldV u')) ⌝ ∧ *)
  (*               ▷ Ψ (u , u') *)
  (*       ) *)
  (*     ) *)
  (*  )%I. *)
  (* Solve Obligations with repeat intros ?; simpl; auto_equiv. *)

  (* Why not define interp_gen (Ψ : typeO -n> D) directly of type typeO -n-> D ? *)
  (* recursion needs to be on type... work *) (* {{{ *)

  (* Program Fixpoint interp_gen (Ψ : typeO -n> D) : typeO -n> D := λne τ, (** almost there *) *)
  (*   match τ with *)
  (*   | TUnit => interp_unit *)
  (*   | TProd τ1 τ2 => interp_prod (interp_gen Ψ τ1) (interp_gen Ψ τ2) *)
  (*   | TSum τ1 τ2 => interp_sum (interp_gen Ψ τ1) (interp_gen Ψ τ2) *)
  (*   | TArrow τ1 τ2 => interp_arrow (interp_gen Ψ τ1) (interp_gen Ψ τ2) *)
  (*   | TRec τb => Ψ τb.[TRec τb/] *)
  (*   (* | TVar x => interp_unit *) *)
  (*   (* | TUnknown => interp_unknown (Ψ TUnknown) *) *)
  (*   | _ => interp_unit *)
  (*   end. *)

   (* }}} *)

  (* Ok, so we define it as follows, but then it will be harder to define correctly; i.e., inserting the right ▷ *)
  (* {{{
  Fixpoint interp_gen (Ψ : typeO -n> D) (τ : typeO) : D := (** almost there *)
    match τ with
    | TUnit => interp_unit
    | TProd τ1 τ2 => interp_prod (interp_gen Ψ τ1) (interp_gen Ψ τ2)
    | TSum τ1 τ2 => interp_sum (interp_gen Ψ τ1) (interp_gen Ψ τ2)
    | TArrow τ1 τ2 => interp_arrow (interp_gen Ψ τ1) (interp_gen Ψ τ2)
    | TRec τb => Ψ τb.[TRec τb/]
    (* | TVar x => interp_unit *)
    (* | TUnknown => interp_unknown (Ψ TUnknown) *)
    | _ => interp_unit
    end. }}} *)

  Definition interp_expr (interp_cor_val : P → iPropO Σ)
      (ee : stlc_mu.lang.expr * cast_calculus.lang.expr) : iProp Σ := (∀ K',
    currently_half (fill K' (ee.2)) →
    WP ee.1 {{ v, ∃ v', currently_half (fill K' (of_val v')) ∗ interp_cor_val (v, v') }})%I.
  (* Global Instance interp_expr_ne n : *)
    (* Proper (dist n ==> (=) ==> dist n) interp_expr'. *)
  (* Proof. solve_proper. Qed. *)

  (* Definition interp_expr'' (interp_cor_val : P -n> iPropO Σ) (ee : prod stlc_mu.lang.expr cast_calculus.lang.expr) : iProp Σ := interp_expr' interp_cor_val ee. *)

  Definition TClosed (τ : type) : Prop := forall σ, τ.[σ] = τ.

  Fixpoint interp_gen (Ψ : typeO -n> D) (τ : typeO) (ww : P) : iPropO Σ := (
    match τ with
    | TUnit => ⌜ww.1 = stlc_mu.lang.UnitV⌝ ∧ ⌜ww.2 = cast_calculus.lang.UnitV⌝
    | TProd τ1 τ2 => (∃ vv', ⌜ww = (stlc_mu.lang.InjLV (vv'.1), InjLV (vv'.2))⌝ ∧ interp_gen Ψ τ1 vv') ∨
                    (∃ vv', ⌜ww = (stlc_mu.lang.InjRV (vv'.1), InjRV (vv'.2))⌝ ∧ interp_gen Ψ τ2 vv')
    | TSum τ1 τ2 => ∃ v1v1' v2v2', ⌜ww = (stlc_mu.lang.PairV (v1v1'.1) (v2v2'.1), cast_calculus.lang.PairV (v1v1'.2) (v2v2'.2))⌝ ∧
                                  interp_gen Ψ τ1 v1v1' ∧ interp_gen Ψ τ2 v2v2'
    | TArrow τ1 τ2 => □ ∀ vv, interp_gen Ψ τ1 vv →
             interp_expr
               (interp_gen Ψ τ2) (stlc_mu.lang.App (stlc_mu.lang.of_val (ww.1)) (stlc_mu.lang.of_val (vv.1)),
                        cast_calculus.lang.App (cast_calculus.lang.of_val (ww.2)) (cast_calculus.lang.of_val (vv.2)))
    | TRec τb => □ ∃ w w', ⌜ww = (stlc_mu.lang.FoldV w, cast_calculus.lang.FoldV w')⌝ ∧ ▷ Ψ (τb.[TRec τb/]) (w, w')
    | TUnknown => ∃ v v', □ (
                               (⌜ ww = (embedV_TUnit v , castupV_TUnit v') ⌝                   ∧ ▷ Ψ TUnit (v, v') )
                             ∨ (⌜ ww = (embedV_Ground_TProd v , castupV_TProd v') ⌝            ∧ ▷ Ψ (TProd TUnknown TUnknown) (v , v'))
                             ∨ (⌜ ww = (embedV_Ground_TSum v , castupV_TSum v') ⌝              ∧ ▷ Ψ (TSum TUnknown TUnknown) (v , v'))
                             ∨ (⌜ ww = (embedV_Ground_TArrow v , castupV_TArrow v') ⌝          ∧ ▷ Ψ (TArrow TUnknown TUnknown) (v , v'))
                             ∨ (∃ u u', ⌜ ww = (embedV_TUnknown u, castupV_TRec (FoldV u')) ⌝ ∧ ▷ Ψ TUnknown (u , u')
                               )
      )
    | _ => True (** exfaslo ... *)
    end)%I.

  Program Definition interp_gen_ne (Ψ : typeO -n> D) : typeO -n> D := λne τ p, interp_gen Ψ τ p.
  Solve Obligations with repeat intros ?; simpl; auto_equiv.

  Global Instance interp_gen_ne_contractive : Contractive interp_gen_ne.
  Proof.
    intros n Ψ1 Ψ2  pnΨ τ. simpl.
    induction τ; intro p; simpl.
    - auto.
    - f_equiv.
      + f_equiv. intro a. f_equiv. exact (IHτ1 a).
      + f_equiv. intro a. f_equiv. exact (IHτ2 a).
    - f_equiv. intro p1. f_equiv. intro p2. f_equiv. f_equiv.
      + exact (IHτ1 p1).
      + exact (IHτ2 p2).
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

  Lemma unfold_interp : interp ≡ interp_gen_ne interp.
  Proof. apply fixpoint_unfold. Qed.

  Lemma unfold_interp_type τ : interp τ ≡ interp_gen_ne interp τ.
  Proof. f_equiv. apply unfold_interp. Qed.

  Lemma unfold_interp_type_pair τ vv : interp τ vv ≡ interp_gen interp τ vv.
  Proof. assert (H : interp_gen interp τ vv ≡ interp_gen_ne interp τ vv). auto_equiv. rewrite H. apply unfold_interp_type. Qed.

  (* Lemma unfold_interp_type_pair τ vv : interp τ vv ≡ interp_gen_ne interp τ vv. *)
  (* Proof. apply unfold_interp_type. Qed. *)

  Global Instance interp_persistent τ vv :
    Persistent (⟦ τ ⟧ vv).
  Proof.
    revert vv. induction τ; intro p; rewrite unfold_interp_type_pair; simpl; try by apply _.
    - apply or_persistent; apply exist_persistent; intro q; rewrite -unfold_interp_type_pair; apply _.
    - apply exist_persistent. intro q. apply exist_persistent. intro r.
      do 2 rewrite -unfold_interp_type_pair. apply _.
  Qed.


  Definition interp_env (Γ : list type)
      (vvs : list (stlc_mu.lang.val * cast_calculus.lang.val)) : iProp Σ :=
    (⌜length Γ = length vvs⌝ ∗ [∗] zip_with (λ τ, ⟦ τ ⟧) Γ vvs)%I.
  Notation "⟦ Γ ⟧*" := (interp_env Γ).

  Global Instance interp_env_base_persistent Γ vs :
  TCForall Persistent (zip_with (λ τ, ⟦ τ ⟧) Γ vs).
  Proof.
    revert vs.
    induction Γ => vs; simpl; destruct vs; constructor; apply _.
  Qed.
  Global Instance interp_env_persistent Γ Δ vvs :
    Persistent (⟦ Γ ⟧* vvs) := _.

  Lemma interp_env_length Γ vvs : ⟦ Γ ⟧* vvs ⊢ ⌜length Γ = length vvs⌝.
  Proof. by iIntros "[% ?]". Qed.

  Lemma interp_env_Some_l Γ vvs x τ :
    Γ !! x = Some τ → ⟦ Γ ⟧* vvs ⊢ (∃ vv, ⌜vvs !! x = Some vv⌝ ∧ ⟦ τ ⟧ vv).
  Proof.
    iIntros (?) "[Hlen HΓ]"; iDestruct "Hlen" as %Hlen.
    destruct (lookup_lt_is_Some_2 vvs x) as [v Hv].
    { by rewrite -Hlen; apply lookup_lt_Some with τ. }
    iExists v; iSplit. done. iApply (big_sepL_elem_of with "HΓ").
    apply elem_of_list_lookup_2 with x.
    rewrite lookup_zip_with; by simplify_option_eq.
  Qed.

  Lemma interp_env_nil : ⊢ ⟦ [] ⟧* [].
  Proof. iSplit; simpl; auto. Qed.
  Lemma interp_env_cons Δ Γ vvs τ vv :
    ⟦ τ :: Γ ⟧* (vv :: vvs) ⊣⊢ ⟦ τ ⟧ vv ∗ ⟦ Γ ⟧* vvs.
  Proof.
    rewrite /interp_env /= (assoc _ (⟦ _ ⟧ _)) -(comm _ ⌜_ = _⌝%I) -assoc.
    by apply sep_proper; [apply pure_proper; lia|].
  Qed.

  (* Lemma interp_env_ren Δ (Γ : list type) vvs τi : *)
  (*   ⟦ subst (ren (+1)) <$> Γ ⟧* (τi :: Δ) vvs ⊣⊢ ⟦ Γ ⟧* Δ vvs. *)
  (* Proof. *)
  (*   apply sep_proper; [apply pure_proper; by rewrite fmap_length|]. *)
  (*   revert Δ vvs τi; induction Γ=> Δ [|v vs] τi; csimpl; auto. *)
  (*   apply sep_proper; auto. apply (interp_weaken [] [τi] Δ). *)
  (* Qed. *)

End logrel.

Typeclasses Opaque interp_env.
Notation "⟦ τ ⟧" := (interp τ).
Notation "⟦ τ ⟧ₑ" := (interp_expr (interp τ)).
Notation "⟦ Γ ⟧*" := (interp_env Γ).

From fae_gtlc_mu.cast_calculus Require Export types typing.

Section bin_log_def.
  Context `{!implG Σ, !specG Σ}.
  Notation D := (prodO stlc_mu.lang.valO cast_calculus.lang.valO -n> iProp Σ).

  Definition bin_log_related
  (Γ : list cast_calculus.types.type) (e : stlc_mu.lang.expr) (e' : cast_calculus.lang.expr) (τ : cast_calculus.types.type) :=
    ∀ vvs (ei' : cast_calculus.lang.expr),
    initially_inv ei' ∗ ⟦ Γ ⟧* vvs ⊢
    ⟦ τ ⟧ₑ (e.[stlc_mu.typing.env_subst (vvs.*1)], e'.[cast_calculus.typing.env_subst (vvs.*2)]).
End bin_log_def.

