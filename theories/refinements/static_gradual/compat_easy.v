From fae_gtlc_mu.refinements.static_gradual Require Export resources_right logical_relation.
From fae_gtlc_mu.cast_calculus Require Export types typing.
From fae_gtlc_mu.stlc_mu Require Export lang.
From fae_gtlc_mu.cast_calculus Require Export lang.
From fae_gtlc_mu.cast_calculus Require Export lang.
From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import lifting.

Notation "Γ ⊨ e '≤log≤' e' : τ" :=
  (bin_log_related Γ e e' τ) (at level 74, e, e', τ at next level).

Section fundamental.
  Context `{!implG Σ,!specG Σ}.
  Notation D := (prodO stlc_mu.lang.valO cast_calculus.lang.valO -n> iPropO Σ).
  (* Implicit Types e : stlc_mu.lang.expr. *)
  Local Hint Resolve to_of_val : core.

  Local Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) ident(w)
        constr(Hv) uconstr(Hp) :=
    iApply (wp_bind (fill [ctx]));
    iApply (wp_wand with "[-]");
      [iApply Hp; iFrame "#"; trivial|];
    iIntros (v); iDestruct 1 as (w) Hv.

  (* Put all quantifiers at the outer level *)
  Lemma bin_log_related_alt {Γ e e' τ} : Γ ⊨ e ≤log≤ e' : τ → ∀ vvs ei' K',
    initially_inv ei' ∗ ⟦ Γ ⟧* vvs ∗ currently_half (fill K' (e'.[cast_calculus.typing.env_subst (vvs.*2)]))
    ⊢ WP e.[stlc_mu.typing.env_subst (vvs.*1)] {{ v, ∃ v',
        currently_half (fill K' (cast_calculus.lang.of_val v')) ∗ interp τ (v, v') }}.
  Proof.
    iIntros (Hlog vvs K ρ) "[#Hρ [HΓ Hj]]". asimpl.
    iApply (Hlog with "[HΓ]"); iFrame. eauto.
  Qed.

  Notation "'` H" := (bin_log_related_alt H) (at level 8).

  Lemma bin_log_related_var Γ x τ :
    Γ !! x = Some τ → Γ ⊨ stlc_mu.lang.Var x ≤log≤ cast_calculus.lang.Var x : τ.
  Proof.
    iIntros (? vvs ei') "[#Hρ #HΓ]". iIntros (K). iIntros "Hj /=".
    iDestruct (interp_env_Some_l with "HΓ") as ([v v']) "[Heq Hv]"; first done.
    iDestruct "Heq" as %Heq.
    erewrite !stlc_mu.typing.env_subst_lookup; rewrite ?list_lookup_fmap ?Heq; eauto.
    erewrite !cast_calculus.typing.env_subst_lookup; rewrite ?list_lookup_fmap ?Heq; eauto.
    iApply wp_value. eauto.
  Qed.

  Lemma bin_log_related_unit Γ : Γ ⊨ stlc_mu.lang.Unit ≤log≤ cast_calculus.lang.Unit : TUnit.
  Proof.
    iIntros (vvs ei') "#[Hρ HΓ]". iIntros (K) "Hj /=".
    iApply wp_value. iExists UnitV. rewrite unfold_interp_type_pair. eauto.
  Qed.

  Lemma bin_log_related_pair Γ e1 e2 e1' e2' τ1 τ2
      (IHHtyped1 : Γ ⊨ e1 ≤log≤ e1' : τ1)
      (IHHtyped2 : Γ ⊨ e2 ≤log≤ e2' : τ2) :
    Γ ⊨ stlc_mu.lang.Pair e1 e2 ≤log≤ Pair e1' e2' : TProd τ1 τ2.
  Proof.
    iIntros (vvs ei') "#[Hρ HΓ]"; iIntros (K) "Hj /=".
    smart_wp_bind (stlc_mu.lang.PairLCtx e2.[stlc_mu.typing.env_subst _]) v v' "[Hv #Hiv]"
      ('`IHHtyped1 _ _ ((PairLCtx e2'.[env_subst _]) :: K)).
    smart_wp_bind (stlc_mu.lang.PairRCtx v) w w' "[Hw #Hiw]"
      ('`IHHtyped2 _ _ ((PairRCtx v') :: K)).
    iApply wp_value.
    iExists (PairV v' w'); iFrame "Hw".
    rewrite interp_rw_TProd.
    iExists (v, v'), (w, w'). simpl; repeat iSplit; trivial.
  Qed.

  Lemma bin_log_related_fst Γ e e' τ1 τ2
      (IHHtyped : Γ ⊨ e ≤log≤ e' : TProd τ1 τ2) :
    Γ ⊨ stlc_mu.lang.Fst e ≤log≤ Fst e' : τ1.
  Proof.
    iIntros (vvs ei') "[#Hρ #HΓ]"; iIntros (K) "Hj /=".
    smart_wp_bind (stlc_mu.lang.FstCtx) v v' "[Hv #Hiv]" ('`IHHtyped _ _ (FstCtx :: K)); cbn.
    rewrite interp_rw_TProd.
    iDestruct "Hiv" as ([w1 w1'] [w2 w2']) "#[% [Hw1 Hw2]]"; simplify_eq.
    iMod (step_fst _ _ K (of_val w1') (of_val w2') with "[-]") as "Hw"; eauto.
    iApply wp_pure_step_later; auto. iApply wp_value; auto.
  Qed.

  Lemma bin_log_related_snd Γ e e' τ1 τ2
      (IHHtyped : Γ ⊨ e ≤log≤ e' : TProd τ1 τ2) :
    Γ ⊨ stlc_mu.lang.Snd e ≤log≤ Snd e' : τ2.
  Proof.
    iIntros (vvs ei') "#[Hρ HΓ]"; iIntros (K) "Hj /=".
    smart_wp_bind (stlc_mu.lang.SndCtx) v v' "[Hv #Hiv]" ('`IHHtyped _ _ (SndCtx :: K)); cbn.
    rewrite interp_rw_TProd.
    iDestruct "Hiv" as ([w1 w1'] [w2 w2']) "#[% [Hw1 Hw2]]"; simplify_eq.
    iMod (step_snd _ _ K (of_val w1') (of_val w2') with "[-]") as "Hw"; eauto.
    iApply wp_pure_step_later; auto. iApply wp_value; auto.
  Qed.

  Lemma bin_log_related_injl Γ e e' τ1 τ2
      (IHHtyped : Γ ⊨ e ≤log≤ e' : τ1) :
    Γ ⊨ stlc_mu.lang.InjL e ≤log≤ InjL e' : (TSum τ1 τ2).
  Proof.
    iIntros (vvs ei') "#[Hρ HΓ]"; iIntros (K) "Hj /=".
    smart_wp_bind (stlc_mu.lang.InjLCtx) v v' "[Hv #Hiv]"
      ('`IHHtyped _ _ (InjLCtx :: K)); cbn.
    iApply wp_value. repeat rewrite /= to_of_val. eauto.
    iExists (InjLV v'); iFrame "Hv".
    rewrite interp_rw_TSum.
    iLeft; iExists (_,_); eauto 10.
  Qed.

  Lemma bin_log_related_injr Γ e e' τ1 τ2
      (IHHtyped : Γ ⊨ e ≤log≤ e' : τ2) :
    Γ ⊨ stlc_mu.lang.InjR e ≤log≤ InjR e' : TSum τ1 τ2.
  Proof.
    iIntros (vvs ei') "#[Hρ HΓ]"; iIntros (K) "Hj /=".
    smart_wp_bind (stlc_mu.lang.InjRCtx) v v' "[Hv #Hiv]"
      ('`IHHtyped _ _ (InjRCtx :: K)); cbn.
    iApply wp_value. repeat rewrite /= to_of_val. eauto.
    iExists (InjRV v'); iFrame "Hv".
    rewrite interp_rw_TSum.
    iRight; iExists (_,_); eauto 10.
  Qed.

  Lemma bin_log_related_case Γ (e0 e1 e2 : stlc_mu.lang.expr) (e0' e1' e2' : cast_calculus.lang.expr) τ1 τ2 τ3
      (IHHtyped1 : Γ ⊨ e0 ≤log≤ e0' : TSum τ1 τ2)
      (IHHtyped2 : τ1 :: Γ ⊨ e1 ≤log≤ e1' : τ3)
      (IHHtyped3 : τ2 :: Γ ⊨ e2 ≤log≤ e2' : τ3) :
    Γ ⊨ stlc_mu.lang.Case e0 e1 e2 ≤log≤ Case e0' e1' e2' : τ3.
  Proof.
    iIntros (vvs ei') "#[Hρ HΓ]"; iIntros (K) "Hj /=".
    iDestruct (interp_env_length with "HΓ") as %?.
    smart_wp_bind (stlc_mu.lang.CaseCtx _ _) v v' "[Hv #Hiv]"
      ('`IHHtyped1 _ _ ((CaseCtx _ _) :: K)); cbn.
    rewrite interp_rw_TSum.
    iDestruct "Hiv" as "[Hiv|Hiv]".
    - iDestruct "Hiv" as ([w w']) "[% Hw]"; simplify_eq.
      iMod (step_case_inl _ _ K (of_val w') with "[-]") as "Hz"; eauto.
      simpl.
      iApply wp_pure_step_later; auto 1 using to_of_val. iNext.
      asimpl. iApply ('`IHHtyped2 ((w,w') :: vvs)); repeat iSplit; eauto.
      iApply interp_env_cons; auto.
    - iDestruct "Hiv" as ([w w']) "[% Hw]"; simplify_eq.
      iMod (step_case_inr _ _ K (of_val w') with "[-]") as "Hz"; eauto.
      simpl.
      iApply wp_pure_step_later; auto 1 using to_of_val. iNext.
      asimpl. iApply ('`IHHtyped3 ((w,w') :: vvs)); repeat iSplit; eauto.
      iApply interp_env_cons; auto.
  Qed.

  Lemma bin_log_related_lam Γ (e : stlc_mu.lang.expr) (e' : cast_calculus.lang.expr) τ1 τ2
      (IHHtyped : τ1 :: Γ ⊨ e ≤log≤ e' : τ2) :
    Γ ⊨ stlc_mu.lang.Lam e ≤log≤ Lam e' : TArrow τ1 τ2.
  Proof.
    iIntros (vvs ei') "#[Hρ HΓ]"; iIntros (K) "Hj /=".
    iApply wp_value. iExists (LamV _).
    rewrite interp_rw_TArrow.
    iIntros "{$Hj} !#".
    iIntros ([v v']) "#Hiv". iIntros (K') "Hj".
    iDestruct (interp_env_length with "HΓ") as %?.
    iApply wp_pure_step_later; auto 1 using to_of_val. iNext.
    iMod (step_lam _ _ K' _ (of_val v') with "[-]") as "Hz"; eauto.
    asimpl. iApply ('`IHHtyped ((v,v') :: vvs)); repeat iSplit; eauto.
    iApply interp_env_cons; iSplit; auto.
  Qed.

  Lemma bin_log_related_app Γ e1 e2 e1' e2' τ1 τ2
      (IHHtyped1 : Γ ⊨ e1 ≤log≤ e1' : TArrow τ1 τ2)
      (IHHtyped2 : Γ ⊨ e2 ≤log≤ e2' : τ1) :
    Γ ⊨ stlc_mu.lang.App e1 e2 ≤log≤ App e1' e2' :  τ2.
  Proof.
    iIntros (vvs ei') "#[Hρ HΓ]"; iIntros (K) "Hj /=".
    smart_wp_bind (stlc_mu.lang.AppLCtx (e2.[stlc_mu.typing.env_subst (vvs.*1)])) v v' "[Hv #Hiv]"
      ('`IHHtyped1 _ _ (((AppLCtx (e2'.[env_subst (vvs.*2)]))) :: K)); cbn.
    smart_wp_bind (stlc_mu.lang.AppRCtx v) w w' "[Hw #Hiw]"
                  ('`IHHtyped2 _ _ ((AppRCtx v') :: K)); cbn.
    rewrite interp_rw_TArrow.
    iApply ("Hiv" $! (w, w') with "Hiw"); simpl; eauto.
  Qed.

  Lemma bin_log_related_fold Γ e e' τ
      (IHHtyped : Γ ⊨ e ≤log≤ e' : τ.[(TRec τ)/]) :
    Γ ⊨ stlc_mu.lang.Fold e ≤log≤ cast_calculus.lang.Fold e' : TRec τ.
  Proof.
    iIntros (vvs ei') "#[Hρ HΓ]"; iIntros (K) "Hj /=".
    iApply (wp_bind (fill [stlc_mu.lang.FoldCtx])).
    iApply (wp_wand with "[Hj]"). iApply ('`IHHtyped _ _ (FoldCtx :: K)). iFrame. auto.
    iIntros (v); iDestruct 1 as (v') "[Hv #Hiv]".
    iApply wp_value.
    iExists (FoldV v'). iFrame "Hv".
    rewrite interp_rw_TRec.
    iAlways. iExists _, _. eauto.
  Qed.

  Lemma bin_log_related_unfold Γ e e' τ
      (IHHtyped : Γ ⊨ e ≤log≤ e' : TRec τ) :
    Γ ⊨ stlc_mu.lang.Unfold e ≤log≤ Unfold e' : τ.[(TRec τ)/].
  Proof.
    iIntros (vvs ei') "#[Hρ HΓ]"; iIntros (K) "Hj /=".
    iApply (wp_bind (fill [stlc_mu.lang.UnfoldCtx])).
    iApply (wp_wand with "[Hj]"). iApply ('`IHHtyped _ _ (UnfoldCtx :: K)). iFrame. auto.
    iIntros (v). iDestruct 1 as (v') "[Hw #Hiw]".
    simpl.
    rewrite interp_rw_TRec.
    iDestruct "Hiw" as (w w') "#[% Hiz]"; simplify_eq/=.
    iMod (step_Fold _ _ K (of_val w') with "[-]") as "Hz"; eauto.
    iApply wp_pure_step_later; cbn; auto.
    iNext. iApply wp_value; auto.
  Qed.


End fundamental.
