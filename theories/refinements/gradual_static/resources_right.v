From iris.algebra Require Import cmra excl auth frac agree gmap list.
From iris.program_logic Require Import lifting.
From iris.proofmode Require Import tactics.
From fae_gtlc_mu.refinements.gradual_static Require Export resources_left.
From fae_gtlc_mu.stlc_mu Require Export lang.
Import uPred.

Definition specN := nroot .@ "gradual".

(** The CMRA for the heap of the specification. *)

Canonical Structure exprO := leibnizO expr.

Definition specR := prodR fracR (agreeR exprO).

(** The CMRA for the thread pool. *)
Class specG Σ := SpecG { specR_inG :> inG Σ specR; spec_name : gname }.

Definition currently `{specG Σ} (e : expr) : iProp Σ :=
  own spec_name ((1%Qp , to_agree e) : specR).

Definition currently_half `{specG Σ} (e : expr) : iProp Σ :=
  own spec_name (((1 / 2)%Qp , to_agree e) : specR).

Definition initially_body `{specG Σ} (ei' : expr) : iProp Σ :=
  (∃ e', (currently_half e')
            ∗ ⌜rtc erased_step ([ei'] , tt) ([e'] , tt)⌝)%I.

Definition initially_inv `{specG Σ} `{invG Σ} (ei' : expr) : iProp Σ :=
  inv specN (initially_body ei').

Section cfg.
  Context `{!specG Σ}.
  Context `{!invG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  (* Implicit Types σ : state. *)
  Implicit Types e : expr.
  Implicit Types v : val.

  Local Hint Resolve to_of_val : core.

  (** Conversion to tpools and back *)
  Lemma step_insert_no_fork K e σ e' σ' :
    head_step e σ [] e' σ' [] → erased_step ([fill K e], σ) ([fill K e'], σ').
  Proof. intros Hst. exists []. eapply (step_atomic _ _ _ _ _ _ _ [] [] []); eauto.
         by apply: Ectx_step.
  Qed.

  Local Set Warnings "-notation-overridden".
  Lemma step_pure E ei' K e1' e2' σ :
    (head_step e1' σ [] e2' σ []) →
    nclose specN ⊆ E →
    initially_inv ei' ∗ currently_half (fill K e1') ={E}=∗ currently_half (fill K e2').
  Proof.
    iIntros (??) "[Hinv Hj]".
    rewrite /initially_inv /initially_body.
    iInv specN as ">Hinit" "Hclose".
    iDestruct "Hinit" as (ef') "[Hown %]".
    (** fill K e1' = ef' *)
    rewrite /currently_half.
    iDestruct (own_valid_2 with "Hown Hj") as "#eee".
    rewrite -pair_op frac_op' Qp_half_half.
    iDestruct "eee" as %[_ ->%agree_op_inv'%leibniz_equiv]%pair_valid.
    (** update *)
    (* bring together *)
    iDestruct (equiv_entails_sym _ _ (own_op _ _ _) with "[Hj Hown]") as "HOwnOne".
    iFrame.
    (* actually update *)
    rewrite -pair_op frac_op' Qp_half_half.
    iMod (own_update _ _ (1%Qp, to_agree (fill K e2')) with "HOwnOne") as "HOwnOne".
    rewrite agree_idemp.
    { apply cmra_update_exclusive. done. }
    rewrite -Qp_half_half -frac_op' -(agree_idemp (to_agree (fill K e2'))).
    iDestruct "HOwnOne" as "[Hown1 Hown2]".
    rewrite frac_op' Qp_half_half (agree_idemp (to_agree (fill K e2'))).
    (** close invariant *)
    iApply fupd_wand_r. iSplitL "Hclose Hown1". iApply ("Hclose" with "[Hown1]").
    iNext. iExists (fill K e2'). iFrame.
    iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto.
    destruct σ. by simpl in H. iFrame "Hown2". done.
  Qed.

  Lemma nsteps_pure_step_ctx n e1' e2' K :
    nsteps pure_step n e1' e2' → nsteps pure_step n (fill K e1') (fill K e2').
  Proof.
    revert e2'. revert e1'.
    induction n.
    - intros e1 e2 H. inversion H. simplify_eq. constructor.
    - intros e1 e2 H. inversion H. econstructor.
      SearchAbout pure_step.
      apply pure_step_ctx.
      apply hack. apply H1. by apply IHn.
  Qed.

  Lemma pure_step_prim_step e e' : pure_step e e' → prim_step e tt [] e' tt [].
    intro Pstp. destruct Pstp. destruct (pure_step_safe tt).
    destruct H as [σ [ls Hprim]]. destruct σ.
    by destruct (pure_step_det tt [] x tt ls Hprim) as [_ [ _ [-> ->]]].
  Qed.

  Lemma pure_step_erased_step e e' : pure_step e e' → erased_step ([e], ()) ([e'],()).
  Proof. intros Pst. exists []. eapply (step_atomic _ _ _ _ _ _ _ [] [] []); eauto. by apply pure_step_prim_step. Qed.

  Lemma nsteps_pure_step_prim_step n e e' : nsteps pure_step n e e' → nsteps erased_step n ([e], ()) ([e'], ()).
  Proof.
    intros.
    SearchAbout nsteps.
    cut (nsteps erased_step n ((fun e => ([e], ())) e) ((fun e => ([e], ())) e')). by simpl.
    eapply nsteps_congruence; eauto.
    intros. by apply pure_step_erased_step.
  Qed.

  Lemma steps_pure E ei' K e1' e2' n :
    (nsteps pure_step n e1' e2') →
    nclose specN ⊆ E →
    initially_inv ei' ∗ currently_half (fill K e1') ={E}=∗ currently_half (fill K e2').
  Proof.
    iIntros (??) "[Hinv Hj]".
    rewrite /initially_inv /initially_body.
    iInv specN as ">Hinit" "Hclose".
    iDestruct "Hinit" as (ef') "[Hown %]".
    (** fill K e1' = ef' *)
    rewrite /currently_half.
    iDestruct (own_valid_2 with "Hown Hj") as "#eee".
    rewrite -pair_op frac_op' Qp_half_half.
    iDestruct "eee" as %[_ ->%agree_op_inv'%leibniz_equiv]%pair_valid.
    (** update *)
    (* bring together *)
    iDestruct (equiv_entails_sym _ _ (own_op _ _ _) with "[Hj Hown]") as "HOwnOne".
    iFrame.
    (* actually update *)
    rewrite -pair_op frac_op' Qp_half_half.
    iMod (own_update _ _ (1%Qp, to_agree (fill K e2')) with "HOwnOne") as "HOwnOne".
    rewrite agree_idemp.
    { apply cmra_update_exclusive. done. }
    rewrite -Qp_half_half -frac_op' -(agree_idemp (to_agree (fill K e2'))).
    iDestruct "HOwnOne" as "[Hown1 Hown2]".
    rewrite frac_op' Qp_half_half (agree_idemp (to_agree (fill K e2'))).
    (** close invariant *)
    iApply fupd_wand_r. iSplitL "Hclose Hown1". iApply ("Hclose" with "[Hown1]").
    iNext. iExists (fill K e2'). iFrame.
    iPureIntro. SearchAbout rtc. eapply rtc_transitive. apply H1.
    apply (nsteps_rtc n). SearchAbout erased_step.
    SearchAbout nsteps.
    apply nsteps_pure_step_prim_step. by apply nsteps_pure_step_ctx.
    iFrame "Hown2". done.
  Qed.

  Lemma step_fst E ei' K e1' e2' :
    AsVal e1' → AsVal e2' →
    nclose specN ⊆ E →
    initially_inv ei' ∗ currently_half (fill K (Fst (Pair e1' e2'))) ={E}=∗ currently_half (fill K e1').
  Proof. intros [? <-] [? <-]. apply step_pure with (σ := tt); econstructor; eauto. Qed.

  Lemma step_snd E ei' K e1' e2' :
    AsVal e1' → AsVal e2' → nclose specN ⊆ E →
    initially_inv ei' ∗ currently_half (fill K (Snd (Pair e1' e2'))) ={E}=∗ currently_half (fill K e2').
  Proof. intros [? <-] [? <-]. apply step_pure with (σ := tt); econstructor; eauto. Qed.

  Lemma step_lam E ei' K e1' e2' :
    AsVal e2' → nclose specN ⊆ E →
    initially_inv ei' ∗ currently_half (fill K (App (Lam e1') e2'))
    ={E}=∗ currently_half (fill K (e1'.[e2'/])).
  Proof. intros [? <-]; apply step_pure with (σ := tt); econstructor; eauto. Qed.

  Lemma step_Fold E ei' K e' :
    AsVal e' → nclose specN ⊆ E →
    initially_inv ei' ∗ currently_half (fill K (Unfold (Fold e'))) ={E}=∗ currently_half (fill K e').
  Proof. intros [? <-]; apply step_pure with (σ := tt); econstructor; eauto. Qed.

  Lemma step_case_inl E ei' K e0' e1' e2' :
    AsVal e0' → nclose specN ⊆ E →
    initially_inv ei' ∗ currently_half (fill K (Case (InjL e0') e1' e2'))
      ={E}=∗ currently_half (fill K (e1'.[e0'/])).
  Proof. intros [? <-]; apply step_pure with (σ := tt); econstructor; eauto. Qed.

  Lemma step_case_inr E ei' K e0' e1' e2' :
    AsVal e0' → nclose specN ⊆ E →
    initially_inv ei' ∗ currently_half (fill K (Case (InjR e0') e1' e2'))
      ={E}=∗ currently_half (fill K (e2'.[e0'/])).
  Proof. intros [? <-]; apply step_pure with (σ := tt); econstructor; eauto. Qed.
End cfg.
