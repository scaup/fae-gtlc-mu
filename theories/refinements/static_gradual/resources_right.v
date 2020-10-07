From iris.base_logic Require Export invariants.
From iris.algebra Require Import agree frac.
From iris.proofmode Require Import tactics.
From fae_gtlc_mu.cast_calculus Require Export lang.
Import uPred.

Definition specN := nroot .@ "gradual".

Canonical Structure exprO := leibnizO expr.
Definition specR := prodR fracR (agreeR exprO).

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
  Implicit Types e : expr.
  Implicit Types v : val.

  Local Hint Resolve to_of_val : core.

  Lemma step_insert_no_fork K e σ e' σ' :
    head_step e e' → erased_step ([fill K e], σ) ([fill K e'], σ').
  Proof. intros Hst. exists []. eapply (step_atomic _ _ _ _ _ _ _ [] [] []); eauto.
         by apply: Ectx_step.
  Qed.

  Lemma step_pure E ei' K e1' e2' :
    (head_step e1' e2') →
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
    iIntros (_). done.
  Qed.

  Lemma step_fst E ei' K e1' e2' :
    AsVal e1' → AsVal e2' →
    nclose specN ⊆ E →
    initially_inv ei' ∗ currently_half (fill K (Fst (Pair e1' e2'))) ={E}=∗ currently_half (fill K e1').
  Proof. intros [? <-] [? <-]. apply step_pure; econstructor; eauto. Qed.

  Lemma step_snd E ei' K e1' e2' :
    AsVal e1' → AsVal e2' → nclose specN ⊆ E →
    initially_inv ei' ∗ currently_half (fill K (Snd (Pair e1' e2'))) ={E}=∗ currently_half (fill K e2').
  Proof. intros [? <-] [? <-]; apply step_pure; econstructor; eauto. Qed.

  Lemma step_lam E ei' K e1' e2' :
    AsVal e2' → nclose specN ⊆ E →
    initially_inv ei' ∗ currently_half (fill K (App (Lam e1') e2'))
    ={E}=∗ currently_half (fill K (e1'.[e2'/])).
  Proof. intros [? <-]; apply step_pure; econstructor; eauto. Qed.

  Lemma step_Fold E ei' K e' :
    AsVal e' → nclose specN ⊆ E →
    initially_inv ei' ∗ currently_half (fill K (Unfold (Fold e'))) ={E}=∗ currently_half (fill K e').
  Proof. intros [? <-]; apply step_pure; econstructor; eauto. Qed.

  Lemma step_case_inl E ei' K e0' e1' e2' :
    AsVal e0' → nclose specN ⊆ E →
    initially_inv ei' ∗ currently_half (fill K (Case (InjL e0') e1' e2'))
      ={E}=∗ currently_half (fill K (e1'.[e0'/])).
  Proof. intros [? <-]; apply step_pure; econstructor; eauto. Qed.

  Lemma step_case_inr E ei' K e0' e1' e2' :
    AsVal e0' → nclose specN ⊆ E →
    initially_inv ei' ∗ currently_half (fill K (Case (InjR e0') e1' e2'))
      ={E}=∗ currently_half (fill K (e2'.[e0'/])).
  Proof. intros [? <-]; apply step_pure; econstructor; eauto. Qed.

End cfg.
