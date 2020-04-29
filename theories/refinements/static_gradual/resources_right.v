From iris.algebra Require Import cmra excl auth frac agree gmap list.
From iris.program_logic Require Import lifting.
From iris.proofmode Require Import tactics.
From fae_gtlc_mu.refinements.static_gradual Require Export resources_left.
From fae_gtlc_mu.cast_calculus Require Export lang.
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

(* Section definitionsS. *)
  (* Context `{specG Σ}. *)

  (* Definition heapS_mapsto (l : loc) (q : Qp) (v: val) : iProp Σ := *)
    (* own cfg_name (◯ (ε, {[ l := (q, to_agree v) ]})). *)

  (* Definition tpool_mapsto (e: expr) : iProp Σ := *)
    (* own cfg_name (◯ (Excl' e, ∅)). *)

  (* Global Instance heapS_mapsto_timeless l q v : Timeless (heapS_mapsto l q v). *)
  (* Proof. apply _. Qed. *)
(* End definitionsS. *)

(* Typeclasses Opaque heapS_mapsto tpool_mapsto. *)

(* Notation "l ↦ₛ{ q } v" := (heapS_mapsto l q v) *)
  (* (at level 20, q at level 50, format "l  ↦ₛ{ q }  v") : bi_scope. *)
(* Notation "l ↦ₛ v" := (heapS_mapsto l 1 v) (at level 20) : bi_scope. *)
(* Notation "⤇ e" := (tpool_mapsto e) (at level 20) : bi_scope. *)

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
  Lemma step_insert_no_fork K e σ κ e' σ' :
    head_step e σ κ e' σ' [] → erased_step ([fill K e], σ) ([fill K e'], σ').
  Proof. intros Hst. eexists. eapply (step_atomic _ _ _ _ _ _ _ [] [] []); eauto.
         by apply: Ectx_step'.
  Qed.

  Local Set Warnings "-notation-overridden".
  Lemma step_pure E ei' K e1' e2' :
    (head_step e1' tt [] e2' tt []) →
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
