From stdpp Require Import base list.
From Autosubst Require Export Autosubst.
Require Export Utf8_core.

From fae_gtlc_mu.backtranslation Require Import alternative_consistency implication_consistencies.help_lemmas.intermediate.

Lemma alternative_consistency_pre_alternative_consistency A τ τ' : alternative_consistency_pre A τ τ' → alternative_consistency A τ τ'.
Proof.
  intro p. induction p; try by constructor.
  - eapply factorUp_Ground.
    intro abs. inversion abs. destruct pτnG; by apply H.
    intro abs. inversion abs. auto.
    + by apply throughProd.
    + apply atomic_Ground_Unknown. constructor.
  - eapply factorUp_Ground.
    intro abs. inversion abs. destruct pτnG; by apply H.
    intro abs. inversion abs. auto.
    + by apply throughSum.
    + apply atomic_Ground_Unknown. constructor.
  - eapply factorUp_Ground.
    intro abs. inversion abs. destruct pτnG; by apply H.
    intro abs. inversion abs. auto.
    + by apply throughArrow.
    + apply atomic_Ground_Unknown. constructor.
  - eapply factorUp_Ground.
    intro abs. inversion abs. by apply pτnG. auto. auto.
    + by eapply atomic_UseRecursion.
    + apply atomic_Ground_Unknown. constructor.
  - eapply factorUp_Ground.
    intro abs. inversion abs. by apply pτnG. auto. auto.
    + by eapply exposeRecursiveCAll.
    + apply atomic_Ground_Unknown. constructor.
  - eapply factorDown_Ground.
    intro abs. inversion abs. destruct pτnG; by apply H.
    intro abs. inversion abs. auto.
    + apply atomic_Unknown_Ground. constructor.
    + by apply throughProd.
  - eapply factorDown_Ground.
    intro abs. inversion abs. destruct pτnG; by apply H.
    intro abs. inversion abs. auto.
    + apply atomic_Unknown_Ground. constructor.
    + by apply throughSum.
  - eapply factorDown_Ground.
    intro abs. inversion abs. destruct pτnG; by apply H.
    intro abs. inversion abs. auto.
    + apply atomic_Unknown_Ground. constructor.
    + by apply throughArrow.
  - eapply factorDown_Ground.
    intro abs. inversion abs. by apply pτnG. auto. auto.
    + apply atomic_Unknown_Ground. constructor.
    + by eapply atomic_UseRecursion.
  - eapply factorDown_Ground.
    intro abs. inversion abs. by apply pτnG. auto. auto.
    + apply atomic_Unknown_Ground. constructor.
    + by eapply exposeRecursiveCAll.
  - by eapply atomic_UseRecursion.
Qed.
