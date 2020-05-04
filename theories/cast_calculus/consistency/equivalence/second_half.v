From stdpp Require Import base list.
From Autosubst Require Export Autosubst.
Require Export Utf8_core.

From fae_gtlc_mu.cast_calculus Require Import types consistency.structural consistency.equivalence.intermediate.

Lemma cons_struct_pre_cons_struct A τ τ' : cons_struct_pre A τ τ' → cons_struct A τ τ'.
Proof.
  intro p. induction p; try by constructor.
  - eapply consTauStar.
    intro abs. inversion abs. destruct pτnG; by apply H.
    intro abs. inversion abs. auto.
    + by apply consTProdTProd.
    + apply consTGroundStar. constructor.
  - eapply consTauStar.
    intro abs. inversion abs. destruct pτnG; by apply H.
    intro abs. inversion abs. auto.
    + by apply consTSumTSum.
    + apply consTGroundStar. constructor.
  - eapply consTauStar.
    intro abs. inversion abs. destruct pτnG; by apply H.
    intro abs. inversion abs. auto.
    + by apply consTArrowTArrow.
    + apply consTGroundStar. constructor.
  - eapply consTauStar.
    intro abs. inversion abs. by apply pτnG. auto. auto.
    + by eapply consTRecTRecUseCall.
    + apply consTGroundStar. constructor.
  - eapply consTauStar.
    intro abs. inversion abs. by apply pτnG. auto. auto.
    + by eapply consTRecTRecExposeCall.
    + apply consTGroundStar. constructor.
  - eapply consStarTau.
    intro abs. inversion abs. destruct pτnG; by apply H.
    intro abs. inversion abs. auto.
    + apply consStarTGround. constructor.
    + by apply consTProdTProd.
  - eapply consStarTau.
    intro abs. inversion abs. destruct pτnG; by apply H.
    intro abs. inversion abs. auto.
    + apply consStarTGround. constructor.
    + by apply consTSumTSum.
  - eapply consStarTau.
    intro abs. inversion abs. destruct pτnG; by apply H.
    intro abs. inversion abs. auto.
    + apply consStarTGround. constructor.
    + by apply consTArrowTArrow.
  - eapply consStarTau.
    intro abs. inversion abs. by apply pτnG. auto. auto.
    + apply consStarTGround. constructor.
    + by eapply consTRecTRecUseCall.
  - eapply consStarTau.
    intro abs. inversion abs. by apply pτnG. auto. auto.
    + apply consStarTGround. constructor.
    + by eapply consTRecTRecExposeCall.
  - by eapply consTRecTRecUseCall.
Qed.
