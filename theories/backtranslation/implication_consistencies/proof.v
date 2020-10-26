From fae_gtlc_mu Require Import prelude.
From fae_gtlc_mu.cast_calculus Require Import consistency.
From fae_gtlc_mu.backtranslation Require Import alternative_consistency.
From fae_gtlc_mu.backtranslation.implication_consistencies.help_lemmas Require Import first_half second_half.

(* Proof that classical consistency relation implies the alternative one.
   We will need this when defining the backtranslation on expressions. *)

Lemma cons_co τi pτi τf pτf : consistency τi pτi τf pτf → alternative_consistency [] τi τf.
Proof.
  intro. apply alternative_consistency_pre_alternative_consistency.
  by apply struct_validity.
Qed.
