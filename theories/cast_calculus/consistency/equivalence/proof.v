From fae_gtlc_mu Require Import prelude.
From fae_gtlc_mu.cast_calculus.consistency Require Import standard structural first_half second_half.

Lemma cons_co τi pτi τf pτf : cons_stand τi pτi τf pτf → cons_struct [] τi τf.
Proof.
  intro. apply cons_struct_pre_cons_struct.
  by apply struct_validity.
Qed.
