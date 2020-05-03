From fae_gtlc_mu Require Import prelude.
From fae_gtlc_mu.cast_calculus.consistency Require Import standard structural.

Lemma cons_co τi pτi τf pτf : cons_stand τi pτi τf pτf → cons_struct [] τi τf.
Admitted.
