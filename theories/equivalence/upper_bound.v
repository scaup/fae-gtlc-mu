From fae_gtlc_mu.equivalence Require Import types closures.
From stdpp Require Import base listset.
From iris Require Import base.

Definition combinations (τ τ' : type) : list (type * type) := (* we count more then actually possible but no biggie *)
  list_prod (closures τ) [TRec TUnknown] ++
  list_prod [TRec TUnknown] (closures τ) ++
  list_prod (closures τ') [TRec TUnknown] ++
  list_prod [TRec TUnknown] (closures τ') ++
  list_prod (closures τ) (closures τ') ++
  list_prod (closures τ') (closures τ).

Notation "{{ l }}" := (Listset l) (at level 20).

Definition upper_bound (A : list (type * type)) τ τ' : nat :=
  size ({{combinations τ τ'}} ∖ {{A}}).

Notation "#" := upper_bound.

(** if types are structurally smaller, then upper_bound is smaller or equal *)

Lemma upper_bound_le_arrow_l A τ1 τ2 τ1' τ2' :
  # A τ1' τ1 ≤ # A (TArrow τ1 τ2) (TArrow τ1' τ2').
Proof.
  rewrite /upper_bound.
  apply subseteq_size.
  apply difference_mono_r.
Admitted.

Lemma upper_bound_le_arrow_r A τ1 τ2 τ1' τ2' :
  # A τ2 τ2' ≤ # A (TArrow τ1 τ2) (TArrow τ1' τ2').
Proof.
  rewrite /upper_bound.
  apply subseteq_size.
  apply difference_mono_r.
Admitted.

(** if types is structurally larger, i.e. from i.e. τb.[μ.τb/] > μ.τ,
    then upper_bound is smaller *)

Lemma upper_bound_lt_rec_star A τb (pn : (TRec τb, TRec TUnknown) ∉ A) :
  # ((TRec τb, TRec TUnknown) :: A) τb.[TRec τb/] TUnknown < # A (TRec τb) TUnknown.
Proof.
Admitted.

Lemma upper_bound_lt_star_rec A τb (pn : (TRec TUnknown, TRec τb) ∉ A) :
  # ((TRec TUnknown, TRec τb) :: A) TUnknown τb.[TRec τb/] < # A TUnknown (TRec τb).
Proof.
Admitted.

Lemma upper_bound_lt_rec_rec A τb τb' (pn : (TRec τb, TRec τb') ∉ A) :
  # ((TRec τb, TRec τb') :: A) τb.[TRec τb/] τb'.[TRec τb'/] < # A (TRec τb) (TRec τb').
Proof.
Admitted.
