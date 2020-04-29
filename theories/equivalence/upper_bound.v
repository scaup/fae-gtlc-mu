From fae_gtlc_mu.equivalence Require Import types closed_rec_types listset_ext.
From stdpp Require Import base listset.
From iris Require Import base.

Definition combinations (τ τ' : type) : listset (type * type) := (* we count more then actually possible but no biggie *)
  listset_prod (closed_rec_types τ) {[TRec TUnknown]} ∪
  listset_prod (closed_rec_types τ') {[TRec TUnknown]} ∪
  listset_prod {[TRec TUnknown]} (closed_rec_types τ) ∪
  listset_prod {[TRec TUnknown]} (closed_rec_types τ') ∪
  listset_prod (closed_rec_types τ) (closed_rec_types τ') ∪
  listset_prod (closed_rec_types τ') (closed_rec_types τ).

Notation "{{ l }}" := (Listset l) (at level 20).

Definition upper_bound (A : list (type * type)) τ τ' : nat :=
  size (combinations τ τ' ∖ {{A}}).

Notation "#" := upper_bound.

Lemma subseteq_comp_normal {X1 X1' X2 X2' X3 X3' X4 X4' X5 X5' X6 X6' : listset (type * type)}
      (H1 : X1 ⊆ X1') (H2 : X2 ⊆ X2') (H3 : X3 ⊆ X3') (H4 : X4 ⊆ X4') (H5 : X5 ⊆ X5') (H6 : X6 ⊆ X6') :
  X1 ∪ X2 ∪ X3 ∪ X4 ∪ X5 ∪ X6 ⊆ X1' ∪ X2' ∪ X3' ∪ X4' ∪ X5' ∪ X6'.
Proof. set_solver. Qed.

Lemma subseteq_comp_contravariant {X1 X1' X2 X2' X3 X3' X4 X4' X5 X5' X6 X6' : listset (type * type)}
      (H1 : X1 ⊆ X2') (H2 : X2 ⊆ X1') (H3 : X3 ⊆ X4') (H4 : X4 ⊆ X3') (H5 : X5 ⊆ X6') (H6 : X6 ⊆ X5') :
  X1 ∪ X2 ∪ X3 ∪ X4 ∪ X5 ∪ X6 ⊆ X1' ∪ X2' ∪ X3' ∪ X4' ∪ X5' ∪ X6'.
Proof. set_solver. Qed.

Lemma size_elem_difference_suc {A : Type} {_ : EqDecision A} (l : listset A) (k : list A) (a : A) : a ∈ l → a ∉ k →
  size (l ∖ {{k}}) = S (size (l ∖ {{a :: k}})).
Proof.
  intros.
  assert (triv : l ≡ l ∖ {[a]} ∪ {[a]}).
  { apply set_subseteq_antisymm; try set_solver.
    intros τ pin; destruct (decide (τ = a)); set_solver. } rewrite{1} triv. clear triv.
  rewrite difference_union_distr_l.
  rewrite size_union_alt.
  assert (triv : {[a]} ≡ {[a]} ∖ {{k}} ∖ (l ∖ {[a]} ∖ {{k}})). set_solver. rewrite -triv. clear triv.
  assert (triv : l ∖ {[a]} ∖ {{k}} ≡ l ∖ {{a :: k}}).
  { assert (triv : {{a :: k}} = {[a]} ∪ {{k}}). set_solver. rewrite triv. clear triv. set_solver. } rewrite triv. clear triv.
  rewrite size_singleton. lia.
Qed.

(** if types are structurally smaller, then upper_bound is smaller or equal *)

Lemma upper_bound_le_arrow_r A τ1 τ2 τ1' τ2' :
  # A τ2 τ2' ≤ # A (TArrow τ1 τ2) (TArrow τ1' τ2').
Proof.
  rewrite /upper_bound.
  apply subseteq_size.
  apply difference_mono_r.
  apply subseteq_comp_normal; apply listset_prod_subseteq; set_solver.
Qed.

Lemma upper_bound_le_arrow_l A τ1 τ2 τ1' τ2' :
  # A τ1' τ1 ≤ # A (TArrow τ1 τ2) (TArrow τ1' τ2').
Proof.
  rewrite /upper_bound.
  apply subseteq_size.
  apply difference_mono_r.
  rewrite /combinations.
  apply subseteq_comp_contravariant; apply listset_prod_subseteq; set_solver.
Qed.

(** if types is structurally larger, i.e. from i.e. τb.[μ.τb/] > μ.τ,
    then upper_bound is smaller *)

Lemma upper_bound_lt_rec_star A τb (pμτb : TClosed (TRec τb)) (pn : (TRec τb, TRec TUnknown) ∉ A) :
  # ((TRec τb, TRec TUnknown) :: A) τb.[TRec τb/] TUnknown < # A (TRec τb) TUnknown.
Proof.
  rewrite /upper_bound.
  rewrite (size_elem_difference_suc _ A (TRec τb, TRec TUnknown)); try auto.
  + apply le_lt_n_Sm. apply subseteq_size. apply difference_mono_r.
    apply subseteq_comp_normal; apply listset_prod_subseteq; (apply (closed_rec_types_unfold_subset τb pμτb) || set_solver).
  + rewrite /combinations.
    cut ((TRec τb, TRec TUnknown) ∈ listset_prod (closed_rec_types (TRec τb)) {[TRec TUnknown]}). set_solver.
    apply in_listset_prod_iff; set_solver.
Qed.

Lemma upper_bound_lt_star_rec A τb (pμτb : TClosed (TRec τb)) (pn : (TRec TUnknown, TRec τb) ∉ A) :
  # ((TRec TUnknown, TRec τb) :: A) TUnknown τb.[TRec τb/] < # A TUnknown (TRec τb).
Proof.
  rewrite /upper_bound.
  rewrite (size_elem_difference_suc _ A (TRec TUnknown, TRec τb)); try auto.
  + apply le_lt_n_Sm. apply subseteq_size. apply difference_mono_r.
    (* apply closed_rec_types_unfold_subset. *)
    apply subseteq_comp_normal; apply listset_prod_subseteq; (apply (closed_rec_types_unfold_subset τb pμτb) || set_solver).
  + rewrite /combinations.
    cut ((TRec TUnknown, TRec τb) ∈ listset_prod {[TRec TUnknown]} (closed_rec_types (TRec τb))). set_solver.
    apply in_listset_prod_iff; set_solver.
Qed.

Lemma upper_bound_lt_rec_rec A τb (pμτb : TClosed (TRec τb)) τb' (pμτb' : TClosed (TRec τb')) (pn : (TRec τb, TRec τb') ∉ A) :
  # ((TRec τb, TRec τb') :: A) τb.[TRec τb/] τb'.[TRec τb'/] < # A (TRec τb) (TRec τb').
Proof.
  rewrite /upper_bound.
  rewrite (size_elem_difference_suc _ A (TRec τb, TRec τb')); try auto.
  + apply le_lt_n_Sm. apply subseteq_size. apply difference_mono_r.
    apply subseteq_comp_normal; apply listset_prod_subseteq; (by eapply (closed_rec_types_unfold_subset) || set_solver).
  + rewrite /combinations.
    cut ((TRec τb, TRec τb') ∈ listset_prod (closed_rec_types (TRec τb)) (closed_rec_types (TRec τb'))). set_solver.
    apply in_listset_prod_iff; set_solver.
Qed.
