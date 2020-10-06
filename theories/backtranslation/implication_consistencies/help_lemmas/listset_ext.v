From iris Require Export base.
From stdpp Require Export base list sets mapset.
From stdpp Require Export base.
(* fhin_sets fin_maps. *)
From Autosubst Require Export Autosubst.
Require Export Utf8_core.
From fae_gtlc_mu.cast_calculus Require Import types.

Lemma map_union {A B} (l k : listset A) (f : A → B) : f <$> (l ∪ k) ≡ (f <$> l) ∪ (f <$> k).
Proof. set_solver. Qed.

Lemma map_singleton {A B} (a : A) (f : A → B) : (f <$> ({[ a ]} : listset A)) ≡ {[ (f a) ]}.
Proof. set_solver. Qed.

Lemma set_Forall_fmap_ext_1 (f g : type → type) (X : listset type) :
  set_Forall (λ x : type, f x = g x) X → f <$> X ≡ g <$> X.
Proof.
  intro.
  apply set_subseteq_antisymm.
  + intros τ Hτ.
    destruct (elem_of_fmap_1 _ _ _ Hτ) as [τ' [-> pin]].
    assert (Heq : f τ' = g τ'). apply H. apply  pin. rewrite Heq.
      by apply elem_of_fmap_2.
  + intros τ Hτ.
    destruct (elem_of_fmap_1 _ _ _ Hτ) as [τ' [-> pin]].
    assert (Heq : f τ' = g τ'). apply H. apply  pin. rewrite -Heq.
      by apply elem_of_fmap_2.
Qed.

Lemma set_Forall_subseteq (X Y : listset type) (P : type → Prop) :
  X ⊆ Y → set_Forall P Y → set_Forall P X.
Proof. intros. intros τ Hτ. apply H0. set_solver. Qed.

Lemma fmap_listset_id (X : listset type) :
  id <$> X ≡ X.
Proof. set_solver. Qed.

Lemma set_Forall_fmap_impl (f : type → type) (X : listset type) (P Q : type → Prop)
      (Himpl : forall τ : type, P τ → Q (f τ)) (HP : set_Forall P X) : set_Forall Q (f <$> X).
Proof.
  intros τ Hτ.
  destruct (elem_of_fmap_1 _ _ _ Hτ) as [τ' [-> pin]].
  apply Himpl. by apply HP.
Qed.

Definition listset_prod {A B : Type} (k : listset A) (l : listset B) : listset (A * B) :=
  Listset $ list_prod (listset_car k) (listset_car l).

Lemma in_listset_prod_iff {A B : Type} (l : listset A) (l' : listset B) (x : A) (y : B) :
  (x, y) ∈ (listset_prod l l') ↔ x ∈ l ∧ y ∈ l'.
Proof.
  rewrite /elem_of /listset_elem_of. do 3 rewrite elem_of_list_In.
  simpl. apply in_prod_iff.
Qed.

Lemma listset_prod_subseteq {A : Type} (k k' l l' : listset A) :
  k ⊆ k' → l ⊆ l' → listset_prod k l ⊆ listset_prod k' l'.
Proof.
  intros. intros (x , y) Hxy. apply in_listset_prod_iff.
  cut (x ∈ k ∧ y ∈ l). set_solver.
  by apply in_listset_prod_iff.
Qed.
