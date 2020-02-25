From Autosubst Require Export Autosubst.
From fae_gtlc_mu Require Import prelude.
From fae_gtlc_mu.cast_calculus Require Import types consistency.standard consistency.structural.definition.

Definition flip (p : type * type) : type * type := (p.2 , p.1).

Lemma flip_rewrite τ1 τ2 : flip (τ1 , τ2) = (τ2 , τ1).
  reflexivity.
Qed.

Lemma flip_flip_map l : map flip (map flip l) = l.
  induction l.
  by simpl.
  simpl. rewrite flip_rewrite IHl. by destruct a.
Qed.

Lemma cons_struct_symmetric (A : list (type * type)) (τ τ' : type) (P : cons_struct A τ τ') :
  cons_struct (map flip A) τ' τ.
Proof.
  induction P; try by constructor.
  - apply consStarTau with (τG := τG); by (done || rewrite map_length).
  - apply consTauStar with (τG := τG); by (done || rewrite map_length).
  - apply consTRecTRecExposeCall. intro abs. apply pμτlμτrnotA. rewrite -flip_rewrite in abs.
    rewrite -(flip_flip_map A).
    rewrite -flip_rewrite.
    by apply elem_of_list_fmap_1.
    by rewrite map_cons in IHP.
  - apply consTRecTRecUseCall with (i := i).
    rewrite list_lookup_fmap.
    rewrite -flip_rewrite.
    by rewrite pμτlμtrinA.
Qed.
