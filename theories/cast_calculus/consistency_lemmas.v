Require Import fae_gtlc_mu.cast_calculus.consistency.
From fae_gtlc_mu Require Import prelude.

Lemma consistency_open_sym {τ τ'} : consistency_open τ τ' → consistency_open τ' τ.
Proof. induction 1; try by constructor. Qed.

Lemma consistency_open_unfold_help τ τ' α (pα : Closed α) α' (pα' : Closed α') k :
  consistency_open (TRec τ) (TRec τ') → consistency_open α α' → consistency_open τ.[upn k (α .: ids)] τ'.[upn k (α' .: ids)].
Proof.
  intro pC. inversion_clear pC.
  generalize dependent τ'.
  generalize dependent k.
  induction τ.
  - intros k τ' pC. inversion_clear pC.
    + asimpl; constructor.
    + asimpl; constructor.
  - intros k τ' pC. inversion_clear pC.
    + asimpl; constructor.
    + asimpl; constructor. by apply IHτ1. by apply IHτ2.
  - intros k τ' pC. inversion_clear pC.
    + asimpl; constructor.
    + asimpl; constructor. by apply IHτ1. by apply IHτ2.
  - intros k τ' pC. inversion_clear pC.
    + asimpl; constructor.
    + asimpl; constructor. by apply IHτ1. by apply IHτ2.
  - intros k τ' pC. inversion_clear pC.
    + asimpl; constructor.
    + intro. apply GenSymRec.
      assert (triv : up (upn k (α .: ids)) = upn (S k) (α .: ids)); first by asimpl. rewrite triv.
      by apply IHτ.
  - intros k τ' pC. inversion_clear pC.
    + asimpl; constructor.
    + intro.
      destruct (subst_fv_upn_cases x k (α .: ids)) as [[-> plt] | [j [eq ->]] ];
      destruct (subst_fv_upn_cases x k (α' .: ids)) as [[-> plt'] | [j' [eq' ->]]]; try by (exfalso; lia).
      * apply GenSymVar.
      * assert (triv : j' = j). lia. rewrite triv. clear triv.
        destruct j; asimpl. by rewrite pα pα'. apply GenSymVar.
  - intros k τ' pC.
    asimpl; constructor.
Qed.

Lemma consistency_open_unfold τ (pτ : Closed (TRec τ)) τ' (pτ' : Closed (TRec τ')) : consistency_open (TRec τ) (TRec τ') → consistency_open τ.[TRec τ/] τ'.[TRec τ'/].
Proof.
  intro pC.
  assert (triv : τ.[TRec τ/] = τ.[upn 0 (TRec τ .: ids)]). by asimpl. rewrite triv. clear triv.
  assert (triv : τ'.[TRec τ'/] = τ'.[upn 0 (TRec τ' .: ids)]). by asimpl. rewrite triv. clear triv.
  by apply consistency_open_unfold_help; auto.
Qed.

Definition consistency_open_dec τ τ' : sumor (consistency_open τ τ') (notT (consistency_open τ τ')).
Proof.
  generalize dependent τ'.
  induction τ; intro τ'; destruct τ'; ((by (apply inleft; by constructor)) || (try by apply inright; intro abs; inversion abs)); try specialize (IHτ1 τ'1); try specialize (IHτ2 τ'2); try specialize (IHτ τ0).
  - destruct IHτ1.
    destruct IHτ2.
    apply inleft; by constructor.
    apply inright. intro abs. inversion abs. contradiction.
    apply inright. intro abs. inversion abs. contradiction.
  - destruct IHτ1.
    destruct IHτ2.
    apply inleft; by constructor.
    apply inright. intro abs. inversion abs. contradiction.
    apply inright. intro abs. inversion abs. contradiction.
  - destruct IHτ1.
    destruct IHτ2.
    apply inleft; by constructor.
    apply inright. intro abs. inversion abs. contradiction.
    apply inright. intro abs. inversion abs. contradiction.
  - destruct IHτ.
    apply inleft; by constructor.
    apply inright. intro abs. inversion abs. contradiction.
  - destruct (decide (x = x0)).
    apply inleft. rewrite e. eapply GenSymVar.
    apply inright. intro abs. inversion abs. contradiction.
Qed.
