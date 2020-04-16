From stdpp Require Import base list.
From Autosubst Require Export Autosubst.
Require Export Utf8_core.

From fae_gtlc_mu.equivalence Require Import types.

Inductive cons_stand : type -> type -> Type :=
| GenSymUnit :
    cons_stand TUnit TUnit
| GenSymUnknownL τ :
    cons_stand TUnknown τ
| GenSymUnknownR τ :
    cons_stand τ TUnknown
| GenSymArrow τ1 τ1' τ2 τ2'
    (s1 : cons_stand τ1 τ1')
    (s2 : cons_stand τ2 τ2')
  : cons_stand (TArrow τ1 τ2) (TArrow τ1' τ2')
| GenSymVar i :
    cons_stand (TVar i) (TVar i)
| GenSymRec τ τ' (P : cons_stand τ τ') :
    cons_stand (TRec τ) (TRec τ').

Lemma cons_stand_sym {τ τ'} : cons_stand τ τ' → cons_stand τ' τ.
Proof. induction 1; try by constructor. Qed.

Lemma cons_stand_unfold_help τ τ' α (pα : TClosed α) α' (pα' : TClosed α') k :
  cons_stand (TRec τ) (TRec τ') → cons_stand α α' → cons_stand τ.[upn k (α .: ids)] τ'.[upn k (α' .: ids)].
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
    + intro. apply GenSymRec.
      assert (triv : up (upn k (α .: ids)) = upn (S k) (α .: ids)); first by asimpl. rewrite triv.
      by apply IHτ.
  - intros k τ' pC. inversion_clear pC.
    + asimpl; constructor.
    + intro. destruct (decide (x < k)).
      * repeat rewrite subst_fv_no; auto. apply GenSymVar.
      * assert (H : k ≤ x). lia.
        assert (H' : (∃ z : nat, x = k + z)). by apply nat_le_sum.
        (* destruct H' as [z ->]. *)
        (* destruct (nat_le_sum _ _ H) as [AAA]. [z ->]. *)
        (* repeat rewrite subst_fv. *)
        admit.
  - intros k τ' pC.
    asimpl; constructor.
Admitted.

Lemma cons_stand_unfold τ (pτ : TClosed (TRec τ)) τ' (pτ' : TClosed (TRec τ')) : cons_stand (TRec τ) (TRec τ') → cons_stand τ.[TRec τ/] τ'.[TRec τ'/].
Proof.
  intro pC.
  assert (triv : τ.[TRec τ/] = τ.[upn 0 (TRec τ .: ids)]). by asimpl. rewrite triv. clear triv.
  assert (triv : τ'.[TRec τ'/] = τ'.[upn 0 (TRec τ' .: ids)]). by asimpl. rewrite triv. clear triv.
  by apply cons_stand_unfold_help; auto.
Qed.
