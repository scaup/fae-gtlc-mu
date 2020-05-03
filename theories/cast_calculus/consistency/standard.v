From Autosubst Require Export Autosubst.
From fae_gtlc_mu Require Import prelude cast_calculus.types.
Require Coq.Logic.JMeq.

From stdpp Require Import base list.
From Autosubst Require Export Autosubst.
Require Export Utf8_core.

Inductive cons_stand_open : type -> type -> Prop :=
| GenSymUnit :
    cons_stand_open TUnit TUnit
| GenSymUnknownL τ :
    cons_stand_open TUnknown τ
| GenSymUnknownR τ :
    cons_stand_open τ TUnknown
| GenSymSum
    (τ1 τ1' τ2 τ2' : type)
    (s1 : cons_stand_open τ1 τ1')
    (s2 : cons_stand_open τ2 τ2')
  : cons_stand_open (τ1 + τ2)%type (τ1' + τ2')%type
| GenSymProd
    (τ1 τ1' τ2 τ2' : type)
    (s1 : cons_stand_open τ1 τ1')
    (s2 : cons_stand_open τ2 τ2')
  : cons_stand_open (τ1 × τ2) (τ1' × τ2')
| GenSymArrow τ1 τ1' τ2 τ2'
    (s1 : cons_stand_open τ1 τ1')
    (s2 : cons_stand_open τ2 τ2')
  : cons_stand_open (TArrow τ1 τ2) (TArrow τ1' τ2')
| GenSymVar i :
    cons_stand_open (TVar i) (TVar i)
| GenSymRec τ τ' (P : cons_stand_open τ τ') :
    cons_stand_open (TRec τ) (TRec τ').

Lemma cons_stand_open_sym {τ τ'} : cons_stand_open τ τ' → cons_stand_open τ' τ.
Proof. induction 1; try by constructor. Qed.

Lemma cons_stand_open_unfold_help τ τ' α (pα : TClosed α) α' (pα' : TClosed α') k :
  cons_stand_open (TRec τ) (TRec τ') → cons_stand_open α α' → cons_stand_open τ.[upn k (α .: ids)] τ'.[upn k (α' .: ids)].
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

Lemma cons_stand_open_unfold τ (pτ : TClosed (TRec τ)) τ' (pτ' : TClosed (TRec τ')) : cons_stand_open (TRec τ) (TRec τ') → cons_stand_open τ.[TRec τ/] τ'.[TRec τ'/].
Proof.
  intro pC.
  assert (triv : τ.[TRec τ/] = τ.[upn 0 (TRec τ .: ids)]). by asimpl. rewrite triv. clear triv.
  assert (triv : τ'.[TRec τ'/] = τ'.[upn 0 (TRec τ' .: ids)]). by asimpl. rewrite triv. clear triv.
  by apply cons_stand_open_unfold_help; auto.
Qed.

Definition cons_stand τ (pτ : TClosed τ) τ' (pτ' : TClosed τ') : Type := cons_stand_open τ τ'.

Instance cons_stand_open_dec τ τ' : Decision (cons_stand_open τ τ').
Proof.
  generalize dependent τ'.
  induction τ; intro τ'; destruct τ'; ((by (apply left; by constructor)) || (try by apply right; intro abs; inversion abs)); try specialize (IHτ1 τ'1); try specialize (IHτ2 τ'2); try specialize (IHτ τ0).
  - destruct IHτ1.
    destruct IHτ2.
    apply left; by constructor.
    apply right. intro abs. inversion abs. contradiction.
    apply right. intro abs. inversion abs. contradiction.
  - destruct IHτ1.
    destruct IHτ2.
    apply left; by constructor.
    apply right. intro abs. inversion abs. contradiction.
    apply right. intro abs. inversion abs. contradiction.
  - destruct IHτ1.
    destruct IHτ2.
    apply left; by constructor.
    apply right. intro abs. inversion abs. contradiction.
    apply right. intro abs. inversion abs. contradiction.
  - destruct IHτ.
    apply left; by constructor.
    apply right. intro abs. inversion abs. contradiction.
  - destruct (decide (x = x0)).
    apply left. rewrite e. eapply GenSymVar.
    apply right. intro abs. inversion abs. contradiction.
Qed.
