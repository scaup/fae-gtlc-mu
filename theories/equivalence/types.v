From stdpp Require Import base list.
From Autosubst Require Export Autosubst.
From iris Require Export base.
Require Export Utf8_core.

(* omitting repetitive cases... *)

Inductive type :=
  | TUnit : type
  | TArrow (τ1 τ2 : type) : type
  | TRec (τ : {bind 1 of type})
  | TVar (x : var)
  | TUnknown.

Instance Ids_type : Ids type. derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.
Instance SubstLemmas_typer : SubstLemmas type. derive. Qed.

Inductive Ground : type → Type :=
  | GUnit : Ground TUnit
  | GArrow : Ground (TArrow TUnknown TUnknown)
  | GRec : Ground (TRec TUnknown).

Definition TClosed (τ : type) : Prop := forall σ, τ.[σ] = τ.

Instance type_eqdec : EqDecision type.
Proof.
  unfold EqDecision.
  intro τ.
  induction τ; intros τ'; destruct τ'; try (by (apply right; intro abs; inversion abs)).
  - by apply left.
  - destruct (IHτ1 τ'1) as [-> | neq].
    + destruct (IHτ2 τ'2) as [-> | neq].
      * by apply left.
      * apply right. intro abs. inversion abs. contradiction.
    + apply right. intro abs. inversion abs. contradiction.
  - destruct (IHτ τ0) as [-> | neq].
    + by apply left.
    + apply right. intro abs. inversion abs. contradiction.
  - destruct (decide (x = x0)) as [-> | neq].
    + by apply left.
    + apply right. intro abs. inversion abs. contradiction.
  - by apply left.
Qed.

Instance Unknown_dec (τ : type) : Decision (τ = TUnknown).
Proof. destruct τ; try (by (apply right; auto)) || (apply left; auto). Qed.

Inductive Cat : type → Type :=
  | CUnknown : Cat TUnknown
  | CGroundUnit : Ground TUnit → Cat TUnit
  | CGroundArrow : Ground (TArrow TUnknown TUnknown) → Cat (TArrow TUnknown TUnknown)
  | CGroundRec : Ground (TRec TUnknown) → Cat (TRec TUnknown)
  | CArrow τ1 τ2 : (τ1 ≠ TUnknown ∨ τ2 ≠ TUnknown) → Cat (TArrow τ1 τ2)
  | CRec τ : (τ ≠ TUnknown) → Cat (TRec τ)
  | CVar i : Cat (TVar i).

Lemma categorize (τ : type) : Cat τ.
Proof.
  destruct τ; try by do 2 constructor.
  - destruct (Unknown_dec τ1); simplify_eq.
    destruct (Unknown_dec τ2); simplify_eq.
    constructor. constructor. constructor; auto. constructor; auto.
  - destruct (Unknown_dec τ); simplify_eq.
    destruct (Unknown_dec TUnknown); simplify_eq.
    constructor. constructor. constructor; auto.
Qed.

(* boring properties about closedness {{{ *)

Lemma TArrow_closed1 {τ1 τ2} : TClosed (TArrow τ1 τ2) → TClosed τ1.
Proof.
  unfold TClosed.
  intros H σ.
  assert (H' : TArrow τ1.[σ] τ2.[σ] = TArrow τ1 τ2). asimpl in H; by rewrite H.
  inversion H'.
  by do 2 rewrite H1.
Qed.

Lemma TArrow_closed2 {τ1 τ2} : TClosed (TArrow τ1 τ2) → TClosed τ2.
Proof.
  unfold TClosed.
  intros H σ.
  assert (H' : TArrow τ1.[σ] τ2.[σ] = TArrow τ1 τ2). asimpl in H; by rewrite H.
  inversion H'.
  by do 2 rewrite H2.
Qed.

Lemma TArrow_closed {τ1 τ2} : TClosed τ1 → TClosed τ2 → TClosed (TArrow τ1 τ2).
Proof.
  unfold TClosed.
  intros H1 H2 τ'.
  simpl. by rewrite H1 H2.
Qed.

Lemma TRec_TArrow_closed {τ1 τ2} : TClosed (TRec τ1) → TClosed (TRec τ2) → TClosed (TRec (TArrow τ1 τ2)).
Proof.
  intros H1 H2.
  intro. simpl.
  assert (H1' : (TRec τ1).[σ] = TRec τ1). by rewrite H1. asimpl in H1'. inversion H1' as [H1'']. do 2 rewrite H1''.
  assert (H2' : (TRec τ2).[σ] = TRec τ2). by rewrite H2. asimpl in H2'. inversion H2' as [H2'']. do 2 rewrite H2''.
  done.
Qed.

Lemma TRec_closed_unfold_pre {τ τ'} : TClosed (TRec τ) → TClosed τ' → TClosed (τ.[τ'/]).
Proof.
  intros.
  induction τ.
  - by asimpl.
  - asimpl. apply TArrow_closed. apply IHτ1. admit.
Admitted.

Lemma TRec_closed_unfold {τ} : TClosed (TRec τ) → TClosed (τ.[TRec τ/]).
Proof. intro; by apply TRec_closed_unfold_pre. Qed.

Lemma no_var_is_closed x : not (TClosed (TVar x)).
Proof.
  intro H. assert (abs : (TVar x).[ren (+1)] = TVar x); first by apply H.
  inversion abs; lia.
Qed.

(* }}} *)


(* boring properties about substitution {{{ *)

Lemma scomp_assoc (σ1 σ2 σ3 : var → type) : (σ1 >> σ2) >> σ3 = σ1 >> (σ2 >> σ3).
Proof. by asimpl. Qed.

Lemma subst_commut (τ τ' : type) (σ : var → type) : up σ >> scons (τ.[σ]) ids = scons τ ids >> σ.
Proof. by asimpl. Qed.

Lemma subst_fv n m σ : (TVar (n + m)).[upn n σ] = ((TVar m).[σ].[ren (+n)]).
Proof.
  asimpl.
  induction n.
  - by asimpl.
  - asimpl. rewrite IHn. by asimpl.
Qed.

Lemma subst_fv_no n m σ : n < m → (TVar n).[upn m σ] = TVar n.
Proof.
Admitted.

(* }}} *)
