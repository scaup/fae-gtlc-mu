From Autosubst Require Export Autosubst.
From fae_gtlc_mu Require Import prelude.
Require Coq.Logic.JMeq.

Inductive type :=
  | TUnit : type
  | TProd (τ1 τ2 : type) : type
  | TSum (τ1 τ2 : type) : type
  | TArrow (τ1 τ2 : type) : type
  | TRec (τ : {bind 1 of type})
  | TVar (x : var)
  | TUnknown : type.

Notation "⋆" := TUnknown : type_scope.
Infix "×" := TProd (at level 150) : type_scope.
Infix "+" := TSum : type_scope.

Instance Is_Unknown_dec (τ : type) : Decision (τ = ⋆).
Proof.
  destruct τ.
  apply right; auto.
  apply right; auto.
  apply right; auto.
  apply right; auto.
  apply right; auto.
  apply right; auto.
  apply left; auto.
Qed.

Instance Ids_type : Ids type. derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.
Instance SubstLemmas_typer : SubstLemmas type. derive. Qed.

Definition Is_Closed τ := forall τ', τ.[τ'/] = τ.

Definition TClosed τ := forall σ, τ.[σ] = τ.

Inductive Ground : type → Type :=
  | Ground_TUnit : Ground TUnit
  | Ground_TProd : Ground (TProd TUnknown TUnknown)
  | Ground_TSum : Ground (TSum TUnknown TUnknown)
  | Ground_TArrow : Ground (TArrow TUnknown TUnknown)
  | Ground_TRec : Ground (TRec TUnknown).

Definition Ground_dec (τ : type) : TDecision (Ground τ).
  destruct τ.
  - apply inl; constructor.
  - destruct (Is_Unknown_dec τ1). rewrite e.
    destruct (Is_Unknown_dec τ2). rewrite e0.
    + apply inl. constructor.
    + apply inr. intro aaa. inversion aaa. apply n. by symmetry.
    + apply inr. intro aaa. inversion aaa. apply n. by symmetry.
  - destruct (Is_Unknown_dec τ1). rewrite e.
    destruct (Is_Unknown_dec τ2). rewrite e0.
    + apply inl. constructor.
    + apply inr. intro aaa. inversion aaa. apply n. by symmetry.
    + apply inr. intro aaa. inversion aaa. apply n. by symmetry.
  - destruct (Is_Unknown_dec τ1). rewrite e.
    destruct (Is_Unknown_dec τ2). rewrite e0.
    + apply inl. constructor.
    + apply inr. intro aaa. inversion aaa. apply n. by symmetry.
    + apply inr. intro aaa. inversion aaa. apply n. by symmetry.
  - destruct (Is_Unknown_dec τ). rewrite e.
    + apply inl. constructor.
    + apply inr. intro aaa. inversion aaa. apply n. by symmetry.
  - apply inr. intro aaa. inversion aaa.
  - apply inr. intro aaa. inversion aaa.
Defined.

(* Checking if two GROUND TYPES are equal *)
Definition Ground_equal {τ1 τ2 : type} (G1 : Ground τ1) (G2 : Ground τ2) : Prop := τ1 = τ2.

(* Distinction between inert and active as in formalisation of Jeremy *)
Inductive Inert_cast_pair : type → type → Prop :=
  | Between_arrow_types τ1 τ2 τ1' τ2' : Inert_cast_pair (TArrow τ1 τ2) (TArrow τ1' τ2')
  | From_ground_to_unknown τ (G : Ground τ) : Inert_cast_pair τ TUnknown.

Lemma Unique_Ground_Proof τ (G1 : Ground τ) (G2 : Ground τ) : G1 = G2.
Proof.
  destruct G1; generalize_eqs G2; intros; destruct G2; try inversion H; try by rewrite H0.
Qed.

Lemma Unique_Inert_cast_pair_proof τi τf (Ip1 : Inert_cast_pair τi τf) (Ip2 : Inert_cast_pair τi τf) : Ip1 = Ip2.
Proof.
  destruct Ip1.
  - generalize_eqs Ip2.
    intros.
    destruct Ip2.
    simplify_eq.
      by rewrite H1.
      inversion H0.
  - generalize_eqs Ip2.
    intros.
    destruct Ip2.
    simplify_eq.
    rewrite (Unique_Ground_Proof τ G G0).
      by rewrite -H0.
Qed.










(* possibly with sigma type and proof of groundness *)
Definition get_shape (τ : type) : option type :=
  match τ with
  | TUnit => None
  | TProd x x0 => Some (TProd ⋆ ⋆)
  | TSum x x0 => Some (TSum ⋆ ⋆)
  | TArrow x x0 => Some (TArrow ⋆ ⋆)
  | TRec τ => Some (TRec ⋆)
  | TVar x => None
  | TUnknown => None
  end.

Lemma get_shape_is_ground {τ τG : type} : get_shape τ = Some τG -> Ground τG.
Proof.
  intro.
  destruct τ; simplify_eq; destruct τG; inversion H; constructor.
Qed.




Definition unfoldish (τ : type) : type := τ.[TRec τ/].
