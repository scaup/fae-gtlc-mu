From Autosubst Require Export Autosubst.
From fae_gtlc_mu Require Export prelude.
Require Coq.Logic.JMeq.

Inductive type :=
  | TUnit : type
  | TProd : type → type → type
  | TSum : type → type → type
  | TArrow : type → type → type
  | TRec (τ : {bind 1 of type})
  | TVar (x : var)
  | TUnknown : type.

Notation "⋆" := TUnknown : type_scope.
Infix "×" := TProd (at level 150) : type_scope.
Infix "+" := TSum : type_scope.

(*
Definition Is_Unknown_dec (τ : type) : Decision (τ = ⋆).
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
*)

Instance Ids_type : Ids type. derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.
Instance SubstLemmas_typer : SubstLemmas type. derive. Qed.

Definition Is_Closed τ := forall τ', τ.[τ'/] = τ.

Inductive Ground : type → Type :=
  | Ground_TUnit : Ground TUnit
  | Ground_TProd : Ground (TProd TUnknown TUnknown)
  | Ground_TSum : Ground (TSum TUnknown TUnknown)
  | Ground_TArrow : Ground (TArrow TUnknown TUnknown)
  | Ground_TRec : Ground (TRec TUnknown).

(*
Definition Ground_dec (τ : type) : Decision (Ground τ).
  destruct τ.
  - apply left; constructor.
  - destruct (Is_Unknown_dec τ1). rewrite e.
    destruct (Is_Unknown_dec τ2). rewrite e0.
    + apply left. constructor.
    + apply right. intro aaa. inversion aaa. apply n. by symmetry.
    + apply right. intro aaa. inversion aaa. apply n. by symmetry.
  - destruct (Is_Unknown_dec τ1). rewrite e.
    destruct (Is_Unknown_dec τ2). rewrite e0.
    + apply left. constructor.
    + apply right. intro aaa. inversion aaa. apply n. by symmetry.
    + apply right. intro aaa. inversion aaa. apply n. by symmetry.
  - destruct (Is_Unknown_dec τ1). rewrite e.
    destruct (Is_Unknown_dec τ2). rewrite e0.
    + apply left. constructor.
    + apply right. intro aaa. inversion aaa. apply n. by symmetry.
    + apply right. intro aaa. inversion aaa. apply n. by symmetry.
  - destruct (Is_Unknown_dec τ). rewrite e.
    + apply left. constructor.
    + apply right. intro aaa. inversion aaa. apply n. by symmetry.
  - apply right. intro aaa. inversion aaa.
  - apply right. intro aaa. inversion aaa.
Defined.
*)

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

(* We keep track on the maximal amount of free variables; *)
(* this is handy when we'll express substitutions later on, we don't have to calculate the distinct free variables... *)
(* also, open_sym 0 will only contain closed types *)

(* needs to be in Type, given a certain consistency, we want to now why it is consistent *)

(* Let's maybe not do this :( *)

Inductive open_sym : type -> type -> Type :=
| GenSymUnit : open_sym TUnit TUnit
| GenSymUnknownL (τ : type) : open_sym ⋆ τ
| GenSymUnknownR (τ : type) : open_sym τ ⋆
| GenSymSum
    (τ1 τ1' τ2 τ2' : type)
    (s1 : open_sym τ1 τ1')
    (s2 : open_sym τ2 τ2')
  : open_sym (τ1 + τ2)%type (τ1' + τ2')%type
| GenSymProd
    (τ1 τ1' τ2 τ2' : type)
    (s1 : open_sym τ1 τ1')
    (s2 : open_sym τ2 τ2')
  : open_sym (τ1 × τ2) (τ1' × τ2')
| GenSymArrow
    (τ1 τ1' τ2 τ2' : type)
    (s1 : open_sym τ1 τ1')
    (s2 : open_sym τ2 τ2')
  : open_sym (TArrow τ1 τ2) (TArrow τ1' τ2')
| GenSymVar (i : nat) :
    open_sym (TVar i) (TVar i)
| GenSymRec (τ τ' : type) (P : open_sym τ τ') :
    open_sym (TRec τ) (TRec τ').

Inductive open_sym_alt : type -> type -> Type :=
| GenSymAltGroundGround τ (G : Ground τ) :
    open_sym_alt τ τ
| GenSymAltGroundStar τ (G : Ground τ) :
    open_sym_alt τ ⋆
| GenSymAltStarGround τ (G : Ground τ) :
    open_sym_alt ⋆ τ
| GenSymAltStarStar :
    open_sym_alt ⋆ ⋆
| GenSymAltProds (τ1 τ1' τ2 τ2' : type) :
    open_sym_alt τ1 τ1' ->
    open_sym_alt τ2 τ2' ->
    open_sym_alt (τ1 × τ2)%type (τ1' × τ2')%type
| GenSymAltSums (τ1 τ1' τ2 τ2' : type) :
    open_sym_alt τ1 τ1' ->
    open_sym_alt τ2 τ2' ->
    open_sym_alt (τ1 + τ2)%type (τ1' + τ2')%type
| GenSymAltArrows (τ1 τ1' τ2 τ2' : type) :
    open_sym_alt τ1 τ1' ->
    open_sym_alt τ2 τ2' ->
    open_sym_alt (TArrow τ1 τ2')%type (TArrow τ1' τ2)%type
| GenSymAltVars (i : nat) :
    open_sym_alt (TVar i) (TVar i)
| GenSymAltVarStar (i : nat) :
    open_sym_alt (TVar i) ⋆
| GenSymAltStarVar (i : nat) :
    open_sym_alt ⋆ (TVar i)
| GenSymAltRec (τ τ' : type) :
    open_sym_alt τ τ' ->
    open_sym_alt (TRec τ) (TRec τ')
| GenSymAltStarTau τ τG (G : Ground τG):
    open_sym_alt τG τ →
    open_sym_alt ⋆ τ
| GenSymAltTauStar τ τG (G : Ground τG):
    open_sym_alt τ τG →
    open_sym_alt τ ⋆.

Lemma open_sym_alt_symmetric (τ τ' : type) : open_sym_alt τ τ' -> open_sym_alt τ' τ.
Proof.
  intro P. induction P; try by constructor.
  by apply GenSymAltTauStar with (τG := τG).
  by apply GenSymAltStarTau with (τG := τG).
Qed.

Lemma open_sym_implies_alt_open_sym (τ τ' : type) : (open_sym τ τ') -> (open_sym_alt τ τ').
Proof.
  generalize τ'.
  induction τ.
  - intros τ'0; destruct τ'0; try by (repeat constructor); try by (intro abs; inversion abs).
  - intros τ'0; destruct τ'0; try by (repeat constructor); try by (intro abs; inversion abs).
    + intro P. inversion P. simplify_eq. constructor. by apply IHτ1. by apply IHτ2.
    + intro P. apply GenSymAltTauStar with (τG := ⋆ × ⋆); first by constructor. constructor.
      apply IHτ1. constructor. apply IHτ2; constructor.
  - intros τ'0; destruct τ'0; try by (repeat constructor); try by (intro abs; inversion abs).
    + intro P. inversion P. simplify_eq. constructor. by apply IHτ1. by apply IHτ2.
    + intro P. apply GenSymAltTauStar with (τG := (⋆ + ⋆)%type); first by constructor. constructor.
      apply IHτ1; constructor. apply IHτ2; constructor.
  - (** Arrow case *) intros τ'0; destruct τ'0; try by (repeat constructor); try by (intro abs; inversion abs).
    + intro P. inversion P. simplify_eq. constructor. by apply IHτ1. apply open_sym_alt_symmetric. by apply IHτ2.
    + intro P. apply GenSymAltTauStar with (τG := (TArrow ⋆ ⋆)%type); first by constructor. constructor.
      apply IHτ1; constructor. apply open_sym_alt_symmetric. apply IHτ2; constructor.
  - intros τ'0; destruct τ'0; try by (repeat constructor); try by (intro abs; inversion abs).
    + intro P. inversion P. simplify_eq.
      constructor. by apply IHτ.
    + intro P. apply GenSymAltTauStar with (τG := (TRec ⋆)); constructor.
      apply IHτ. constructor.
  - intros τ'0; destruct τ'0; try by (repeat constructor); try by (intro abs; inversion abs).
    + intro P. inversion P. simplify_eq.
      by apply GenSymAltVars.
  - intros τ'0; induction τ'0; try by (repeat constructor); try by (intro abs; inversion abs).
    + intros P. apply GenSymAltStarTau with (τG := (⋆ × ⋆)%type); constructor.
      apply IHτ'0_1; constructor. apply IHτ'0_2; constructor.
    + intros P. apply GenSymAltStarTau with (τG := (⋆ + ⋆)%type); constructor.
      apply IHτ'0_1; constructor. apply IHτ'0_2; constructor.
    + intros P. apply GenSymAltStarTau with (τG := (TArrow ⋆ ⋆)%type); constructor.
      apply IHτ'0_1; constructor. apply open_sym_alt_symmetric. apply IHτ'0_2; constructor.
    + intros P. apply GenSymAltStarTau with (τG := (TRec ⋆)%type); constructor.
      apply IHτ'0; constructor.
Qed.

Lemma open_sym_reflexive (τ : type) : open_sym τ τ.
Proof.
  induction τ; by constructor.
Qed.

Lemma open_sym_symmetric (τ τ' : type) : open_sym τ τ' -> open_sym τ' τ.
Proof.
  intro P.
  induction P; by constructor.
Qed.


Lemma open_sym_alt_implies_open_sym (τ τ' : type) : (open_sym_alt τ τ') -> (open_sym τ τ').
Proof.
  intro P.
  induction P; try by (apply GenSymUnknownR || apply GenSymUnknownL || by constructor).
  - apply open_sym_reflexive.
  - constructor.
    + auto.
    + by apply open_sym_symmetric.
Qed.
