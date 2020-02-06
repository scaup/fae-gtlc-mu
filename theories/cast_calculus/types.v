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
(* also, gen_sym 0 will only contain closed types *)

(* needs to be in Type, given a certain consistency, we want to now why it is consistent *)

Inductive gen_sym : nat -> type -> type -> Type :=
| GenSymUnit (i : nat) : gen_sym i TUnit TUnit
(* | GenSymUnknownL (i : nat) (τ : type) : gen_sym i ⋆ τ *)
| GenSymUnknownL (i : nat) (τ : type) : (exists (l : nat) , τ = TVar l -> l < i) -> gen_sym i ⋆ τ
(* | GenSymUnknownR (i : nat) (τ : type) : gen_sym i τ ⋆ *)
| GenSymUnknownR (i : nat) (τ : type) : (exists (l : nat) , τ = TVar l -> l < i) -> gen_sym i τ ⋆
| GenSymSum
    (i : nat)
    (τ1 τ1' τ2 τ2' : type)
    (s1 : gen_sym i τ1 τ1')
    (s2 : gen_sym i τ2 τ2')
  : gen_sym i (τ1 + τ2)%type (τ1' + τ2')%type
| GenSymProd
    (i : nat)
    (τ1 τ1' τ2 τ2' : type)
    (s1 : gen_sym i τ1 τ1')
    (s2 : gen_sym i τ2 τ2')
  : gen_sym i (τ1 × τ2) (τ1' × τ2')
| GenSymArrow
    (i : nat)
    (τ1 τ1' τ2 τ2' : type)
    (s1 : gen_sym i τ1 τ1')
    (s2 : gen_sym i τ2 τ2')
  : gen_sym i (TArrow τ1 τ2) (TArrow τ1' τ2')
| GenSymVar (j : nat) (i : nat) (P : i < j) :
    gen_sym j (TVar i) (TVar i)
| GenSymRec (j : nat) (τ τ' : type) (P : gen_sym (S j) τ τ') :
    gen_sym j (TRec τ) (TRec τ').

Inductive gen_sym_alt : nat -> type -> type -> Type :=
| GenSymAltGroundGround (i : nat) τ (G : Ground τ) :
    gen_sym_alt i τ τ
| GenSymAltGroundStar (i : nat) τ (G : Ground τ) :
    gen_sym_alt i τ ⋆
| GenSymAltStarGround (i : nat) τ (G : Ground τ) :
    gen_sym_alt i ⋆ τ
| GenSymAltStarStar (i : nat) :
    gen_sym_alt i ⋆ ⋆
| GenSymAltProds (i : nat) (τ1 τ1' τ2 τ2' : type) :
    gen_sym_alt i τ1 τ1' ->
    gen_sym_alt i τ2 τ2' ->
    gen_sym_alt i (τ1 × τ2)%type (τ1' × τ2')%type
| GenSymAltSums (i : nat) (τ1 τ1' τ2 τ2' : type) :
    gen_sym_alt i τ1 τ1' ->
    gen_sym_alt i τ2 τ2' ->
    gen_sym_alt i (τ1 + τ2)%type (τ1' + τ2')%type
| GenSymAltArrows (i : nat) (τ1 τ1' τ2 τ2' : type) :
    gen_sym_alt i τ1 τ1' ->
    gen_sym_alt i τ2 τ2' ->
    gen_sym_alt i (TArrow τ1 τ2')%type (TArrow τ1' τ2)%type
| GenSymAltVars (i j : nat) :
    i < j →
    gen_sym_alt j (TVar i) (TVar i)
| GenSymAltVarStar (i j : nat) :
    i < j →
    gen_sym_alt j (TVar i) ⋆
| GenSymAltStarVar (i j : nat) :
    i < j →
    gen_sym_alt j ⋆ (TVar i)
| GenSymAltRec (j : nat) (τ τ' : type) :
    gen_sym_alt (S j) τ τ' ->
    gen_sym_alt j (TRec τ) (TRec τ')
| GenSymAltStarTau i τ τG (G : Ground τG):
    gen_sym_alt i τG τ →
    gen_sym_alt i ⋆ τ
| GenSymAltTauStar i τ τG (G : Ground τG):
    gen_sym_alt i τ τG →
    gen_sym_alt i τ ⋆.

Lemma gen_sym_alt_symmetric (n : nat) (τ τ' : type) : gen_sym_alt n τ τ' -> gen_sym_alt n τ' τ.
Proof.
  intro P. induction P; try by constructor.
  by apply GenSymAltTauStar with (τG := τG).
  by apply GenSymAltStarTau with (τG := τG).
Qed.

Lemma sym_implies_alt_sym (n : nat) (τ τ' : type) : (gen_sym n τ τ') -> (gen_sym_alt n τ τ').
Proof.
  generalize τ' n.
  induction τ.
  - intros τ'0 m; destruct τ'0; try by (repeat constructor); try by (intro abs; inversion abs).
  - intros τ'0 m; destruct τ'0; try by (repeat constructor); try by (intro abs; inversion abs).
    + intro P. inversion P. simplify_eq. constructor. by apply IHτ1. by apply IHτ2.
    + intro P. apply GenSymAltTauStar with (τG := ⋆ × ⋆); first by constructor. constructor.
      apply IHτ1. constructor. { exists 0.  } apply IHτ2; constructor. { admit. }
  - intros τ'0 m; destruct τ'0; try by (repeat constructor); try by (intro abs; inversion abs).
    + intro P. inversion P. simplify_eq. constructor. by apply IHτ1. by apply IHτ2.
    + intro P. apply GenSymAltTauStar with (τG := (⋆ + ⋆)%type); first by constructor. constructor.
      apply IHτ1; constructor. { admit. } apply IHτ2; constructor. { admit. }
  - (** Arrow case *) intros τ'0 m; destruct τ'0; try by (repeat constructor); try by (intro abs; inversion abs).
    + intro P. inversion P. simplify_eq. constructor. by apply IHτ1. apply gen_sym_alt_symmetric. by apply IHτ2.
    + intro P. apply GenSymAltTauStar with (τG := (TArrow ⋆ ⋆)%type); first by constructor. constructor.
      apply IHτ1; constructor. { admit. } apply gen_sym_alt_symmetric. apply IHτ2; constructor. { admit. }
  - intros τ'0 m; destruct τ'0; try by (repeat constructor); try by (intro abs; inversion abs).
    + intro P. inversion P. simplify_eq.
      constructor. by apply IHτ.
    + intro P. apply GenSymAltTauStar with (τG := (TRec ⋆)); constructor.
      apply IHτ. constructor.
  - intros τ'0 m; destruct τ'0; try by (repeat constructor); try by (intro abs; inversion abs).
    + intro P. inversion P. simplify_eq.
      by apply GenSymAltVars.
    + intro P. apply GenSymAltVarStar. admit.
  - intros τ'0; induction τ'0; try by (repeat constructor); try by (intro abs; inversion abs).
    + intros m P. apply GenSymAltStarTau with (τG := (⋆ × ⋆)%type); constructor.
      apply IHτ'0_1; constructor. apply IHτ'0_2; constructor.
    + intros m P. apply GenSymAltStarTau with (τG := (⋆ + ⋆)%type); constructor.
      apply IHτ'0_1; constructor. apply IHτ'0_2; constructor.
    + intros m P. apply GenSymAltStarTau with (τG := (TArrow ⋆ ⋆)%type); constructor.
      apply IHτ'0_1; constructor. apply gen_sym_alt_symmetric. apply IHτ'0_2; constructor.
    + intros m P. apply GenSymAltStarTau with (τG := (TRec ⋆)%type); constructor.
      apply IHτ'0; constructor.
    + intros m P. apply GenSymAltStarVar. admit.



Definition sym : type -> type -> Prop := gen_sym 0.

Definition sym_alt : type -> type -> Prop := gen_sym_alt 0.


