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

Instance Ids_type : Ids type. derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.
Instance SubstLemmas_typer : SubstLemmas type. derive. Qed.

(* We keep track on the maximal amount of free variables; *)
(* this is handy when we'll express substitutions later on, we don't have to calculate the distinct free variables... *)
(* also, gen_sym 0 will only contain closed types *)

Inductive gen_sym : nat -> type -> type -> Prop :=
| GenSymUnit (i : nat) : gen_sym i TUnit TUnit
| GenSymUnknownL (i : nat) (τ : type) : gen_sym i ⋆ τ
| GenSymUnknwonR (i : nat) (τ : type) : gen_sym i τ ⋆
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

Definition sym : type -> type -> Prop := gen_sym 0.

(* Lemma sym_dec (n : nat) (τi τf : type) : Decision (gen_sym n τi τf). *)
(* Proof. *)
  (* destruct τi; destruct τf; (apply left; by constructor) || apply right. *)
  (* -  *)


Lemma sym_dec (τi τf : type) : Decision (sym τi τf).
Proof.
  destruct τi; induction τf; simplify_eq; ((apply left; by constructor) || (try by (apply right; intro abs; inversion abs))).
  rep

  - simplify_eq.
  - constructor.

Inductive Ground : type → Prop :=
  | Ground_TUnit : Ground TUnit
  | Ground_TProd : Ground (TProd TUnknown TUnknown)
  | Ground_TSum : Ground (TSum TUnknown TUnknown)
  | Ground_TArrow : Ground (TArrow TUnknown TUnknown)
  | Ground_TRec : Ground (TRec TUnknown).

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

