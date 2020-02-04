From Autosubst Require Export Autosubst.
From fae_gtlc_mu Require Export prelude.

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

Inductive sym : type -> type -> Type :=
| SymUnit : sym TUnit TUnit
| SymUnknownL (τ : type) : sym ⋆ τ
| SymUnknwonR (τ : type) : sym τ ⋆
| SymSum
    (τ1 τ1' τ2 τ2' : type)
    (s1 : sym τ1 τ1')
    (s2 : sym τ2 τ2')
  : sym (τ1 + τ2)%type (τ1' + τ2')%type
| SymProd
    (τ1 τ1' τ2 τ2' : type)
    (s1 : sym τ1 τ1')
    (s2 : sym τ2 τ2')
  : sym (τ1 × τ2) (τ2 × τ2')
| SymArrow
    (τ1 τ1' τ2 τ2' : type)
    (s1 : sym τ1 τ1')
    (s2 : sym τ2 τ2')
  : sym (TArrow τ1 τ2) (TArrow τ2 τ2').

Inductive Ground : type → Prop :=
  | Ground_TUnit : Ground TUnit
  | Ground_TProd : Ground (TProd TUnknown TUnknown)
  | Ground_TSum : Ground (TSum TUnknown TUnknown)
  | Ground_TArrow : Ground (TArrow TUnknown TUnknown)
  | Ground_TRec : Ground (TRec TUnknown).

(* Definition is_unknown_dec (τ : type) : sum (τ = TUnknown) (not (τ = TUnknown)) := *)
(*   match τ with *)
(*   | TUnit => inr _ *)
(*   | TProd x x0 => inr _ *)
(*   | TSum x x0 => inr _ *)
(*   | TArrow x x0 => inr _ *)
(*   | TRec τ => inr _ *)
(*   | TVar x => inr _ *)
(*   | TUnknown => inl eq_refl *)
(*   end. *)

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

  (* match τ with *)
  (* | TUnit => left Ground_TUnit *)
  (* | TProd x x0 => match (decide (x = Unknown)) with *)
  (*                | left _ => match (decide (x0 = Unknown)) with *)
  (*                             | left _ => left Ground_TProd *)
  (*                             | right _ =>  *)
  (* | TSum x x0 => *)
  (* | TArrow x x0 => *)
  (* | TRec τ => *)
  (* | TVar x => *)
  (* | TUnknown => *)
  (* end. *)


(* Checking if two GROUND TYPES are equal *)
Definition Ground_equal {τ1 τ2 : type} (G1 : Ground τ1) (G2 : Ground τ2) : Prop := τ1 = τ2.

(* Definition Ground_equal_dec {τ1 τ2 : type} (G1 : Ground τ1) (G2 : Ground τ2) : Decision  := τ1 = τ2. *)

(* Inductive ground_type : Type := *)
(*   | Ground_TUnit : ground_type *)
(*   | Ground_TProd : ground_type *)
(*   | Ground_TArrow : ground_type *)
(*   | Ground_TSum : ground_type *)
(*   | Ground_TRec : ground_type. *)

(* Definition to_ground (τ : type) : option ground_type := *)
(*   match τ with *)
(*   | TUnit => Some Ground_TUnit *)
(*   | TProd x x0 => match x with *)
(*                  | TUnknown => match x0 with *)
(*                               | TUnknown => Some Ground_TProd *)
(*                               | _ => None *)
(*                               end *)
(*                  | _ => None *)
(*                  end *)
(*   | TSum x x0 => match x with *)
(*                  | TUnknown => match x0 with *)
(*                               | TUnknown => Some Ground_TSum *)
(*                               | _ => None *)
(*                               end *)
(*                  | _ => None *)
(*                  end *)
(*   | TArrow x x0 => match x with *)
(*                  | TUnknown => match x0 with *)
(*                               | TUnknown => Some Ground_TArrow *)
(*                               | _ => None *)
(*                               end *)
(*                  | _ => None *)
(*                  end *)
(*   | TRec τ => match τ with *)
(*              | TUnknown => Some Ground_TRec *)
(*              | _ => None *)
(*              end *)
(*   | TVar x => None *)
(*   | TUnknown => None *)
(*   end. *)
