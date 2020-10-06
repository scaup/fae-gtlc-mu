From Autosubst Require Export Autosubst.

(** Types *)
Inductive type :=
  | TUnit : type
  | TProd (τ1 τ2 : type) : type
  | TSum (τ1 τ2 : type) : type
  | TArrow (τ1 τ2 : type) : type
  | TRec (τ : {bind 1 of type})
  | TVar (x : var).

Instance Ids_type : Ids type. derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.
Instance SubstLemmas_typer : SubstLemmas type. derive. Qed.
