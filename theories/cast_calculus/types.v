From Autosubst Require Export Autosubst.

(** Types *)
Inductive type :=
  | TUnit : type
  | TProd (τ1 τ2 : type) : type
  | TSum (τ1 τ2 : type) : type
  | TArrow (τ1 τ2 : type) : type
  | TRec (τ : {bind 1 of type})
  | TVar (x : var)
  | TUnknown : type.

Instance Ids_type : Ids type. derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.
Instance SubstLemmas_typer : SubstLemmas type. derive. Qed.

(** Definition of shape operator; S in figure 2 of paper *)
Definition get_shape (τ : type) : option type :=
  match τ with
  | TUnit => None
  | TProd x x0 => Some (TProd TUnknown TUnknown)
  | TSum x x0 => Some (TSum TUnknown TUnknown)
  | TArrow x x0 => Some (TArrow TUnknown TUnknown)
  | TRec τ => Some (TRec TUnknown)
  | TVar x => None
  | TUnknown => None
  end.

(** Definition of shape operator; S in figure 2 of paper *)
Inductive Ground : type -> Type :=
  | Ground_TUnit : Ground TUnit
  | Ground_TProd : Ground (TProd TUnknown TUnknown)
  | Ground_TSum : Ground (TSum TUnknown TUnknown)
  | Ground_TArrow : Ground (TArrow TUnknown TUnknown)
  | Ground_TRec : Ground (TRec TUnknown).

Lemma get_shape_is_ground {τ τG : type} : get_shape τ = Some τG -> Ground τG.
Proof. intro. destruct τ; destruct τG; inversion H; constructor. Qed.

(** Inert casting pairs; used to define which expressions are values *)
Inductive ICP : type -> type -> Prop :=
  | TArrow_TArrow_icp τ1 τ2 τ1' τ2' : ICP (TArrow τ1 τ2) (TArrow τ1' τ2')
  | TGround_TUnknown_icp {τ} (G : Ground τ) : ICP τ TUnknown.
