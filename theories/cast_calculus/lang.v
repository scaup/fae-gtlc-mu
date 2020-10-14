From Autosubst Require Export Autosubst.
From iris.program_logic Require Export language ectx_language ectxi_language.
From fae_gtlc_mu.cast_calculus Require Export types types_lemmas.

(** Expressions *)
Inductive expr :=
| Var (x : var)
| Lam (e : {bind 1 of expr})
| App (e1 e2 : expr)
(* Base types *)
| Unit
(* Products *)
| Pair (e1 e2 : expr)
| Fst (e : expr)
| Snd (e : expr)
(* Sums *)
| InjL (e : expr)
| InjR (e : expr)
| Case (e0 : expr) (e1 : {bind expr}) (e2 : {bind expr})
(* Recursive Types *)
| Fold (e : expr)
| Unfold (e : expr)
(* Casts! *)
| Cast (e : expr) (τi τf : type)
| CastError.

Coercion App : expr >-> Funclass.

Instance Ids_expr : Ids expr. derive. Defined.
Instance Rename_expr : Rename expr. derive. Defined.
Instance Subst_expr : Subst expr. derive. Defined.
Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.

(** Values *)
Inductive val :=
| LamV (e : {bind 1 of expr})
| UnitV
| PairV (v1 v2 : val)
| InjLV (v : val)
| InjRV (v : val)
| FoldV (v : val)
| CastV (v : val) (τi τf : type) (Ip : ICP τi τf).

Fixpoint of_val (v : val) : expr :=
  match v with
  | LamV e => Lam e
  | UnitV => Unit
  | PairV v1 v2 => Pair (of_val v1) (of_val v2)
  | InjLV v => InjL (of_val v)
  | InjRV v => InjR (of_val v)
  | FoldV v => Fold (of_val v)
  | CastV v τi τf Ip => Cast (of_val v) τi τf
  end.
(* Notation "# v" := (of_val v) (at level 20). *)

Coercion of_val : val >-> expr.

Fixpoint to_val (e : expr) : option val :=
  match e with
  | Lam e => Some (LamV e)
  | Unit => Some UnitV
  | Pair e1 e2 => v1 ← to_val e1; v2 ← to_val e2; Some (PairV v1 v2)
  | InjL e => InjLV <$> to_val e
  | InjR e => InjRV <$> to_val e
  | Fold e => v ← to_val e; Some (FoldV v)
  | Cast e τi τf => match (ICP_dec τi τf) with
                     | left Ip => v ← to_val e; Some (CastV v τi τf Ip)
                     | right _ => None
                   end
  | Var _ => None
  | App _ _ => None
  | Fst _ => None
  | Snd _ => None
  | Case _ _ _ => None
  | Unfold _ => None
  | CastError => None
  end.

(** Evaluation contexts of depth 1 *)
Inductive ectx_item :=
| AppLCtx (e2 : expr)
| AppRCtx (v1 : val)
| PairLCtx (e2 : expr)
| PairRCtx (v1 : val)
| FstCtx
| SndCtx
| InjLCtx
| InjRCtx
| CaseCtx (e1 : {bind expr}) (e2 : {bind expr})
| FoldCtx
| UnfoldCtx
| CastCtx (τi τf : type).

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | AppLCtx e2 => App e e2
  | AppRCtx v1 => App (of_val v1) e
  | PairLCtx e2 => Pair e e2
  | PairRCtx v1 => Pair (of_val v1) e
  | FstCtx => Fst e
  | SndCtx => Snd e
  | InjLCtx => InjL e
  | InjRCtx => InjR e
  | CaseCtx e1 e2 => Case e e1 e2
  | FoldCtx => Fold e
  | UnfoldCtx => Unfold e
  | CastCtx τi τf => Cast e τi τf
  end.

Definition state : Type := ().

(** Head steps *)
Inductive head_step : expr → expr → Prop :=
(* β *)
| BetaS e1 e2 v2:
    to_val e2 = Some v2 →
    head_step (App (Lam e1) e2) e1.[e2/]
(* Products *)
| FstS e1 v1 e2 v2:
    to_val e1 = Some v1 → to_val e2 = Some v2 →
    head_step (Fst (Pair e1 e2)) e1
| SndS e1 v1 e2 v2:
    to_val e1 = Some v1 → to_val e2 = Some v2 →
    head_step (Snd (Pair e1 e2)) e2
(* Sums *)
| CaseLS e0 v0 e1 e2:
    to_val e0 = Some v0 →
    head_step (Case (InjL e0) e1 e2) e1.[e0/]
| CaseRS e0 v0 e1 e2:
    to_val e0 = Some v0 →
    head_step (Case (InjR e0) e1 e2) e2.[e0/]
(* Recursive Types *)
| Unfold_Fold e v:
    to_val e = Some v →
    head_step (Unfold (Fold e)) e
(** Casts *)
(* Between same base type *)
| IdBase e v:
    to_val e = Some v →
    head_step (Cast e TUnit TUnit) e
(* Between two times star *)
| IdStar e v:
    to_val e = Some v →
    head_step (Cast e TUnknown TUnknown) e
(* Between two ground types *)
| Same_Ground e v τ :
    to_val e = Some v →
    Ground τ →
    head_step (Cast (Cast e τ TUnknown) TUnknown τ) e
| Different_Ground e v τ1 τ2 (G1 : Ground τ1) (G2 : Ground τ2):
    to_val e = Some v →
    not (τ1 = τ2) →
    head_step (Cast (Cast e τ1 TUnknown) TUnknown τ2) CastError
(* Application of function that is casted between arrow types *)
| AppCast e1 v1 e2 v2 τ1 τ2 τ3 τ4:
    to_val e1 = Some v1 →
    to_val e2 = Some v2 →
    head_step
      (App (Cast e1 (TArrow τ1 τ2) (TArrow τ3 τ4)) e2)
      (Cast (App e1 (Cast e2 τ3 τ1)) τ2 τ4)
(* Cast between two product casts *)
| ProdCast e1 v1 e2 v2 τ1 τ2 τ1' τ2':
    to_val e1 = Some v1 →
    to_val e2 = Some v2 →
    head_step
      (Cast (Pair e1 e2) (TProd τ1 τ2) (TProd τ1' τ2'))
      (Pair (Cast e1 τ1 τ1') (Cast e2 τ2 τ2'))
| SumCast1 e1 v1 τ1 τ2 τ1' τ2':
    to_val e1 = Some v1 →
    head_step
      (Cast (InjL e1) (TSum τ1 τ2) (TSum τ1' τ2'))
      (InjL (Cast e1 τ1 τ1'))
| SumCast2 e2 v2 τ1 τ2 τ1' τ2':
    to_val e2 = Some v2 →
    head_step
      (Cast (InjR e2) (TSum τ1 τ2) (TSum τ1' τ2'))
      (InjR (Cast e2 τ2 τ2'))
| RecursiveCast e v τb τb':
    to_val e = Some v →
    head_step
      (Cast (Fold e) (TRec τb) (TRec τb'))
      (Fold (Cast e (τb.[TRec τb/]) (τb'.[TRec τb'/])))
(* Factorisations *)
| UpFactorization e v τ τG (G : get_shape τ = Some τG):
    to_val e = Some v →
    ((Ground τ) -> False) →
    (¬ (τ = TUnknown)) →
    head_step
      (Cast e τ TUnknown)
      (Cast (Cast e τ τG) τG TUnknown)
| DownFactorization e v τ τG (G : get_shape τ = Some τG):
    to_val e = Some v →
    (notT (Ground τ)) →
    (¬ (τ = TUnknown)) →
    head_step
      (Cast e TUnknown τ)
      (Cast (Cast e TUnknown τG) τG τ).

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  induction v; simplify_option_eq; try done.
  (* extra case *)
  destruct (ICP_dec τi τf).
  - rewrite IHv. simpl. by rewrite (Unique_ICP_proof τi τf Ip i).
  - (* impossible case *) exfalso. apply n. apply Ip.
Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  revert v; induction e; intros; simplify_option_eq; auto with f_equal.
  destruct (ICP_dec τi τf).
  - destruct (to_val e); simplify_option_eq; by rewrite IHe.
  - inversion H.
Qed.

Lemma val_head_stuck e1 e2 :
  head_step e1 e2 → to_val e1 = None.
Proof.
  destruct 1; try naive_solver.
  - simpl.
    destruct (ICP_dec TUnknown τ).
    destruct (Ground_dec τ); simplify_option_eq.
    inversion i. inversion G. done. done.
  - simpl.
    destruct (ICP_dec TUnknown τ2).
    destruct (Ground_dec τ1); simplify_option_eq.
    inversion i. inversion G. auto.
  - simpl.
    by destruct (Ground_dec τ); simplify_option_eq.
  - simpl.
    destruct (ICP_dec τ TUnknown).
    inversion i; by exfalso.
    destruct (ICP_dec TUnknown τ).
    inversion i. by exfalso.
    done.
Qed.

Instance of_val_inj : Inj (=) (=) of_val.
Proof. by intros ?? Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto.
destruct (ICP_dec τi τf).
  simplify_option_eq. by eexists. inversion H.
Qed.

Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq; auto with f_equal. Qed.

Lemma head_ctx_step_val Ki e e2 :
  head_step (fill_item Ki e) e2 → is_Some (to_val e).
Proof.
  destruct Ki; inversion_clear 1; simplify_option_eq; eauto.
  - simpl.
    destruct (Ground_dec τf); simplify_option_eq.
    by eexists.
    by exfalso.
  - destruct (Ground_dec τ1); simplify_option_eq.
    by eexists.
Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  destruct Ki1, Ki2; intros; try discriminate; simplify_eq;
  repeat match goal with
          | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
          end; auto.
Qed.

(** General evaluation contexts *)
Notation ectx := (list ectx_item).

Definition fill (K : ectx) (e : expr) : expr := foldl (flip fill_item) e K.

Instance fill_inj K : Inj (=) (=) (fill K).
Proof.
  induction K as [| Ki K IH]; rewrite /Inj; naive_solver.
Qed.

Notation observation := Empty_set.

(** Reduction relation of our language *)
Inductive prim_step : expr → list observation → expr → list expr → Prop :=
  | Ectx_step K e1 e1' e2 e2' :
    e1 = fill K e1' → e2 = fill K e2' →
    head_step e1' e2' → prim_step e1 [] e2 []
  | CastError_step K (ne : K ≠ []) :
    prim_step (fill K CastError) [] CastError [].

Lemma fill_item_not_val Ki e : to_val e = None → to_val (fill_item Ki e) = None.
Proof.
  destruct Ki; intro; simplify_option_eq; try done.
  rewrite to_of_val /= H; by simpl.
  by destruct ICP_dec; try done; rewrite H /=.
Qed.

Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
Proof.
  generalize dependent e.
  induction K. by simpl. intros. simpl. rewrite IHK; auto. by rewrite fill_item_not_val.
Qed.

Lemma val_prim_stuck e1 ks e2 ls : prim_step e1 ks e2 ls → to_val e1 = None.
Proof.
  destruct 1.
  - simplify_eq. apply fill_not_val.
    by eapply val_head_stuck.
  - apply fill_not_val. by simpl.
Qed.

Lemma lang_mixin : @LanguageMixin _ _ () Empty_set of_val to_val (fun e1 _ ls e2 _ ks => prim_step e1 ls e2 ks).
Proof.
  split; apply _ || intros; eauto using to_of_val, of_to_val, val_prim_stuck.
Qed.

Canonical Structure stateO := leibnizO state.
Canonical Structure valO := leibnizO val.
Canonical Structure exprO := leibnizO expr.

(** Defines language using the Iris `Language` structure *)
Canonical Structure lang : language := Language lang_mixin.

Hint Extern 20 (PureExec _ _ _) => progress simpl : typeclass_instances.

Hint Extern 5 (IntoVal _ _) => eapply of_to_val; fast_done : typeclass_instances.
Hint Extern 10 (IntoVal _ _) =>
  rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

Hint Extern 5 (AsVal _) => eexists; eapply of_to_val; fast_done : typeclass_instances.
Hint Extern 10 (AsVal _) =>
  eexists; rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

(** Definition of halting *)
Definition Halts (e : expr) :=
  ∃ v, rtc erased_step ([e], tt) ([of_val v], tt).
