From Autosubst Require Export Autosubst.
From iris.program_logic Require Export language ectx_language ectxi_language.
From fae_gtlc_mu Require Export cast_calculus.types.

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
(* We are not going to ask for a proof of τi ~ τf... only in type-checking *)
| Blame.

Instance Ids_expr : Ids expr. derive. Defined.
Instance Rename_expr : Rename expr. derive. Defined.
Instance Subst_expr : Subst expr. derive. Defined.
Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.

Inductive val :=
| LamV (e : {bind 1 of expr})
| UnitV
| PairV (v1 v2 : val)
| InjLV (v : val)
| InjRV (v : val)
| FoldV (v : val)
| CastV (v : val) (τi τf : type) (Ip : Inert_cast_pair τi τf).

Fixpoint of_val (v : val) : expr :=
  match v with
  | LamV e => Lam e
  | UnitV => Unit
  | PairV v1 v2 => Pair (of_val v1) (of_val v2)
  | InjLV v => InjL (of_val v)
  | InjRV v => InjR (of_val v)
  | FoldV v => Fold (of_val v)
  | CastV v τi τf _ => Cast (of_val v) τi τf
  end.
Notation "# v" := (of_val v) (at level 20).

Definition Inert_cast_pair_dec (τi τf : type) : Decision (Inert_cast_pair τi τf).
destruct τf.
  - apply right. intro aaa. inversion aaa.
  - apply right. intro aaa. inversion aaa.
  - apply right. intro aaa. inversion aaa.
  - destruct τi.
    + apply right. intro aaa. inversion aaa.
    + apply right. intro aaa. inversion aaa.
    + apply right. intro aaa. inversion aaa.
    + apply left. constructor.
    + apply right. intro aaa. inversion aaa.
    + apply right. intro aaa. inversion aaa.
    + apply right. intro aaa. inversion aaa.
  - apply right. intro aaa. inversion aaa.
  - apply right. intro aaa. inversion aaa.
  - destruct (Ground_dec τi).
    + apply left. by constructor.
    + apply right. intro aaa. inversion aaa. by apply n.
Defined.

Fixpoint to_val (e : expr) : option val :=
  match e with
  | Lam e => Some (LamV e)
  | Unit => Some UnitV
  | Pair e1 e2 => v1 ← to_val e1; v2 ← to_val e2; Some (PairV v1 v2)
  | InjL e => InjLV <$> to_val e
  | InjR e => InjRV <$> to_val e
  | Fold e => v ← to_val e; Some (FoldV v)
  | Cast e τi τf => match (Inert_cast_pair_dec τi τf) with
                     | left Ip => v ← to_val e; Some (CastV v τi τf Ip)
                     | right _ => None
                   end
  | Var _ => None
  | App _ _ => None
  | Fst _ => None
  | Snd _ => None
  | Case _ _ _ => None
  | Unfold _ => None
  | Blame => None
  end.

(** Evaluation contexts *)
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

Inductive head_step : expr → state → list Empty_set → expr → state → list expr → Prop :=
(* β *)
| BetaS e1 e2 v2 σ :
    to_val e2 = Some v2 →
    head_step (App (Lam e1) e2) σ [] e1.[e2/] σ []
(* Products *)
| FstS e1 v1 e2 v2 σ :
    to_val e1 = Some v1 → to_val e2 = Some v2 →
    head_step (Fst (Pair e1 e2)) σ [] e1 σ []
| SndS e1 v1 e2 v2 σ :
    to_val e1 = Some v1 → to_val e2 = Some v2 →
    head_step (Snd (Pair e1 e2)) σ [] e2 σ []
(* Sums *)
| CaseLS e0 v0 e1 e2 σ :
    to_val e0 = Some v0 →
    head_step (Case (InjL e0) e1 e2) σ [] e1.[e0/] σ []
| CaseRS e0 v0 e1 e2 σ :
    to_val e0 = Some v0 →
    head_step (Case (InjR e0) e1 e2) σ [] e2.[e0/] σ []
(* Recursive Types *)
| Unfold_Fold e v σ :
    to_val e = Some v →
    head_step (Unfold (Fold e)) σ [] e σ []
(** Casts *)
(* Between same base type *)
| IdBase e v σ :
    to_val e = Some v →
    head_step (Cast e TUnit TUnit) σ [] e σ []
(* Between two times star *)
| IdStar e v σ :
    to_val e = Some v →
    head_step (Cast e ⋆ ⋆) σ [] e σ []
(* Between two ground types *)
| Same_Ground e v σ τ :
    to_val e = Some v →
    Ground τ →
    head_step (Cast (Cast e τ ⋆) ⋆ τ) σ [] e σ []
| Different_Ground e v σ τ1 τ2 (G1 : Ground τ1) (G2 : Ground τ2):
    to_val e = Some v →
    not (Ground_equal G1 G2) →
    head_step (Cast (Cast e τ1 ⋆) ⋆ τ2) σ [] Blame σ []
(* Application of function that is casted between arrow types *)
| AppCast e1 e2 v2 τ1 τ2 τ3 τ4 σ:
    to_val e2 = Some v2 →
    head_step
      (App (Cast (Lam e1) (TArrow τ1 τ2) (TArrow τ3 τ4)) e2) σ []
      (Cast (App e1 (Cast e2 τ3 τ1)) τ2 τ4) σ []
(* Cast between two product casts *)
| ProdCast e v τ1 τ2 τ1' τ2' σ:
    to_val e = Some v →
    head_step
      (Cast e (TProd τ1 τ2) (TProd τ1' τ2')) σ []
      (Pair (Cast (Fst e) τ1 τ1') (Cast (Snd e) τ2 τ2')) σ []
(* Cast between two sum casts *)
| SumCast e v τ1 τ2 τ1' τ2' σ:
    to_val e = Some v →
    head_step
      (Cast e (TSum τ1 τ2) (TSum τ1' τ2')) σ []
      (Case e (Cast (Var 0) τ1 τ1') (Cast (Var 0) τ2 τ2')) σ []
(* Cast between two recursive casts *)
| RecursiveCast e v τb τb' σ:
    to_val e = Some v →
    head_step
      (Cast e (TRec τb) (TRec τb')) σ []
      (Fold (Cast (Unfold e) (τb.[TRec τb/]) (τb'.[TRec τb'/]))) σ []
(* Factorisations *)
| UpFactorization e v τ τG (G : Ground τG) σ :
    to_val e = Some v →
    (¬ Ground τ) →
    (¬ (τ = ⋆)) →
    open_sym τ τG →
    head_step
      (Cast e τ ⋆) σ []
      (Cast (Cast e τ τG) τG ⋆) σ []
| DownFactorization e v τ τG (G : Ground τG) σ :
    to_val e = Some v →
    (¬ Ground τ) →
    (¬ (τ = ⋆)) →
    open_sym τ τG →
    head_step
      (Cast e ⋆ τ) σ []
      (Cast (Cast e ⋆ τG) τG τ) σ []
(* Let Blame diverge *)
| BlameDiverge σ :
    head_step
      Blame σ []
      Blame σ [].

(** Basic properties about the language *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  induction v; simplify_option_eq; try done.
  (* extra case *)
  destruct (Inert_cast_pair_dec τi τf).
  - rewrite IHv. simpl. by rewrite (Unique_Inert_cast_pair_proof τi τf Ip i).
  - (* impossible case *) exfalso. apply n. apply Ip.
Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  revert v; induction e; intros; simplify_option_eq; auto with f_equal.
  destruct (Inert_cast_pair_dec τi τf).
  - destruct (to_val e); simplify_option_eq; by rewrite IHe.
  - inversion H.
Qed.

Instance of_val_inj : Inj (=) (=) of_val.
Proof. by intros ?? Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto.
destruct (Inert_cast_pair_dec τi τf).
  simplify_option_eq. by eexists. inversion H.
Qed.

Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq; auto with f_equal. Qed.

Lemma val_stuck e1 σ1 κ e2 σ2 ef :
  head_step e1 σ1 κ e2 σ2 ef → to_val e1 = None.
Proof.
  destruct 1; try naive_solver.
  - simpl.
    destruct (Inert_cast_pair_dec ⋆ τ).
    destruct (Ground_dec τ); simplify_option_eq.
    inversion i. inversion G. done. done.
  - simpl.
    destruct (Inert_cast_pair_dec ⋆ τ2).
    destruct (Ground_dec τ1); simplify_option_eq.
    inversion i. inversion G. auto. auto.
  - simpl.
    by destruct (Ground_dec τ); simplify_option_eq.
  - simpl.
    destruct (Inert_cast_pair_dec τ ⋆).
    inversion i; by exfalso.
    destruct (Inert_cast_pair_dec ⋆ τ).
    inversion i. by exfalso.
    done.
Qed.

Lemma head_ctx_step_val Ki e σ1 κ e2 σ2 ef :
  head_step (fill_item Ki e) σ1 κ e2 σ2 ef → is_Some (to_val e).
Proof. destruct Ki; inversion_clear 1; simplify_option_eq; eauto.
  - simpl.
    destruct (Ground_dec τf); simplify_option_eq.
    by eexists.
    by exfalso.
  - destruct (Ground_dec τ1); simplify_option_eq.
    by eexists.
    by exfalso.
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

Lemma val_head_stuck e1 σ1 κ e2 σ2 efs : head_step e1 σ1 κ e2 σ2 efs → to_val e1 = None.
Proof. destruct 1; try naive_solver.
  - simpl.
    destruct (Inert_cast_pair_dec ⋆ τ).
    destruct (Ground_dec τ); simplify_option_eq.
    inversion i. inversion G. done. done.
  - simpl.
    destruct (Inert_cast_pair_dec ⋆ τ2).
    destruct (Ground_dec τ1); simplify_option_eq.
    inversion i. inversion G. auto. auto.
  - destruct (Inert_cast_pair_dec τ ⋆).
    by inversion i.
    simpl.
    by destruct (Ground_dec τ); simplify_option_eq.
  - destruct (Inert_cast_pair_dec ⋆ τ).
    by inversion i.
    simpl.
    destruct (Inert_cast_pair_dec ⋆ τ).
    by exfalso; done. done.
Qed.

Lemma lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
          fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
Qed.

Canonical Structure stateO := leibnizO state.
Canonical Structure valO := leibnizO val.
Canonical Structure exprO := leibnizO expr.

(** Language *)
Canonical Structure ectxi_lang := EctxiLanguage lang_mixin.
Canonical Structure ectx_lang := EctxLanguageOfEctxi ectxi_lang.
Canonical Structure lang := LanguageOfEctx ectx_lang.

Hint Extern 20 (PureExec _ _ _) => progress simpl : typeclass_instances.

Hint Extern 5 (IntoVal _ _) => eapply of_to_val; fast_done : typeclass_instances.
Hint Extern 10 (IntoVal _ _) =>
  rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

Hint Extern 5 (AsVal _) => eexists; eapply of_to_val; fast_done : typeclass_instances.
Hint Extern 10 (AsVal _) =>
  eexists; rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.
