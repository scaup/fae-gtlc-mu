From fae_gtlc_mu.cast_calculus Require Export types.
From fae_gtlc_mu.backtranslation Require Import cast_help.universe.
From fae_gtlc_mu.stlc_mu Require Export types.
From fae_gtlc_mu Require Export prelude.

Reserved Notation "<< τ >>" (at level 4, τ at next level).
Fixpoint backtranslate_type (τ : cast_calculus.types.type) : type :=
  match τ with
  | cast_calculus.types.TUnit => TUnit
  | cast_calculus.types.TProd τ1 τ2 => TProd <<τ1>> <<τ2>>
  | cast_calculus.types.TSum τ1 τ2 => TSum <<τ1>> <<τ2>>
  | cast_calculus.types.TArrow τ1 τ2 => TArrow <<τ1>> <<τ2>>
  | cast_calculus.types.TRec τ => TRec <<τ>>
  | cast_calculus.types.TVar x => TVar x
  | cast_calculus.types.TUnknown => Universe
  end where "<< e >>" := (backtranslate_type e).

(* Lemma back_Ground_closed {τG} (G : Ground τG) : Closed <<τG>>. *)
(* Proof. destruct G; intro σ; simpl; by repeat rewrite Universe_closed. Qed. *)

(* Lemma btype_ren_gen τ : *)
(*   forall k l, << τ.[upn l (ren (+k))] >> = <<τ>>.[upn l (ren (+k))]. *)
(* Proof. *)
(*   induction τ; intros k l; try by asimpl. *)
(*   - asimpl. by rewrite IHτ1 IHτ2. *)
(*   - asimpl. by rewrite IHτ1 IHτ2. *)
(*   - asimpl. by rewrite IHτ1 IHτ2. *)
(*   - simpl. specialize (IHτ k (S l)). by rewrite IHτ. *)
(*   - asimpl. do 2 rewrite (iter_up l x (ren (+k))). *)
(*     destruct (lt_dec x l); by asimpl. *)
(* Qed. *)

(* Lemma back_unfold_comm_gen (τb : cast_calculus.types.type) : forall (τ : cast_calculus.types.type) k, *)
(*   << τb.[upn k (τ .: ids)] >> = <<τb>>.[upn k (<<τ>> .: ids)]. *)
(* Proof. *)
(*   induction τb; intros τ' k; try by asimpl. *)
(*   - asimpl. by rewrite IHτb1 IHτb2. *)
(*   - asimpl. by rewrite IHτb1 IHτb2. *)
(*   - asimpl. by rewrite IHτb1 IHτb2. *)
(*   - simpl. specialize (IHτb τ' (S k)). by rewrite IHτb. *)
(*   - asimpl. *)
(*     rewrite (iter_up k x (τ' .: ids)) (iter_up k x (<<τ'>> .: ids)). *)
(*     destruct (lt_dec x k). *)
(*       + by asimpl. *)
(*       + destruct (decide (x - k = 0)); asimpl. rewrite e. asimpl. *)
(*         cut (<< τ'.[upn 0 (ren (+k))] >> = (<< τ' >>).[upn 0 (ren (+k))]). *)
(*         by asimpl. by rewrite btype_ren_gen. *)
(*         destruct (x - k). exfalso; lia. by asimpl. *)
(* Qed. *)

(* Lemma back_unfold_comm (τb : cast_calculus.types.type) : *)
(*   << τb.[cast_calculus.types.TRec τb/]>> = <<τb>>.[TRec <<τb>>/]. *)
(* Proof. *)
(*   cut (<< (τb.[upn 0 ((cast_calculus.types.TRec τb) .: ids)])>> = <<τb>>.[upn 0 (<<(cast_calculus.types.TRec τb)>> .: ids)]). *)
(*   by asimpl. apply back_unfold_comm_gen. *)
(* Qed. *)

(* Lemma back_closed_gen τ : forall n (pnτ : NClosed n τ), NClosed n <<τ>>. *)
(* Proof. *)
(*   induction τ; intros n pnτ; simpl; try by (intro σ; by asimpl). *)
(*   - specialize (IHτ1 n (TProd_nclosed1 pnτ)). *)
(*     specialize (IHτ2 n (cast_calculus.types.TProd_nclosed2 pnτ)). *)
(*     intro σ; asimpl; by rewrite IHτ1 IHτ2. *)
(*   - specialize (IHτ1 n (cast_calculus.types.TSum_nclosed1 pnτ)). *)
(*     specialize (IHτ2 n (cast_calculus.types.TSum_nclosed2 pnτ)). *)
(*     intro σ; asimpl; by rewrite IHτ1 IHτ2. *)
(*   - specialize (IHτ1 n (cast_calculus.types.TArrow_nclosed1 pnτ)). *)
(*     specialize (IHτ2 n (cast_calculus.types.TArrow_nclosed2 pnτ)). *)
(*     intro σ; asimpl; by rewrite IHτ1 IHτ2. *)
(*   - specialize (IHτ (S n) (cast_calculus.types.TRec_nclosed1 pnτ)). *)
(*     intro σ; asimpl; by rewrite IHτ. *)
(*   - apply NClosed_var. by apply cast_calculus.types.NClosed_var. *)
(* Qed. *)

(* Lemma back_closed {τ} (pτ : cast_calculus.types.Closed τ) : Closed <<τ>>. *)
(* Proof. apply (back_closed_gen τ 0 pτ). Qed. *)
