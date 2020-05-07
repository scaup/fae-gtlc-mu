From fae_gtlc_mu Require Import stlc_mu.typing.
From fae_gtlc_mu Require Import cast_calculus.types.

Reserved Notation "[| τ |]" (at level 4, τ at next level).
Fixpoint embed_type (τ : stlc_mu.types.type) : type :=
  match τ with
  | stlc_mu.types.TUnit => TUnit
  | stlc_mu.types.TProd τ1 τ2 => TProd [| τ1 |] [| τ2 |]
  | stlc_mu.types.TSum τ1 τ2 => TSum [| τ1 |] [| τ2 |]
  | stlc_mu.types.TArrow τ1 τ2 => TArrow [| τ1 |] [| τ2 |]
  | stlc_mu.types.TRec τb => TRec [| τb |]
  | stlc_mu.types.TVar x => TVar x
  end where "[| e |]" := (embed_type e).

Lemma etype_ren_gen τ :
  forall k l, [| τ.[upn l (ren (+k))] |] = [|τ|].[upn l (ren (+k))].
Proof.
  induction τ; intros k l; try by asimpl.
  - asimpl. by rewrite IHτ1 IHτ2.
  - asimpl. by rewrite IHτ1 IHτ2.
  - asimpl. by rewrite IHτ1 IHτ2.
  - simpl. specialize (IHτ k (S l)). by rewrite IHτ.
  - asimpl. do 2 rewrite (iter_up l x (ren (+k))).
    destruct (lt_dec x l); by asimpl.
Qed.

Lemma embd_unfold_comm_gen (τb : stlc_mu.types.type) : forall (τ : stlc_mu.types.type) k,
  [| τb.[upn k (τ .: ids)] |] = [|τb|].[upn k ([|τ|] .: ids)].
Proof.
  induction τb; intros τ' k; try by asimpl.
  - asimpl. by rewrite IHτb1 IHτb2.
  - asimpl. by rewrite IHτb1 IHτb2.
  - asimpl. by rewrite IHτb1 IHτb2.
  - simpl. specialize (IHτb τ' (S k)). by rewrite IHτb.
  - asimpl.
    rewrite (iter_up k x (τ' .: ids)) (iter_up k x ([|τ'|] .: ids)).
    destruct (lt_dec x k).
      + by asimpl.
      + destruct (decide (x - k = 0)); asimpl. rewrite e. asimpl.
        cut ([| τ'.[upn 0 (ren (+k))] |] = ([| τ' |]).[upn 0 (ren (+k))]).
        by asimpl. by rewrite etype_ren_gen.
        destruct (x - k). exfalso; lia. by asimpl.
Qed.

Lemma embd_unfold_comm (τb : stlc_mu.types.type) :
  [| τb.[stlc_mu.types.TRec τb/]|] = [|τb|].[TRec [|τb|]/].
Proof.
  cut ([| (τb.[upn 0 ((stlc_mu.types.TRec τb) .: ids)])|] = [|τb|].[upn 0 ([|(stlc_mu.types.TRec τb)|] .: ids)]).
  by asimpl. apply embd_unfold_comm_gen.
Qed.

Lemma embd_closed_gen τ : forall n (pnτ : stlc_mu.types.TnClosed n τ), TnClosed n [|τ|].
Proof.
  induction τ; intros n pnτ; simpl; try by (intro σ; by asimpl).
  - specialize (IHτ1 n (stlc_mu.types.TProd_nclosed1 pnτ)).
    specialize (IHτ2 n (stlc_mu.types.TProd_nclosed2 pnτ)).
    intro σ; asimpl; by rewrite IHτ1 IHτ2.
  - specialize (IHτ1 n (stlc_mu.types.TSum_nclosed1 pnτ)).
    specialize (IHτ2 n (stlc_mu.types.TSum_nclosed2 pnτ)).
    intro σ; asimpl; by rewrite IHτ1 IHτ2.
  - specialize (IHτ1 n (stlc_mu.types.TArrow_nclosed1 pnτ)).
    specialize (IHτ2 n (stlc_mu.types.TArrow_nclosed2 pnτ)).
    intro σ; asimpl; by rewrite IHτ1 IHτ2.
  - specialize (IHτ (S n) (stlc_mu.types.TRec_nclosed1 pnτ)).
    intro σ; asimpl; by rewrite IHτ.
  - apply TnClosed_var. by apply stlc_mu.types.TnClosed_var.
Qed.

Lemma embd_closed {τ} (pτ : stlc_mu.types.TClosed τ) : TClosed [|τ|].
Proof. apply (embd_closed_gen τ 0 pτ). Qed.
