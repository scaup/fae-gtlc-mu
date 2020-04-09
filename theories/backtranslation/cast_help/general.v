From fae_gtlc_mu.stlc_mu Require Export typing lang lib.fix.
From fae_gtlc_mu.cast_calculus Require Export types consistency.structural.definition.
From fae_gtlc_mu.backtranslation.cast_help Require Export universe embed extract between factorize.
(* From fae_gtlc_mu.backtranslation Require Export types de_bruijn_hell. *)

(** emulation of a cast between an arbitrary pair of consistent types *)
(* recursively defined on the alternative consistency relation *)

Fixpoint 𝓕 {A : list (types.type * types.type)} {τi τf : cast_calculus.types.type} (P : A ⊢ τi ~ τf) : expr :=
  match P with
  | consStarTGround _ τG G => extract τG G
  | consTGroundStar _ τG G => embed τG G
  | consTauStar _ τ τG pτnG pτnStar pτSτG pτConsτG =>
    factorization_up
      (𝓕 pτConsτG) τG (get_shape_is_ground pτSτG)
  | consStarTau _ τ τG pτnG pτnStar pτSτG pτGConsτ =>
    factorization_down
      (𝓕 pτGConsτ) τG (get_shape_is_ground pτSτG)
  | consBaseBase _ => identity
  | consStarStar _ => identity
  | consTSumTSum _ τ1 τ1' τ2 τ2' pCons1 pCons2 =>
    between_TSum
      (𝓕 pCons1)
      (𝓕 pCons2)
  | consTProdTProd _ τ1 τ1' τ2 τ2' pCons1 pCons2 =>
    between_TProd
      (𝓕 pCons1)
      (𝓕 pCons2)
  | consTArrowTArrow _ τ1 τ2 τ3 τ4 pCons31 pCons24 =>
    between_TArrow
      (𝓕 pCons31)
      (𝓕 pCons24)
  | consTRecTRecExposeCall _ τl τr pμτlμτrnotA pUnfτlUnfτr =>
    between_TRec
      (𝓕 pUnfτlUnfτr)
  (* | consTRecTRecUseCall _ τl τr i pμτlμtrinA => Lam ((Var (S i)) (Var 0)) *)
  | consTRecTRecUseCall _ τl τr i pμτlμtrinA => Var i
  end.

From fae_gtlc_mu.stlc_mu Require Export typing lang lib.fix.

Definition pair_to_static_function (p : cast_calculus.types.type * cast_calculus.types.type) : stlc_mu.typing.type :=
  TArrow <<p.1>> <<p.2>>.

Lemma 𝓕_typed (A : list (cast_calculus.types.type * cast_calculus.types.type)) (τi τf : cast_calculus.types.type) (pτi : TClosed τi) (pτf : TClosed τf) (pτiConsτf : A ⊢ τi ~ τf) :
  (map pair_to_static_function A) ⊢ₛ (𝓕 pτiConsτf) : (TArrow <<τi>> <<τf>>).
Proof.
  induction pτiConsτf; simpl.
  - apply extract_typed.
  - apply embed_typed.
  - apply factorization_up_typed.
    apply IHpτiConsτf.
    done. admit.
  - apply factorization_down_typed.
    apply IHpτiConsτf.
    admit. admit.
  - apply identity_typed.
  - apply identity_typed.
  - apply between_TSum_typed.
    apply IHpτiConsτf1.
    admit. admit.
    apply IHpτiConsτf2.
    admit. admit.
  - apply between_TProd_typed.
    apply IHpτiConsτf1.
    admit. admit.
    apply IHpτiConsτf2.
    admit. admit.
  - apply between_TArrow_typed.
    apply IHpτiConsτf1.
    admit. admit.
    apply IHpτiConsτf2.
    admit. admit.
  - apply between_TRec_typed.
    admit. admit.
    rewrite map_cons in IHpτiConsτf.
    repeat rewrite unfolding_backtranslation_commutes in IHpτiConsτf.
    apply IHpτiConsτf.
    admit. admit.
  - apply Var_typed.
    rewrite list_lookup_fmap.
    by rewrite pμτlμtrinA.
Admitted.


Definition 𝓕c {A} {τi τf} (pC : cons_struct A τi τf) fs : stlc_mu.lang.expr :=
  (𝓕 pC).[stlc_mu.typing.env_subst fs].

(** 𝓕 pC is a value after substitution *)

Definition 𝓕cV {A} {τi τf} (pC : cons_struct A τi τf) fs (H : length A = length fs) : stlc_mu.lang.val :=
  match to_val (𝓕c pC fs) with
  | Some x => x
  | None => UnitV
  end.

Lemma 𝓕c_rewrite {A} {τi τf} (pC : cons_struct A τi τf) fs (H : length A = length fs) : 𝓕c pC fs = # (𝓕cV pC fs H).
Proof.
  unfold 𝓕cV.
  destruct pC.
  - rewrite /𝓕c /𝓕. by rewrite extract_no_subs to_of_val.
  - rewrite /𝓕c /𝓕. by rewrite embed_no_subs to_of_val.
  - rewrite /𝓕c /𝓕. rewrite factorization_up_subst_rewrite. fold (𝓕 pC).
    by rewrite to_of_val.
  - rewrite /𝓕c /𝓕. rewrite factorization_down_subst_rewrite. fold (𝓕 pC).
    by rewrite to_of_val.
  - rewrite /𝓕c /𝓕. by asimpl.
  - rewrite /𝓕c /𝓕. by asimpl.
  - rewrite /𝓕c /𝓕. rewrite between_TSum_subst_rewrite.
    fold (𝓕 pC1).
    fold (𝓕 pC2).
    by rewrite to_of_val.
  - rewrite /𝓕c /𝓕. rewrite between_TProd_subst_rewrite.
    by rewrite to_of_val.
  - rewrite /𝓕c /𝓕. rewrite between_TArrow_subst_rewrite.
    by rewrite to_of_val.
  - rewrite /𝓕c /𝓕. rewrite between_TRec_subst_rewrite.
    by rewrite to_of_val.
  - rewrite /𝓕c /𝓕.
    assert (Hi : i < length fs). rewrite -H; apply lookup_lt_is_Some; by econstructor.
    destruct (fs !! i) eqn:Hf.
    simpl.
    erewrite env_subst_lookup. by rewrite to_of_val.
    apply Hf.
    exfalso.
    assert (length fs ≤ i). by apply lookup_ge_None_1.
    lia.
Qed.

Lemma 𝓕c_closed {A} {τi τf} (pC : cons_struct A τi τf) fs (H : length A = length fs) (Hfsc : Forall VClosed fs) :
  EClosed (𝓕c pC fs).
Proof.
  generalize dependent fs.
  induction pC; intros fs Hfs Hfsc; rewrite /𝓕c /𝓕.
  - intro. by repeat rewrite extract_no_subs.
  - intro. by repeat rewrite embed_no_subs.
  - fold (𝓕 pC). rewrite factorization_up_subst_rewrite. fold (𝓕c pC fs).
    intro. asimpl. rewrite embed_no_subs. by repeat rewrite IHpC.
  - fold (𝓕 pC). rewrite factorization_down_subst_rewrite. fold (𝓕c pC fs).
    intro. asimpl. rewrite extract_no_subs. by repeat rewrite IHpC.
  - intro; by asimpl.
  - intro; by asimpl.
  - fold (𝓕 pC1). fold (𝓕 pC2).
    rewrite between_TSum_subst_rewrite.
    fold (𝓕c pC1 fs). fold (𝓕c pC2 fs).
    intro; asimpl. repeat rewrite IHpC1; by repeat rewrite IHpC2.
  - fold (𝓕 pC1). fold (𝓕 pC2).
    rewrite between_TProd_subst_rewrite.
    fold (𝓕c pC1 fs). fold (𝓕c pC2 fs).
    intro; asimpl. repeat rewrite IHpC1; by repeat rewrite IHpC2.
  - fold (𝓕 pC1). fold (𝓕 pC2).
    rewrite between_TArrow_subst_rewrite.
    fold (𝓕c pC1 fs). fold (𝓕c pC2 fs).
    intro; asimpl. repeat rewrite IHpC1; by repeat rewrite IHpC2.
  - fold (𝓕 pC).
    rewrite between_TRec_subst_rewrite.
    intro.
    admit.
  - asimpl.
    assert (Hi : i < length fs). rewrite -Hfs; apply lookup_lt_is_Some; by econstructor.
    destruct (fs !! i) eqn:Hf.
    + rewrite (env_subst_lookup fs _ v).
      apply ve_closed.
      eapply (Forall_lookup_1). apply Hfsc. apply Hf. apply Hf.
    + exfalso.
      assert (length fs ≤ i). by apply lookup_ge_None_1.
      lia.
Admitted.
