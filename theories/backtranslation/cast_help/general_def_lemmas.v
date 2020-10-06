From fae_gtlc_mu.stlc_mu Require Export typing lang types_lemmas.
From fae_gtlc_mu.cast_calculus Require Export types types_lemmas.
From fae_gtlc_mu.backtranslation Require Export alternative_consistency types_lemmas.
From fae_gtlc_mu.backtranslation.cast_help Require Export universe embed extract between factorize general_def.
From Coq Require Export List.

(** 𝓕 pC is a value after substitution *)

Definition 𝓕cV {A} {τi τf} (pC : alternative_consistency A τi τf) fs (H : length A = length fs) : stlc_mu.lang.val :=
  match to_val (𝓕c pC fs) with
  | Some x => x
  | None => UnitV
  end.

Lemma 𝓕c_rewrite {A} {τi τf} (pC : alternative_consistency A τi τf) fs (H : length A = length fs) : 𝓕c pC fs = # (𝓕cV pC fs H).
Proof.
  unfold 𝓕cV.
  destruct pC.
  - rewrite /𝓕c /𝓕. by rewrite extract_no_subs to_of_val.
  - rewrite /𝓕c /𝓕. by rewrite embed_no_subs to_of_val.
  - rewrite /𝓕c /𝓕. rewrite factorization_subst_rewrite. fold (𝓕 pC1). fold (𝓕 pC2).
    by rewrite to_of_val.
  - rewrite /𝓕c /𝓕. rewrite factorization_subst_rewrite. fold (𝓕 pC2). fold (𝓕 pC2).
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


From fae_gtlc_mu.stlc_mu Require Export lang.

Lemma expr_double_subst (e : expr) σ1 σ2 : e.[σ1].[σ2] = e.[σ1 >> σ2].
Proof. by asimpl. Qed.

Definition VClosed (v : val) := Closed (# v).

Lemma 𝓕c_closed_gen {A} {τi τf} (pC : alternative_consistency A τi τf) fs (Hfsc : Forall VClosed fs) :
  forall n, (length A = n + length fs) → forall σ, (𝓕 pC).[upn n (env_subst fs)].[upn n σ] = (𝓕 pC).[upn n (env_subst fs)].
Proof.
  generalize dependent fs.
  induction pC; intros fs Hfsc; rewrite /𝓕c /𝓕; intros n H.
  - intro. by repeat rewrite extract_no_subs.
  - intro. by repeat rewrite embed_no_subs.
  - intro. fold (𝓕 pC1). fold (𝓕 pC2).
    rewrite expr_double_subst. do 2 rewrite factorization_subst_rewrite.
    do 2 rewrite -expr_double_subst.
    rewrite IHpC1; auto. rewrite IHpC2; auto.
  - intro. fold (𝓕 pC1). fold (𝓕 pC2).
    rewrite expr_double_subst. do 2 rewrite factorization_subst_rewrite.
    do 2 rewrite -expr_double_subst.
    rewrite IHpC1; auto. rewrite IHpC2; auto.
  - intro; by asimpl.
  - intro; by asimpl.
  - fold (𝓕 pC1). fold (𝓕 pC2). intro σ.
    rewrite expr_double_subst. do 2 rewrite between_TSum_subst_rewrite.
    do 2 rewrite -expr_double_subst.
    rewrite IHpC1; auto. rewrite IHpC2; auto.
  - fold (𝓕 pC1). fold (𝓕 pC2). intro σ.
    rewrite expr_double_subst. do 2 rewrite between_TProd_subst_rewrite.
    do 2 rewrite -expr_double_subst.
    rewrite IHpC1; auto. rewrite IHpC2; auto.
  - fold (𝓕 pC1). fold (𝓕 pC2). intro σ.
    rewrite expr_double_subst. do 2 rewrite between_TArrow_subst_rewrite.
    do 2 rewrite -expr_double_subst.
    rewrite IHpC1; auto. rewrite IHpC2; auto.
  - fold (𝓕 pC). intro σ.
    rewrite expr_double_subst. do 2 rewrite between_TRec_subst_rewrite.
    cut (# between_TRec (𝓕 pC).[upn (S n) (env_subst fs)].[upn (S n) σ] = # between_TRec (𝓕 pC).[upn (S n) (env_subst fs)]). by asimpl.
    rewrite IHpC; auto. simpl. lia.
  - intro σ. asimpl.
    destruct (iter_up_cases i n (env_subst fs)) as [[-> eq] | [j [-> ->]]].
    + asimpl. by rewrite upn_lt.
    + assert (Hnj : n + j < length A). apply lookup_lt_is_Some. by econstructor. rewrite H in Hnj.
      assert (Hj : j < length fs). lia.
      destruct (fs !! j) eqn:Hf.
      * rewrite (env_subst_lookup fs _ v).
        assert (vc : VClosed v). eapply (Forall_lookup_1). apply Hfsc. apply Hf.
        asimpl. by do 2 rewrite vc. auto.
      * assert (length fs ≤ j). by apply lookup_ge_None_1. exfalso; lia.
Qed.


Lemma 𝓕c_closed {A} {τi τf} (pC : alternative_consistency A τi τf) fs (H : length A = length fs) (Hfsc : Forall VClosed fs) :
  Closed (𝓕c pC fs).
Proof.
  intro σ. rewrite /𝓕c. cut ((𝓕 pC).[upn 0 (env_subst fs)].[upn 0 σ] = (𝓕 pC).[upn 0 (env_subst fs)]). by asimpl.
  by apply 𝓕c_closed_gen.
Qed.
