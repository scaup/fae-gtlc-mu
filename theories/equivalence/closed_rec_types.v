From iris Require Export base.
From stdpp Require Export base list sets mapset.
(* From stdpp Require Import base binders boolset coGset coPset countable decidable finite fin_map_dom fin_maps fin_sets fin functions gmap gmultiset hashset hlist infinite lexico listset_nodup listset list mapset namespaces nat_cancel natmap nmap numbers option orders pmap pretty proof_irrel propset relations sets sorting streams stringmap strings tactics telescopes vector. *)
(* fhin_sets fin_maps. *)
From Autosubst Require Export Autosubst.
Require Export Utf8_core.
From fae_gtlc_mu.equivalence Require Import types listset_ext.

Fixpoint closed_rec_types (τ : type) : listset type :=
  match τ with
  | TUnit => ∅
  | TArrow τ1 τ2 => closed_rec_types τ1 ∪ closed_rec_types τ2
  | TRec τb => {[ TRec τb ]} ∪ fmap (subst (TRec τb .: ids)) (closed_rec_types τb)
  | TVar x => ∅
  | TUnknown => ∅
  end.

From Coq Require Import Relation_Operators Operators_Properties.

Inductive p_le_pre : type → type → Prop :=
  | arrow_l_p_le_pre τ τ' : p_le_pre τ (TArrow τ τ')
  | arrow_r_p_le_pre τ τ' : p_le_pre τ' (TArrow τ τ').

Definition p_le : type → type → Prop := rtc p_le_pre.

Fixpoint subst_chain (ch : list type) : var → type :=
  match ch with
  | nil => ids
  | cons τ1 ch => ((TRec τ1) .: ids) >> subst_chain ch
  end.

Fixpoint subst_chains_fmap (pk : list type) (pn : list type) : var → type :=
  match pk with
  | nil => ids
  | cons α1 αs => (((TRec α1).[upn (length αs) (subst_chain pn)]) .: ids) >> subst_chains_fmap αs pn
  end.

Lemma subst_chains_fmap_nil (pk : list type) : subst_chains_fmap pk [] = subst_chain pk.
Proof.
  induction pk; try by simpl.
  simpl. rewrite up_id_n. rewrite IHpk. by rewrite up_id subst_id.
Qed.

Inductive Chain : type → type → list type → Prop :=
  | nil_Chain α τ (p : p_le α τ) : Chain α τ []
  | cons_Chain α τ0 (p0 : p_le α τ0) τ1 (p : p_le (TRec τ0) τ1) τn (ls : list type) (pc : Chain τ1 τn ls) :
      Chain α τn (τ0 :: ls).

Lemma chain_diff_prefix α α' τ pn : Chain α' τ pn → p_le α α' → Chain α τ pn.
Proof.
  inversion 1.
  - simplify_eq.
    intro. apply nil_Chain. by eapply rtc_transitive.
  - simplify_eq.
    intro. eapply cons_Chain. by eapply rtc_transitive. apply p. apply pc.
Qed.

Lemma chain_diff_suffix α τ τ' pn : Chain α τ pn → p_le τ τ' → Chain α τ' pn.
Proof.
  induction 1.
  - intros. simplify_eq.
    apply nil_Chain. by eapply rtc_transitive.
  - intros. eapply cons_Chain. apply p0. apply p. by apply IHChain.
Qed.

Lemma app_Chain (pk pn : list type) (α1 τ1 τn : type) (pchk : Chain α1 τ1 pk) (pchn : Chain τ1 τn pn) : Chain α1 τn (pk ++ pn).
Proof.
  generalize dependent α1.
  generalize dependent pn.
  induction pk as [| α1' pk ].
  - intros. simpl. inversion_clear pchk.
    eapply chain_diff_prefix. apply pchn. apply p.
  - intros. inversion pchk; simplify_eq.
    eapply cons_Chain. auto. apply p. fold (app pk ( pn)).
    apply IHpk; auto.
Qed.

Lemma subst_chain_subst_chains_fmap (pk pn : list type) :
      upn (length pk) (subst_chain pn) >> subst_chains_fmap pk pn = subst_chain (pk ++ pn).
Proof.
  induction pk as [|α1 pk].
  - by asimpl.
  - simpl; rewrite -subst_through_rec -scomp_assoc subst_commut.
    fold (iterate up).
    by rewrite scomp_assoc IHpk.
Qed.

Lemma var_subst_chain j pn : ((j < length pn) * { p : type | pn !! j = Some p ∧ (TRec p).[subst_chain (drop (S j) pn)] = (TVar j).[subst_chain pn] }) +
                             (length pn ≤ j ∧ (TVar j).[subst_chain pn] = (TVar (j - length pn))).
Proof.
  destruct (decide (j < length pn)).
  - left. split. auto.
    destruct (pn !! j) eqn:eq.
    + exists t. split. auto.
      generalize dependent j.
      induction pn.
      * intros. exfalso. simpl in l. lia.
      * intros. destruct j. simpl in *. inversion eq.
        simplify_eq. by simpl.
        simpl. rewrite -subst_through_rec.
        simpl in l.
        apply IHpn. lia. simpl in eq.  auto.
    + exfalso. assert (H : length pn ≤ j). by apply lookup_ge_None.
      lia.
  - right. split. lia.
    generalize dependent j.
    induction pn. intros. simpl. f_equal. lia.
    destruct j. intros. exfalso. simpl in n. lia.
    intros. assert (triv : (TVar (S j)).[subst_chain (a :: pn)] = (TVar j).[subst_chain pn]).
    by asimpl. rewrite triv. rewrite (IHpn j). by simpl. simpl in n. lia.
Qed.

Lemma drop_Chain τ0 τ ls x τx (pchn : Chain τ0 τ ls)
      (Hx : x < length ls)
      (Hlsx : ls !! x = Some τx) : Chain (TRec τx) τ (drop (S x) ls).
Proof.
  generalize dependent ls.
  generalize dependent τ0.
  induction x.
  - intros.
    destruct ls. inversion Hlsx. inversion Hlsx.
    inversion pchn. inversion Hx.
    simplify_eq. simpl. rewrite drop_0.
    eapply chain_diff_prefix. apply pc. done.
    simplify_eq. simpl. rewrite drop_0.
    eapply chain_diff_prefix. apply pc. done.
  - intros.
    destruct ls. inversion Hlsx.
    inversion pchn. simplify_eq.
    simpl. eapply IHx.
    apply pc. simpl in *. lia.
    by simpl in *.
Qed.

Lemma subst_chain_app (ls ks : list type) : subst_chain (ls ++ ks) = subst_chain ls >> subst_chain ks.
Proof. induction ls. by asimpl. simpl. rewrite IHls. by asimpl. Qed.

Lemma split_Chain (ls ks : list type) τ1 τ : Chain τ1 τ (ls ++ ks) → exists δ, Chain τ1 δ ls ∧ Chain δ τ ks.
Proof.
  generalize dependent τ1.
  induction ls.
  - intros. simpl in *. exists τ1. split. apply nil_Chain. apply rtc_refl. auto.
  - simpl in *. intros. inversion H. simplify_eq.
    specialize (IHls τ2 pc).
    destruct IHls as [δ [H1 H2]].
    exists δ. split. eapply cons_Chain. apply p0. apply p. auto. auto.
Qed.

Lemma chop_off_last {A} (ls : list A) n : length ls = S n → exists ks x, ls = ks ++ [x].
Proof.
  intro.
  generalize dependent n.
  induction ls.
  - intros. exfalso. simpl in H. lia.
  - intros. destruct n.
    + simpl in H. inversion H. destruct ls. exists [], a. by simpl. inversion H1.
    + simpl in H. inversion H. destruct (IHls n H1) as [ks [x ->]].
      exists (a :: ks), x. by simpl.
Qed.

Lemma mono_map_subseteq {A B : Type} (f : A → B) (ls ks : listset A) : ls ⊆ ks → f <$> ls ⊆ f <$> ks.
Proof. intro. set_solver. Qed.

Lemma le_TUnit τ : p_le τ TUnit → τ = TUnit.
Proof.
  intro. apply (@rtc_ind_l _ p_le_pre (fun τ : type => (τ = TUnit)) TUnit); auto.
  intros. inversion H0; rewrite H2 in H4; inversion H4.
Qed.

Lemma le_TVar τ x : p_le τ (TVar x) → τ = (TVar x).
Proof.
  intro. apply (@rtc_ind_l _ p_le_pre (fun τ : type => (τ = TVar x)) (TVar x)); auto.
  intros. inversion H0; rewrite H2 in H4; inversion H4.
Qed.

Lemma le_TUnknown τ : p_le τ TUnknown → τ = TUnknown.
Proof.
  intro. apply (@rtc_ind_l _ p_le_pre (fun τ : type => (τ = TUnknown)) TUnknown); auto.
  intros. inversion H0; rewrite H2 in H4; inversion H4.
Qed.

Lemma le_TArrow τ τ1 τ2 : p_le τ (TArrow τ1 τ2) → τ = TArrow τ1 τ2 ∨ p_le τ τ1 ∨ p_le τ τ2.
Proof.
  intro.
  apply (@rtc_ind_l _ p_le_pre (fun τ' : type => (τ' = TArrow τ1 τ2 ∨ p_le τ' τ1 ∨ p_le τ' τ2)) (TArrow τ1 τ2)).
  - by left.
  - intros. destruct H2 as [-> | [p1 | p2] ].
    + inversion H0; simplify_eq.
      * right. left. by constructor.
      * right. right. by constructor.
    + right. left. by econstructor.
    + right. right. by econstructor.
  - auto.
Qed.

Lemma le_TRec τ τ' : p_le τ (TRec τ') → τ = TRec τ'.
Proof.
  intro.
  apply (@rtc_ind_l _ p_le_pre (fun τ : type => (τ = TRec τ')) (TRec τ')); auto.
  intros. simplify_eq. inversion H0.
Qed.

Lemma chain_off_last (ls : list type) α τ n : length ls = S n → Chain α τ ls → exists ks δ, ls = ks ++ [δ] ∧ Chain α δ ks ∧ p_le (TRec δ) τ.
Proof.
  intros Hls pchn.
  destruct (chop_off_last ls n Hls) as [ks [z ->]].
  destruct (split_Chain ks [z] _ _ pchn) as [δ [Hch1 Hch2]].
  inversion Hch2. simplify_eq. inversion pc. simplify_eq.
  exists ks, z. split; split; auto.
  eapply chain_diff_suffix. apply Hch1. auto.
  by eapply rtc_transitive.
Qed.

Lemma chain_cons_right ks α δ τ : Chain α δ ks → p_le (TRec δ) τ → Chain α τ (ks ++ [δ]).
Proof.
  intros. eapply app_Chain. apply H.
  eapply cons_Chain. constructor. apply H0.
  constructor. constructor.
Qed.

Lemma elem_of_closed_rec_types n : forall (τ : type) (αb : type)
      (ls : list type) (Hls : length ls = n) (pch : Chain (TRec αb) τ ls), {[(TRec αb).[subst_chain ls]]} ⊆ closed_rec_types τ.
Proof.
  induction n.
  - intros. destruct ls; try by inversion Hls. clear Hls. rewrite subst_id. inversion_clear pch.
    induction τ.
    + assert (abs : TRec αb = TUnit). by apply le_TUnit. inversion abs.
    + destruct (le_TArrow _ _ _ p) as [abs | [p1 | p2]].
      * inversion abs.
      * set_solver.
      * set_solver.
    + clear IHτ.
      simpl. destruct (le_TRec (TRec αb) τ p) as [->]. set_solver.
    + assert (abs : TRec αb = TVar x). by apply le_TVar. inversion abs.
    + assert (abs : TRec αb = TUnknown). by apply le_TUnknown. inversion abs.
  - induction τ; intros.
    + destruct (chain_off_last ls _ _ n Hls pch) as [ks [δ [eq [pchn pμδτ]]]].
      assert (abs : TRec δ = TUnit). by apply le_TUnit. inversion abs.
    + clear IHn.
      destruct (chain_off_last ls _ _ n Hls pch) as [ks [δ [-> [pchn pμδτ]]]].
      destruct (le_TArrow _ _ _ pμδτ) as [abs | [p1 | p2]].
      * inversion abs.
      * specialize (IHτ1 αb (ks ++ [δ]) Hls (chain_cons_right _ _ _ _ pchn p1)). set_solver.
      * specialize (IHτ2 αb (ks ++ [δ]) Hls (chain_cons_right _ _ _ _ pchn p2)). set_solver.
    + clear IHτ.
      destruct (chain_off_last ls _ _ n Hls pch) as [ks [δ [-> [pchn pμδτ]]]].
      rewrite app_length in Hls. simpl in Hls.
      specialize (IHn δ αb ks ltac:(lia) pchn).
      destruct (le_TRec (TRec δ) τ pμδτ) as [->].
      rewrite subst_chain_app. simpl (subst_chain [δ]). simpl (closed_rec_types (TRec δ)).
      cut (subst (TRec δ .: ids) <$> {[(TRec αb).[subst_chain ks]]} ⊆ subst (TRec δ .: ids) <$> closed_rec_types δ ).
      { rewrite map_singleton. asimpl. set_solver. }
      by apply mono_map_subseteq.
    + destruct (chain_off_last ls _ _ n Hls pch) as [ks [δ [eq [pchn pμδτ]]]].
      assert (abs : TRec δ = TVar x). by apply le_TVar. inversion abs.
    + destruct (chain_off_last ls _ _ n Hls pch) as [ks [δ [eq [pchn pμδτ]]]].
      assert (abs : TRec δ = TUnknown). by apply le_TUnknown. inversion abs.
Qed.

Lemma elem_of_closed_rec_types' n : forall (τ : type) (αb : type)
      (ls : list type) (Hls : length ls = n) (pch : Chain (TRec αb) τ ls), (TRec αb).[subst_chain ls] ∈ closed_rec_types τ.
Proof. intros. apply elem_of_subseteq_singleton. by eapply elem_of_closed_rec_types. Qed.

Lemma crt_closed_gen τ : forall n, TnClosed n τ → set_Forall (TnClosed n) (closed_rec_types τ).
Proof.
  induction τ; intros; simpl.
  - apply set_Forall_empty.
  - apply set_Forall_union.
    + apply IHτ1. by eapply TArrow_nclosed1.
    + apply IHτ2. by eapply TArrow_nclosed2.
  - apply set_Forall_union.
    + by apply set_Forall_singleton.
    + specialize (IHτ (S n)). apply set_Forall_fmap_impl with (P := TnClosed (S n)).
      { intros τ' Hτ'. by apply TnClosed_subst. }
      apply IHτ. by apply TRec_nclosed1.
  - apply set_Forall_empty.
  - apply set_Forall_empty.
Qed.

Lemma crt_closed τ (pτ : TClosed τ) : set_Forall TClosed (closed_rec_types τ).
Proof. eapply set_Forall_impl. apply (crt_closed_gen _ 0). auto. auto. Qed.

Lemma nat_total_induction (P : nat → Prop) (base : P 0) (IH : forall n, (forall m, m ≤ n → P m) → P (S n)) : forall n, P n.
Proof.
  cut (forall n m, m ≤ n → P m).
  - intros. apply (H n n). lia.
  - intros n. induction n.
    + intros. inversion H. apply base.
    + intros. inversion H. apply IH. apply IHn. by apply IHn.
Qed.

Lemma closed_rec_types_unfold_subset_gen τ (pτ : TClosed τ) : ∀ (n : nat),
    forall (α : type) (k : nat) (pk : list type) (Hpk : length pk = k) (αk : type) (pchk : Chain α αk pk)
    (pn : list type) (Hpn : length pn = n) (pchn : Chain αk τ pn),
    fmap (subst (subst_chains_fmap pk pn)) (closed_rec_types α.[upn k (subst_chain pn)]) ⊆ closed_rec_types τ.
Proof.
  apply (nat_total_induction (fun n => forall (α : type) (k : nat) (pk : list type) (Hpk : length pk = k) (αk : type) (pchk : Chain α αk pk)
                                      (pn : list type) (Hpn : length pn = n) (pchn : Chain αk τ pn),
                                  fmap (subst (subst_chains_fmap pk pn)) (closed_rec_types α.[upn k (subst_chain pn)]) ⊆ closed_rec_types τ)).
  - intro α. induction α as [_ | β1 IHβ1 β2 IHβ2 | αb IHαb | x | _];
      intros k pk Hpk αk pchk nil p0 pchnil; try by set_solver.
    + specialize (IHβ1 k pk Hpk αk (chain_diff_prefix _ _ _ _ pchk (rtc_once _ _ (arrow_l_p_le_pre β1 β2))) nil p0 pchnil).
      specialize (IHβ2 k pk Hpk αk (chain_diff_prefix _ _ _ _ pchk (rtc_once _ _ (arrow_r_p_le_pre β1 β2))) nil p0 pchnil).
      set_solver.
    + specialize (IHαb (S k) (αb :: pk) ltac:(simpl; by rewrite Hpk) αk (cons_Chain _ _ (rtc_refl _ αb) _ (rtc_refl _ (TRec αb)) _ _ pchk) nil p0 pchnil).
      simpl. rewrite map_union. apply union_least.
      * destruct nil; simpl in p0; try by (exfalso; lia).
        rewrite subst_chains_fmap_nil. asimpl. rewrite up_id_n. asimpl.
        eapply elem_of_closed_rec_types. auto. eapply chain_diff_suffix. apply pchk. by inversion_clear pchnil.
      * rewrite -set_fmap_compose.
        erewrite set_Forall_fmap_ext_1. apply IHαb.
        rewrite -subst_through_rec.
        intro.
        rewrite scomp_comp. rewrite -Hpk. simpl. reflexivity.
    + destruct nil; simpl in p0; try by (exfalso; lia). simpl (subst_chain []). rewrite up_id_n. asimpl. set_solver.
  - intros n Hni α.
    induction α as [_ | β1 IHβ1 β2 IHβ2 | αb IHαb | x | _];
      intros k pk Hpk αk pchk pSn HpSn pchSn.
    + clear Hni. simpl. set_solver.
    + clear Hni. simpl.
      specialize (IHβ1 k pk Hpk αk (chain_diff_prefix _ _ _ _ pchk (rtc_once _ _ (arrow_l_p_le_pre β1 β2))) pSn HpSn pchSn).
      specialize (IHβ2 k pk Hpk αk (chain_diff_prefix _ _ _ _ pchk (rtc_once _ _ (arrow_r_p_le_pre β1 β2))) pSn HpSn pchSn).
      set_solver.
    + clear Hni.
      specialize (IHαb (S k) (αb :: pk) ltac:(simpl;auto) αk (cons_Chain αb αb (rtc_refl _ _) (TRec αb) (rtc_refl _ _) _ _ pchk) pSn HpSn pchSn).
      simpl. rewrite map_union. apply union_least.
      * clear IHαb. rewrite -subst_through_rec.
        rewrite map_singleton.
        assert (triv : (TRec αb).[upn k (subst_chain pSn)].[subst_chains_fmap pk pSn] = ((TRec αb).[upn k (subst_chain pSn) >> subst_chains_fmap pk pSn])). by asimpl. rewrite triv. clear triv.
        rewrite -Hpk.
        rewrite subst_chain_subst_chains_fmap.
        eapply elem_of_closed_rec_types. auto. eapply app_Chain. apply pchk. done.
      * rewrite -set_fmap_compose.
        erewrite set_Forall_fmap_ext_1.
        apply IHαb.
        rewrite -subst_through_rec.
        intro.
        rewrite scomp_comp. rewrite -Hpk. simpl. reflexivity.
    + destruct pSn as [_ | τ0' pn]; first by (simpl in HpSn; exfalso; lia).
      inversion HpSn as [Hpn]. inversion pchSn.
      clear H3 ls H2 τ0 τn H0 α H.
      destruct (subst_fv_upn_cases x k (subst_chain (τ0' :: pn))) as [[-> plt] | [j [eq ->]] ].
      * set_solver.
      * destruct (var_subst_chain j (τ0' ::pn)) as [[pj [τj [plk <-]]] | [_ ->]].
        ++ assert (Hch : Chain (TRec τj) τ (drop (S j) (τ0' :: pn))). eapply drop_Chain; auto. apply pchSn. simpl in Hch. simpl (drop (S j) _).
           specialize (Hni (n - j) ltac:(lia) (TRec τj) 0 [] ltac:(auto) (TRec τj) (nil_Chain _ _ (rtc_refl _ _)) (drop j pn) ltac:(by rewrite drop_length Hpn) Hch).
           rewrite upn0 in Hni. simpl (subst_chains_fmap [] (drop j pn)) in Hni. rewrite subst_idX in Hni.
           assert (Hni' : closed_rec_types (TRec τj).[subst_chain (drop j pn)] ⊆ closed_rec_types τ). set_solver. clear Hni. rename Hni' into Hni.
           assert (Hc : TClosed (TRec τj).[subst_chain (drop j pn)]).
           { apply (crt_closed τ pτ). eapply elem_of_closed_rec_types'; auto. }
           rewrite Hc.
           assert (Hcc : set_Forall TClosed (closed_rec_types (TRec τj).[subst_chain (drop j pn)])).
           { eapply set_Forall_subseteq. apply Hni. apply (crt_closed τ pτ). }
           rewrite (set_Forall_fmap_ext_1 _ id). set_solver.
           eapply set_Forall_impl. apply Hcc. intros. by rewrite H.
        ++ (* impossible cast but yeah.. *) simpl. set_solver.
    + simpl. set_solver.
Qed.

Lemma closed_rec_types_unfold_subset τb (pμτb : TClosed (TRec τb)) : closed_rec_types τb.[TRec τb/] ⊆ closed_rec_types (TRec τb).
Proof.
  cut (fmap (subst (subst_chains_fmap [] [τb])) (closed_rec_types τb.[upn 0 (subst_chain [τb])])  ⊆ closed_rec_types (TRec τb)).
  { intro. asimpl. asimpl in H. set_solver. }
  apply closed_rec_types_unfold_subset_gen with (αk := τb) (n := 1); auto.
  constructor; constructor. econstructor; constructor. constructor.
Qed.
