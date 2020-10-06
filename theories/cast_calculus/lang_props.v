From fae_gtlc_mu.cast_calculus Require Export lang.

Lemma fill_CastError K : ∀ e, fill K e = CastError → e = CastError.
Proof.
  induction K as [|Ki K IHK]. by simpl.
  simpl. intros. assert (H' : fill_item Ki e = CastError). by apply IHK.
  destruct Ki; by inversion H'.
Qed.

Lemma CastError_stuck : stuck CastError tt.
Proof.
  split. by simpl.
  intros l e σ efs Hstep. inversion Hstep; simplify_eq.
  + assert (eq : e1' = CastError). by eapply fill_CastError.
    rewrite eq in H1. inversion H1.
  + exfalso. destruct K. contradiction.
    simpl in H0.
    assert (eq : fill_item e CastError = CastError). by eapply fill_CastError.
    destruct e; simpl in eq; inversion eq.
Qed.

Lemma fill_app K K' e : fill K' (fill K e) = fill (K ++ K') e.
Proof.
  generalize dependent e.
  induction K.
  by simpl. intro e. simpl. by rewrite IHK.
Qed.

Lemma fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e).
Proof.
  revert e. induction K as [|Ki K IHK]; first by simpl.
  intros e pev. apply fill_item_val with (Ki := Ki).
  apply IHK. by simpl.
Qed.

Lemma step_by_val K K' e1 e1' e2 :
  fill K e1 = fill K' e1' →
  to_val e1 = None →
  head_step e1' e2 →
  ∃ K'', K' = K'' ++ K.
Proof.
  intros Hfill Hred Hstep.
  revert K' Hfill.
  induction K as [|Ki K IH] using rev_ind=> /= K' Hfill; eauto using app_nil_r.
  destruct K' as [|Ki' K' _] using @rev_ind; simplify_eq/=.
  { rewrite -fill_app in Hstep. apply head_ctx_step_val in Hstep.
    apply fill_val in Hstep. by apply not_eq_None_Some in Hstep. }
  do 2 rewrite -fill_app /= in Hfill.
  assert (Ki = Ki') as ->.
  { eapply fill_item_no_val_inj, Hfill.
    by apply fill_not_val. apply fill_not_val; eauto using val_head_stuck. }
  simplify_eq. destruct (IH K') as [K'' ->]; auto.
  exists K''. by rewrite assoc.
Qed.

Lemma cast_error_step K : K ≠ [] → pure_step (fill K CastError) CastError.
Proof.
  intro neq. split.
  - intros σ. exists CastError, tt, [].
    by apply CastError_step.
  - intros. destruct σ1, σ2. inversion H; simplify_eq.
    + exfalso. destruct (step_by_val K K0 CastError e1' e2'0 H0 ltac:(by simpl) H2) as [K'' ->].
      rewrite -fill_app in H0.
      assert (CastError = fill K'' e1'). by apply (inj (fill K) _ _).
      assert (e1' = CastError). eapply fill_CastError. by symmetry. rewrite H3 in H2.
      inversion H2.
    + done.
Qed.

Lemma fill_step_inv (K : ectx) e1' κ e2 efs : e2 ≠ CastError →
  to_val e1' = None → prim_step (fill K e1') κ e2 efs →
  ∃ e2', e2 = fill K e2' ∧ prim_step e1' κ e2' efs.
Proof.
  intros neq Hnval Hprimstep.
  inversion Hprimstep.
  - simplify_eq.
    destruct (step_by_val K K0 e1' e1'0 e2') as [K' ->]; eauto.
    rewrite -fill_app in H. apply (inj (fill _)) in H.
    exists (fill K' e2'). rewrite -fill_app; split; auto.
    eapply Ectx_step; eauto.
  - simplify_eq.
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

Lemma split_list {A : Type} (a : A) (ls : list A) : exists ls' a', (a :: ls) = ls' ++ [a'].
Proof. eapply chop_off_last. done. Qed.

Lemma fill_CastError_empty K e : CastError = fill K e → K = [].
Proof.
  generalize dependent e.
  induction K as [|Ki K IHK]; first by simpl.
  intros. simpl in H. assert (K = []). by eapply IHK. rewrite H0 in H. simpl in H. exfalso.
  destruct Ki; inversion H.
Qed.

Lemma fill_item_step_CastError_inv Ki e (eNeqCE : e ≠ CastError) (Hnv : to_val e = None) (Hstep : prim_step (fill_item Ki e) [] CastError []) :
  prim_step e [] CastError [].
Proof.
  inversion Hstep.
  - simplify_eq.
    assert (eq : e2' = CastError). by rewrite (fill_CastError K e2').
    destruct (step_by_val [Ki] K e e1' CastError) as [K' ->]; eauto. by rewrite -eq.
    assert (abs : K' ++ [Ki] = []). eapply fill_CastError_empty. by rewrite eq in H0.
    assert (abs' : length (K' ++ [Ki]) = 0). by rewrite abs. rewrite app_length in abs'. simpl in abs'.
    exfalso. lia.
  - destruct K.
    { exfalso. destruct Ki; simpl in H0; inversion H0. }
    destruct (split_list e0 K) as [K' [Ki' eq]]. rewrite eq in H0.
    rewrite -fill_app in H0.
    simpl in H0.
    destruct Ki, Ki';
      (try by inversion H0); inversion H0; (try simpl in H0);
        try by (destruct K'; simplify_eq; simpl in Hstep; by apply CastError_step).
    + exfalso. rewrite -H1 in Hnv. rewrite to_of_val in Hnv. inversion Hnv.
    + assert (abs : to_val (fill K' CastError) = Some v1). rewrite H1. by rewrite to_of_val. assert (true : to_val (fill K' CastError) = None). by rewrite fill_not_val.
      rewrite true in abs. inversion abs.
    + exfalso. rewrite -H1 in Hnv. rewrite to_of_val in Hnv. inversion Hnv.
    + assert (abs : to_val (fill K' CastError) = Some v1). rewrite H1. by rewrite to_of_val. assert (true : to_val (fill K' CastError) = None). by rewrite fill_not_val.
      rewrite true in abs. inversion abs.
Qed.

Lemma fill_step_CastError_inv K e (eNeqCE : e ≠ CastError) (Hnv : to_val e = None) (Hstep : prim_step (fill K e) [] CastError []) : prim_step e [] CastError [].
Proof.
  generalize dependent e.
  induction K as [| Ki K IHK].
  - intros. by simpl in Hstep.
  - intros. simpl in Hstep.
    assert (H : fill_item Ki e ≠ CastError). intro abs. destruct Ki; inversion abs.
    specialize (IHK (fill_item Ki e) H (fill_item_not_val Ki _ Hnv) Hstep).
    by eapply fill_item_step_CastError_inv.
Qed.

Lemma head_step_det e e1 e2 : head_step e e1 → head_step e e2 → e1 = e2.
Proof. intros H1 H2. inversion H1; inversion H2; ((by simplify_eq) || (try done) || simplify_eq; inversion G2). Qed.

Lemma prim_step_det e e1 e2 ws xs ys zs : prim_step e ws e1 xs → prim_step e ys e2 zs → e1 = e2.
Proof.
  intros H1 H2.
  inversion H1 as [K d e' d1 e1' eq1 eq2 Hstep1|L neq].
  - inversion H2 as [L f e'' f1 e2' eq3 eq4 Hstep2| L neq]; simplify_eq.
    + assert (K = L) as ->.
      { destruct (step_by_val K L e' e'' e2' eq3) as [M eq]; auto. by eapply val_head_stuck.
        destruct (step_by_val L K e'' e' e1') as [N eq']; auto. by eapply val_head_stuck.
        rewrite eq in eq'. assert (length K = length (N ++ M ++ K)). by rewrite -eq'.
        do 2 rewrite app_length in H. assert (M = []) as ->. apply length_zero_iff_nil. lia.
        by simpl in eq. }
      f_equal.
      rewrite (inj (fill L) e' e'' eq3) in Hstep1.
      apply (head_step_det _ _ _ Hstep1 Hstep2).
    + exfalso. destruct (step_by_val L K CastError e' e1' H5) as [L' ->]; auto.
      rewrite -fill_app in H5. assert (CastError = fill L' e'). by apply (inj (fill L)).
      rewrite (fill_CastError L' e' (eq_sym H)) in Hstep1.
      inversion Hstep1.
  - inversion H2 as [K f e'' f1 e2' eq3 eq4 Hstep2| K neq']; simplify_eq.
    + exfalso. destruct (step_by_val L K CastError e'' e2') as [L' ->]; auto.
      rewrite -fill_app in eq3. assert (CastError = fill L' e''). by apply (inj (fill L)).
      rewrite (fill_CastError L' e'' (eq_sym H)) in Hstep2.
      inversion Hstep2.
    + done.
Qed.

Lemma prim_step_pure e e' : prim_step e [] e' [] → pure_step e e'.
Proof.
  intro Hp. split.
  + intro σ. destruct σ. exists e', tt, []. by simpl.
  + intros. destruct σ1, σ2. simpl in H.
    assert (efs = []) as ->; first by inversion H. assert (κ = []) as ->; first by inversion H.
    erewrite (prim_step_det e e' e2'); eauto.
Qed.

Instance expr_eqdec : EqDecision expr.
Proof. solve_decision. Qed.

