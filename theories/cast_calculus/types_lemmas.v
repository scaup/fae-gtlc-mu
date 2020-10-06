From fae_gtlc_mu.cast_calculus Require Import types.
From fae_gtlc_mu Require Export prelude.

Instance type_eqdec : EqDecision type.
Proof. solve_decision. Qed.

Instance Is_Unknown_dec (τ : type) : Decision (τ = TUnknown) := type_eqdec τ TUnknown.

Lemma scomp_comp (σ1 σ2 : var → type) τ : (subst σ1 ∘ subst σ2) τ = subst (σ2 >> σ1) τ.
Proof. by asimpl. Qed.

Lemma scomp_assoc (σ1 σ2 σ3 : var → type) : (σ1 >> σ2) >> σ3 = σ1 >> (σ2 >> σ3).
Proof. by asimpl. Qed.

Lemma subst_commut (τ : type) (σ : var → type) : up σ >> scons (τ.[σ]) ids = scons τ ids >> σ.
Proof. by asimpl. Qed.

Lemma subst_fv_upn_yes n m σ : (TVar (n + m)).[upn n σ] = ((TVar m).[σ].[ren (+n)]).
Proof.
  asimpl.
  induction n.
  - by asimpl.
  - asimpl. rewrite IHn. by asimpl.
Qed.

Lemma subst_fv_upn_no n m σ : n < m → (TVar n).[upn m σ] = TVar n.
Proof.
  generalize dependent n.
  induction m.
  - intros. exfalso. lia.
  - intros. destruct n.
    + by asimpl.
    + asimpl. asimpl in IHm. rewrite IHm. by asimpl. lia.
Qed.

Lemma subst_fv_upn_cases (k n : nat) σ : ((TVar k).[upn n σ] = TVar k ∧ k < n) +
                                 { j : nat | (k = (n + j)) ∧ (TVar k).[upn n σ] = (TVar j).[σ].[ren (+n)]  }.
Proof.
  destruct (decide (k < n)).
  - apply inl. split. apply subst_fv_upn_no; auto. auto.
  - apply inr. exists (k - n). split. lia. rewrite -subst_fv_upn_yes.
    assert (triv : k = n + (k - n)). lia. by rewrite -triv.
Qed.

(* properties about closedness {{{ *)

Lemma TUnit_Closed : Closed TUnit.
Proof. try by (intro σ; by asimpl). Qed.

Lemma TArrow_closed {τ1 τ2} : Closed τ1 → Closed τ2 → Closed (TArrow τ1 τ2).
Proof.
  unfold Closed.
  intros H1 H2 τ'.
  simpl. by rewrite H1 H2.
Qed.

Lemma TArrow_closed1 {τ1 τ2} : Closed (TArrow τ1 τ2) → Closed τ1.
Proof.
  unfold Closed.
  intros H σ.
  assert (H' : TArrow τ1.[σ] τ2.[σ] = TArrow τ1 τ2). asimpl in H; by rewrite H.
  inversion H'.
  by do 2 rewrite H1.
Qed.

Lemma TArrow_closed2 {τ1 τ2} : Closed (TArrow τ1 τ2) → Closed τ2.
Proof.
  unfold Closed.
  intros H σ.
  assert (H' : TArrow τ1.[σ] τ2.[σ] = TArrow τ1 τ2). asimpl in H; by rewrite H.
  inversion H'.
  by do 2 rewrite H2.
Qed.

Lemma TProd_closed {τ1 τ2} : Closed τ1 → Closed τ2 → Closed (TProd τ1 τ2).
Proof.
  unfold Closed.
  intros H1 H2 τ'.
  simpl. by rewrite H1 H2.
Qed.

Lemma TProd_closed1 {τ1 τ2} : Closed (TProd τ1 τ2) → Closed τ1.
Proof.
  unfold Closed.
  intros H σ.
  assert (H' : TProd τ1.[σ] τ2.[σ] = TProd τ1 τ2). asimpl in H; by rewrite H.
  inversion H'.
  by do 2 rewrite H1.
Qed.

Lemma TProd_closed2 {τ1 τ2} : Closed (TProd τ1 τ2) → Closed τ2.
Proof.
  unfold Closed.
  intros H σ.
  assert (H' : TProd τ1.[σ] τ2.[σ] = TProd τ1 τ2). asimpl in H; by rewrite H.
  inversion H'.
  by do 2 rewrite H2.
Qed.

Lemma TSum_closed {τ1 τ2} : Closed τ1 → Closed τ2 → Closed (TSum τ1 τ2).
Proof.
  unfold Closed.
  intros H1 H2 τ'.
  simpl. by rewrite H1 H2.
Qed.

Lemma TSum_closed1 {τ1 τ2} : Closed (TSum τ1 τ2) → Closed τ1.
Proof.
  unfold Closed.
  intros H σ.
  assert (H' : TSum τ1.[σ] τ2.[σ] = TSum τ1 τ2). asimpl in H; by rewrite H.
  inversion H'.
  by do 2 rewrite H1.
Qed.

Lemma TSum_closed2 {τ1 τ2} : Closed (TSum τ1 τ2) → Closed τ2.
Proof.
  unfold Closed.
  intros H σ.
  assert (H' : TSum τ1.[σ] τ2.[σ] = TSum τ1 τ2). asimpl in H; by rewrite H.
  inversion H'.
  by do 2 rewrite H2.
Qed.

Lemma TRec_closed {τ} : Closed τ → Closed (TRec τ).
Proof. intros H σ. asimpl. by rewrite H. Qed.

Lemma TRec_TArrow_closed {τ1 τ2} : Closed (TRec τ1) → Closed (TRec τ2) → Closed (TRec (TArrow τ1 τ2)).
Proof.
  intros H1 H2.
  intro. simpl.
  assert (H1' : (TRec τ1).[σ] = TRec τ1). by rewrite H1. asimpl in H1'. inversion H1' as [H1'']. do 2 rewrite H1''.
  assert (H2' : (TRec τ2).[σ] = TRec τ2). by rewrite H2. asimpl in H2'. inversion H2' as [H2'']. do 2 rewrite H2''.
  done.
Qed.

Lemma no_var_is_closed x : not (Closed (TVar x)).
Proof.
  intro H. assert (abs : (TVar x).[ren (+1)] = TVar x); first by apply H.
  inversion abs; lia.
Qed.

Lemma TArrow_nclosed1 {τ1 τ2} {n} : NClosed n (TArrow τ1 τ2) → NClosed n τ1.
Proof.
  unfold NClosed.
  intros H σ.
  assert (H' : TArrow τ1.[upn n σ] τ2.[upn n σ] = TArrow τ1 τ2). asimpl in H. by rewrite H.
  inversion H'.
  by do 2 rewrite H1.
Qed.

Lemma TArrow_nclosed2 {τ1 τ2} {n} : NClosed n (TArrow τ1 τ2) → NClosed n τ2.
Proof.
  unfold NClosed.
  intros H σ.
  assert (H' : TArrow τ1.[upn n σ] τ2.[upn n σ] = TArrow τ1 τ2). asimpl in H; by rewrite H.
  inversion H'.
  by do 2 rewrite H2.
Qed.

Lemma TArrow_nclosed {τ1 τ2} {n} : (NClosed n τ1 ∧ NClosed n τ2) ↔ NClosed n (TArrow τ1 τ2).
Proof.
  split. intros (H1, H2). intro σ. asimpl. by rewrite H1 H2.
  intros. split. by eapply TArrow_nclosed1. by eapply TArrow_nclosed2.
Qed.

Lemma TProd_nclosed1 {τ1 τ2} {n} : NClosed n (TProd τ1 τ2) → NClosed n τ1.
Proof.
  unfold NClosed.
  intros H σ.
  assert (H' : TProd τ1.[upn n σ] τ2.[upn n σ] = TProd τ1 τ2). asimpl in H. by rewrite H.
  inversion H'.
  by do 2 rewrite H1.
Qed.

Lemma TProd_nclosed2 {τ1 τ2} {n} : NClosed n (TProd τ1 τ2) → NClosed n τ2.
Proof.
  unfold NClosed.
  intros H σ.
  assert (H' : TProd τ1.[upn n σ] τ2.[upn n σ] = TProd τ1 τ2). asimpl in H; by rewrite H.
  inversion H'.
  by do 2 rewrite H2.
Qed.

Lemma TSum_nclosed1 {τ1 τ2} {n} : NClosed n (TSum τ1 τ2) → NClosed n τ1.
Proof.
  unfold NClosed.
  intros H σ.
  assert (H' : TSum τ1.[upn n σ] τ2.[upn n σ] = TSum τ1 τ2). asimpl in H. by rewrite H.
  inversion H'.
  by do 2 rewrite H1.
Qed.

Lemma TSum_nclosed2 {τ1 τ2} {n} : NClosed n (TSum τ1 τ2) → NClosed n τ2.
Proof.
  unfold NClosed.
  intros H σ.
  assert (H' : TSum τ1.[upn n σ] τ2.[upn n σ] = TSum τ1 τ2). asimpl in H; by rewrite H.
  inversion H'.
  by do 2 rewrite H2.
Qed.

Lemma TRec_nclosed1 {τ} {n} : NClosed n (TRec τ) → NClosed (S n) τ.
Proof.
  intros H σ.
  assert (H' : TRec τ.[upn (S n) σ] = TRec τ). specialize (H σ). by asimpl in H.
  inversion H'.
  by do 2 rewrite H1.
Qed.

Lemma TRec_nclosed {τ} {n} : NClosed n (TRec τ) ↔ NClosed (S n) τ.
Proof.
  split. apply TRec_nclosed1.
  intros H σ.
  asimpl. apply f_equal. apply H.
Qed.

Lemma NClosed_var (x n : nat) : NClosed n (TVar x) ↔ x < n.
Proof.
  split.
  - intros.
    destruct (subst_fv_upn_cases x n (ren (+1))) as [[_ eq] | [j [-> _]]].
    + auto.
    + exfalso. unfold NClosed in H.
      specialize (H (ren (+1))).
      rewrite subst_fv_upn_yes in H.
      asimpl in H. inversion H. lia.
  - intros. intro σ. by apply subst_fv_upn_no.
Qed.

Lemma le_exists_add x y : x ≤ y → exists z, x + z = y.
Proof. intros. exists (y - x). lia. Qed.

Lemma NClosed_mon τ (n m : nat) : n ≤ m → NClosed n τ → NClosed m τ.
Proof.
  intros ple pnτ. intro σ. destruct (le_exists_add n m ple) as [z <-]. generalize σ. clear σ.
  simpl. induction z. asimpl. intro σ. by rewrite pnτ. intro σ. cut (τ.[upn (n + S z) σ] = τ.[upn (n + z) (up σ)]).
  intro. rewrite H. apply IHz. lia. by asimpl.
Qed.

Lemma NClosed_ren_gen (τ : type) :
  forall (n m : nat) (pτ : NClosed n τ) (l : nat), NClosed (m + n) τ.[upn l (ren (+m))].
Proof.
  induction τ; intros.
  - by asimpl.
  - specialize (IHτ1 n m ltac:(by eapply TProd_nclosed1) l).
    specialize (IHτ2 n m ltac:(by eapply TProd_nclosed2) l).
    simpl. intro σ. simpl. by rewrite IHτ1 IHτ2.
  - specialize (IHτ1 n m ltac:(by eapply TSum_nclosed1) l).
    specialize (IHτ2 n m ltac:(by eapply TSum_nclosed2) l).
    simpl. intro σ. simpl. by rewrite IHτ1 IHτ2.
  - specialize (IHτ1 n m ltac:(by eapply TArrow_nclosed1) l).
    specialize (IHτ2 n m ltac:(by eapply TArrow_nclosed2) l).
    simpl. intro σ. simpl. by rewrite IHτ1 IHτ2.
  - simpl. apply TRec_nclosed.
    specialize (IHτ (S n) m ltac:(by apply TRec_nclosed) (S l)).
    by asimpl in *.
  - destruct (subst_fv_upn_cases x l (ren (+m))) as [[-> p] | [j [eq ->]]].
    + eapply (NClosed_mon _ n). lia. apply pτ.
    + asimpl. apply NClosed_var.
      assert (H : x < n). by apply NClosed_var. lia.
  - by asimpl.
Qed.

Lemma NClosed_ren (τ : type) :
  forall (n m : nat) (pτ : NClosed n τ), NClosed (m + n) τ.[ren (+m)].
Proof. intros. cut (NClosed (m + n) τ.[upn 0 (ren (+m))]). by asimpl. by apply NClosed_ren_gen. Qed.

Lemma NClosed_subst_gen n τ τ' : forall m, NClosed (S (m + n)) τ' → NClosed n τ → NClosed ((m + n)) τ'.[upn m (τ .: ids)].
Proof.
  generalize dependent n.
  induction τ'; intros.
  - asimpl. intro σ; by asimpl.
  - asimpl.
    specialize (IHτ'1 n m ltac:(by eapply TProd_nclosed1) H0).
    specialize (IHτ'2 n m ltac:(by eapply TProd_nclosed2) H0).
    intro σ. simpl. by rewrite IHτ'1 IHτ'2.
  - asimpl.
    specialize (IHτ'1 n m ltac:(by eapply TSum_nclosed1) H0).
    specialize (IHτ'2 n m ltac:(by eapply TSum_nclosed2) H0).
    intro σ. simpl. by rewrite IHτ'1 IHτ'2.
  - asimpl.
    specialize (IHτ'1 n m ltac:(by eapply TArrow_nclosed1) H0).
    specialize (IHτ'2 n m ltac:(by eapply TArrow_nclosed2) H0).
    intro σ. simpl. by rewrite IHτ'1 IHτ'2.
  - simpl.
    apply TRec_nclosed.
    apply (IHτ' n (S m)). by apply TRec_nclosed. auto.
  - destruct (subst_fv_upn_cases x m (τ .: ids)) as [[-> p] | [j [eq ->]]].
    + apply NClosed_var. lia.
    + destruct j.
      * asimpl. by apply NClosed_ren.
      * asimpl. assert (p1 : x < S (m + n)). by apply NClosed_var.
        apply NClosed_var. lia.
  - by asimpl.
Qed.

Lemma NClosed_subst n τ τ' : NClosed (S n) τ' → NClosed n τ → NClosed n τ'.[τ/].
Proof. intros. rewrite -(upn0 (τ .: ids)). apply (NClosed_subst_gen n τ τ' 0); auto. Qed.

Lemma TRec_closed_unfold {τ} : Closed (TRec τ) → Closed (τ.[TRec τ/]).
Proof. intro. cut (NClosed 0 τ.[TRec τ/]). by simpl. apply NClosed_subst.
       apply TRec_nclosed. by simpl. by simpl.
Qed.


Lemma TRec_NClosed τ n : NClosed n (TRec τ) → NClosed (S n) τ.
Proof. intros p σ. specialize (p σ). asimpl in p. inversion p. by do 2 rewrite H0. Qed.

Lemma closed_Fold_typed_help_gen τ : forall n τ', NClosed n τ.[upn n (τ' .: ids)] → NClosed (S n) τ.
Proof.
  induction τ; intros n τ'.
  - by asimpl.
  - asimpl. intro p.
    specialize (IHτ1 n τ' (TProd_nclosed1 p)).
    specialize (IHτ2 n τ' (TProd_nclosed2 p)).
    intro σ. simpl. by rewrite IHτ1 IHτ2.
  - asimpl. intro p.
    specialize (IHτ1 n τ' (TSum_nclosed1 p)).
    specialize (IHτ2 n τ' (TSum_nclosed2 p)).
    intro σ. simpl. by rewrite IHτ1 IHτ2.
  - asimpl. intro p. apply (iffLR TArrow_nclosed); split.
    apply (IHτ1 n τ' (TArrow_nclosed1 p)).
    apply (IHτ2 n τ' (TArrow_nclosed2 p)).
  - asimpl. intro p.
    assert (q : NClosed (S n) τ.[upn (S n) (τ' .: ids)]).
    by apply TRec_NClosed. specialize (IHτ (S n) τ' q).
    by apply TRec_nclosed.
  - intros. asimpl in H.
    destruct (iter_up_cases x n (τ' .: ids)) as [[eq plt] | [j [eq eq2]]].
    + apply NClosed_var. lia.
    + rewrite eq2 in H. rewrite eq. clear eq eq2 x.
      destruct j.
      * apply NClosed_var. lia.
      * exfalso. asimpl in H.
        assert (abs : n + j < n). by apply NClosed_var. lia.
  - by asimpl.
Qed.

Lemma closed_Fold_typed_help τ : Closed τ.[TRec τ/] → Closed (TRec τ).
Proof.
  intro.
  cut (NClosed 1 τ). intro. cut (NClosed 0 (TRec τ)). by simpl. by apply (iffRL TRec_nclosed).
  by eapply closed_Fold_typed_help_gen.
Qed.

Ltac closed_solver :=
  ( by eapply TUnit_Closed
  || by eapply TArrow_closed
  || by eapply TArrow_closed1
  || by eapply TArrow_closed2
  || by eapply TProd_closed
  || by eapply TProd_closed1
  || by eapply TProd_closed2
  || by eapply TSum_closed
  || by eapply TSum_closed1
  || by eapply TSum_closed2
  ).

(* }}} *)

(* ground types, inert casts... {{{ *)

Definition Ground_dec (τ : type) : sum (Ground τ) (Ground τ → False).
  destruct τ.
  - apply inl; constructor.
  - destruct (Is_Unknown_dec τ1). rewrite e.
    destruct (Is_Unknown_dec τ2). rewrite e0.
    + apply inl. constructor.
    + apply inr. intro aaa. inversion aaa. apply n. by symmetry.
    + apply inr. intro aaa. inversion aaa. apply n. by symmetry.
  - destruct (Is_Unknown_dec τ1). rewrite e.
    destruct (Is_Unknown_dec τ2). rewrite e0.
    + apply inl. constructor.
    + apply inr. intro aaa. inversion aaa. apply n. by symmetry.
    + apply inr. intro aaa. inversion aaa. apply n. by symmetry.
  - destruct (Is_Unknown_dec τ1). rewrite e.
    destruct (Is_Unknown_dec τ2). rewrite e0.
    + apply inl. constructor.
    + apply inr. intro aaa. inversion aaa. apply n. by symmetry.
    + apply inr. intro aaa. inversion aaa. apply n. by symmetry.
  - destruct (Is_Unknown_dec τ). rewrite e.
    + apply inl. constructor.
    + apply inr. intro aaa. inversion aaa. apply n. by symmetry.
  - apply inr. intro aaa. inversion aaa.
  - apply inr. intro aaa. inversion aaa.
Defined.

(* Checking if two GROUND TYPES are equal *)
Definition Ground_equal {τ1 τ2 : type} (G1 : Ground τ1) (G2 : Ground τ2) : Prop := τ1 = τ2.

(* Distinction between inert and active as in formalisation of Jeremy *)

Require Logic.JMeq.
Lemma Unique_Ground_Proof τ (G1 : Ground τ) (G2 : Ground τ) : G1 = G2.
Proof.
  destruct G1; generalize_eqs G2; intros; destruct G2; try inversion H; try by rewrite H0.
Qed.

Lemma Unique_ICP_proof τi τf (Ip1 : ICP τi τf) (Ip2 : ICP τi τf) : Ip1 = Ip2.
Proof.
  destruct Ip1.
  - generalize_eqs Ip2.
    intros.
    destruct Ip2.
    simplify_eq.
      by rewrite H1.
      inversion H0.
  - generalize_eqs Ip2.
    intros.
    destruct Ip2.
    simplify_eq.
    rewrite (Unique_Ground_Proof τ G G0).
      by rewrite -H0.
Qed.







Lemma Ground_closed {τG} (G : Ground τG) : Closed τG.
Proof. destruct G; intro σ; by asimpl. Qed.



Lemma Closed_easy : forall τ n, τ.[upn n (TUnit .: ids)] = τ → NClosed n τ.
Proof.
  intro τ.
  induction τ; intros n eq.
  - intro σ; by asimpl.
  - asimpl in eq. inversion eq.
    specialize (IHτ1 n H0). specialize (IHτ2 n H1).
    rewrite IHτ1 IHτ2. intro σ. asimpl. by rewrite IHτ1 IHτ2.
  - asimpl in eq. inversion eq.
    specialize (IHτ1 n H0). specialize (IHτ2 n H1).
    rewrite IHτ1 IHτ2. intro σ. asimpl. by rewrite IHτ1 IHτ2.
  - asimpl in eq. inversion eq.
    specialize (IHτ1 n H0). specialize (IHτ2 n H1).
    rewrite IHτ1 IHτ2. intro σ. asimpl. by rewrite IHτ1 IHτ2.
  - apply TRec_nclosed. apply IHτ. asimpl in eq. inversion eq. by do 2 rewrite H0.
  - asimpl in eq. destruct (iter_up_cases x n (TUnit .: ids)) as [[a p]| [j [b eq']]].
    by apply NClosed_var. exfalso. rewrite eq in eq'. destruct j; asimpl in eq'. inversion eq'.
    inversion eq'. lia.
  - intro σ; by asimpl.
Qed.

Instance Closed_dec τ : Decision (Closed τ).
Proof.
  destruct (decide (τ.[TUnit/] = τ)).
  apply left. cut (NClosed 0 τ). by simpl. apply Closed_easy. by asimpl.
  apply right. intro abs. assert (H : τ.[TUnit/] = τ). by rewrite abs. contradiction.
Qed.

Definition ICP_dec (τi τf : type) : Decision (ICP τi τf).
Proof. destruct τf.
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
    + apply right. intro aaa. inversion aaa. by apply f.
Defined.

