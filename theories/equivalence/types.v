From stdpp Require Import base list.
From Autosubst Require Export Autosubst.
From iris Require Export base.
Require Export Utf8_core.

(* omitting repetitive cases... *)

Inductive type :=
  | TUnit : type
  | TArrow (τ1 τ2 : type) : type
  | TRec (τ : {bind 1 of type})
  | TVar (x : var)
  | TUnknown.

Instance Ids_type : Ids type. derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.
Instance SubstLemmas_typer : SubstLemmas type. derive. Qed.

Inductive Ground : type → Type :=
  | GUnit : Ground TUnit
  | GArrow : Ground (TArrow TUnknown TUnknown)
  | GRec : Ground (TRec TUnknown).

Definition TClosed (τ : type) : Prop := forall σ, τ.[σ] = τ.

Instance type_eqdec : EqDecision type.
Proof.
  unfold EqDecision.
  intro τ.
  induction τ; intros τ'; destruct τ'; try (by (apply right; intro abs; inversion abs)).
  - by apply left.
  - destruct (IHτ1 τ'1) as [-> | neq].
    + destruct (IHτ2 τ'2) as [-> | neq].
      * by apply left.
      * apply right. intro abs. inversion abs. contradiction.
    + apply right. intro abs. inversion abs. contradiction.
  - destruct (IHτ τ0) as [-> | neq].
    + by apply left.
    + apply right. intro abs. inversion abs. contradiction.
  - destruct (decide (x = x0)) as [-> | neq].
    + by apply left.
    + apply right. intro abs. inversion abs. contradiction.
  - by apply left.
Qed.

Instance Unknown_dec (τ : type) : Decision (τ = TUnknown).
Proof. destruct τ; try (by (apply right; auto)) || (apply left; auto). Qed.

Inductive Cat : type → Type :=
  | CUnknown : Cat TUnknown
  | CGroundUnit : Ground TUnit → Cat TUnit
  | CGroundArrow : Ground (TArrow TUnknown TUnknown) → Cat (TArrow TUnknown TUnknown)
  | CGroundRec : Ground (TRec TUnknown) → Cat (TRec TUnknown)
  | CArrow τ1 τ2 : (τ1 ≠ TUnknown ∨ τ2 ≠ TUnknown) → Cat (TArrow τ1 τ2)
  | CRec τ : (τ ≠ TUnknown) → Cat (TRec τ)
  | CVar i : Cat (TVar i).

Lemma categorize (τ : type) : Cat τ.
Proof.
  destruct τ; try by do 2 constructor.
  - destruct (Unknown_dec τ1); simplify_eq.
    destruct (Unknown_dec τ2); simplify_eq.
    constructor. constructor. constructor; auto. constructor; auto.
  - destruct (Unknown_dec τ); simplify_eq.
    destruct (Unknown_dec TUnknown); simplify_eq.
    constructor. constructor. constructor; auto.
Qed.

(* boring properties about closedness {{{ *)

Lemma subst_through_arrow {τ1 τ2} σ : (TArrow τ1 τ2).[σ] = TArrow τ1.[σ] τ2.[σ].
Proof. by asimpl. Qed.

Lemma subst_through_rec {τb} σ : (TRec τb).[σ] = TRec τb.[up σ].
Proof. by asimpl. Qed.

Lemma TArrow_closed1 {τ1 τ2} : TClosed (TArrow τ1 τ2) → TClosed τ1.
Proof.
  unfold TClosed.
  intros H σ.
  assert (H' : TArrow τ1.[σ] τ2.[σ] = TArrow τ1 τ2). asimpl in H; by rewrite H.
  inversion H'.
  by do 2 rewrite H1.
Qed.

Lemma TArrow_closed2 {τ1 τ2} : TClosed (TArrow τ1 τ2) → TClosed τ2.
Proof.
  unfold TClosed.
  intros H σ.
  assert (H' : TArrow τ1.[σ] τ2.[σ] = TArrow τ1 τ2). asimpl in H; by rewrite H.
  inversion H'.
  by do 2 rewrite H2.
Qed.

Lemma TArrow_closed {τ1 τ2} : TClosed τ1 → TClosed τ2 → TClosed (TArrow τ1 τ2).
Proof.
  unfold TClosed.
  intros H1 H2 τ'.
  simpl. by rewrite H1 H2.
Qed.

Lemma TRec_TArrow_closed {τ1 τ2} : TClosed (TRec τ1) → TClosed (TRec τ2) → TClosed (TRec (TArrow τ1 τ2)).
Proof.
  intros H1 H2.
  intro. simpl.
  assert (H1' : (TRec τ1).[σ] = TRec τ1). by rewrite H1. asimpl in H1'. inversion H1' as [H1'']. do 2 rewrite H1''.
  assert (H2' : (TRec τ2).[σ] = TRec τ2). by rewrite H2. asimpl in H2'. inversion H2' as [H2'']. do 2 rewrite H2''.
  done.
Qed.

Lemma no_var_is_closed x : not (TClosed (TVar x)).
Proof.
  intro H. assert (abs : (TVar x).[ren (+1)] = TVar x); first by apply H.
  inversion abs; lia.
Qed.

(* }}} *)


(* boring properties about substitution {{{ *)

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

Lemma subst_fv_upn_cases k n σ : ((TVar k).[upn n σ] = TVar k ∧ k < n) +
                                 { j : nat | k = n + j ∧ (TVar k).[upn n σ] = (TVar j).[σ].[ren (+n)]  }.
Proof.
  destruct (decide (k < n)).
  - apply inl. split. apply subst_fv_upn_no; auto. auto.
  - apply inr. exists (k - n). split. lia. rewrite -subst_fv_upn_yes.
    assert (triv : k = n + (k - n)). lia. by rewrite -triv.
Qed.


(* }}} *)

Definition TnClosed : nat → type → Prop := fun n τ => forall σ, τ.[upn n σ] = τ.

Lemma TArrow_nclosed1 {τ1 τ2} {n} : TnClosed n (TArrow τ1 τ2) → TnClosed n τ1.
Proof.
  unfold TnClosed.
  intros H σ.
  assert (H' : TArrow τ1.[upn n σ] τ2.[upn n σ] = TArrow τ1 τ2). asimpl in H. by rewrite H.
  inversion H'.
  by do 2 rewrite H1.
Qed.

Lemma TArrow_nclosed2 {τ1 τ2} {n} : TnClosed n (TArrow τ1 τ2) → TnClosed n τ2.
Proof.
  unfold TnClosed.
  intros H σ.
  assert (H' : TArrow τ1.[upn n σ] τ2.[upn n σ] = TArrow τ1 τ2). asimpl in H; by rewrite H.
  inversion H'.
  by do 2 rewrite H2.
Qed.

Lemma TArrow_nclosed {τ1 τ2} {n} : (TnClosed n τ1 ∧ TnClosed n τ2) ↔ TnClosed n (TArrow τ1 τ2).
Proof.
  split. intros (H1, H2). intro σ. asimpl. by rewrite H1 H2.
  intros. split. by eapply TArrow_nclosed1. by eapply TArrow_nclosed2.
Qed.

Lemma TRec_nclosed1 {τ} {n} : TnClosed n (TRec τ) → TnClosed (S n) τ.
Proof.
  intros H σ.
  assert (H' : TRec τ.[upn (S n) σ] = TRec τ). specialize (H σ). by asimpl in H.
  inversion H'.
  by do 2 rewrite H1.
Qed.

Lemma TRec_nclosed {τ} {n} : TnClosed n (TRec τ) ↔ TnClosed (S n) τ.
Proof.
  split. apply TRec_nclosed1.
  intros H σ.
  asimpl. apply f_equal. apply H.
Qed.

Lemma TnClosed_var (x n : nat) : TnClosed n (TVar x) ↔ x < n.
Proof.
  split.
  - intros.
    destruct (subst_fv_upn_cases x n (ren (+1))) as [[_ eq] | [j [-> _]]].
    + auto.
    + exfalso. unfold TnClosed in H.
      specialize (H (ren (+1))).
      rewrite subst_fv_upn_yes in H.
      asimpl in H. inversion H. lia.
  - intros. intro σ. by apply subst_fv_upn_no.
Qed.

Lemma le_exists_add x y : x ≤ y → exists z, x + z = y.
Proof. intros. exists (y - x). lia. Qed.

Lemma TnClosed_mon τ (n m : nat) : n ≤ m → TnClosed n τ → TnClosed m τ.
Proof.
  intros ple pnτ. intro σ. destruct (le_exists_add n m ple) as [z <-]. generalize σ. clear σ.
  simpl. induction z. asimpl. intro σ. by rewrite pnτ. intro σ. cut (τ.[upn (n + S z) σ] = τ.[upn (n + z) (up σ)]).
  intro. rewrite H. apply IHz. lia. by asimpl.
Qed.

Lemma TnClosed_ren_gen (τ : type) :
  forall (n m : nat) (pτ : TnClosed n τ) (l : nat), TnClosed (m + n) τ.[upn l (ren (+m))].
Proof.
  induction τ; intros.
  - by asimpl.
  - specialize (IHτ1 n m ltac:(by eapply TArrow_nclosed1) l).
    specialize (IHτ2 n m ltac:(by eapply TArrow_nclosed2) l).
    simpl. intro σ. simpl. by rewrite IHτ1 IHτ2.
  - rewrite subst_through_rec.
    apply TRec_nclosed.
    specialize (IHτ (S n) m ltac:(by apply TRec_nclosed) (S l)).
    by asimpl in *.
  - destruct (subst_fv_upn_cases x l (ren (+m))) as [[-> p] | [j [eq ->]]].
    + eapply (TnClosed_mon _ n). lia. apply pτ.
    + asimpl. apply TnClosed_var.
      assert (H : x < n). by apply TnClosed_var. lia.
  - by asimpl.
Qed.

Lemma TnClosed_ren (τ : type) :
  forall (n m : nat) (pτ : TnClosed n τ), TnClosed (m + n) τ.[ren (+m)].
Proof. intros. cut (TnClosed (m + n) τ.[upn 0 (ren (+m))]). by asimpl. by apply TnClosed_ren_gen. Qed.

Lemma TnClosed_subst_gen n τ τ' : forall m, TnClosed (S (m + n)) τ' → TnClosed n τ → TnClosed ((m + n)) τ'.[upn m (τ .: ids)].
Proof.
  generalize dependent n.
  induction τ'; intros.
  - asimpl. intro σ; by asimpl.
  - asimpl.
    specialize (IHτ'1 n m ltac:(by eapply TArrow_nclosed1) H0).
    specialize (IHτ'2 n m ltac:(by eapply TArrow_nclosed2) H0).
    intro σ. simpl. by rewrite IHτ'1 IHτ'2.
  - simpl.
    apply TRec_nclosed.
    apply (IHτ' n (S m)). by apply TRec_nclosed. auto.
  - destruct (subst_fv_upn_cases x m (τ .: ids)) as [[-> p] | [j [eq ->]]].
    + apply TnClosed_var. lia.
    + destruct j.
      * asimpl. by apply TnClosed_ren.
      * asimpl. assert (p1 : x < S (m + n)). by apply TnClosed_var.
        apply TnClosed_var. lia.
  - by asimpl.
Qed.

Lemma TnClosed_subst n τ τ' : TnClosed (S n) τ' → TnClosed n τ → TnClosed n τ'.[τ/].
Proof. intros. rewrite -(upn0 (τ .: ids)). apply (TnClosed_subst_gen n τ τ' 0); auto. Qed.

(* Lemma TRec_closed_unfold_pre {τ τ'} : TClosed (TRec τ) → TClosed τ' → TClosed (τ.[τ'/]). *)

Lemma TRec_closed_unfold {τ} : TClosed (TRec τ) → TClosed (τ.[TRec τ/]).
Proof. intro. cut (TnClosed 0 τ.[TRec τ/]). by simpl. apply TnClosed_subst.
       apply TRec_nclosed. by simpl. by simpl.
Qed.

