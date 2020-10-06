From stdpp Require Import base list.
From Autosubst Require Export Autosubst.
Require Export Utf8_core.
From fae_gtlc_mu.backtranslation.implication_consistencies.help_lemmas Require Import intermediate upper_bound.
From fae_gtlc_mu.cast_calculus Require Export types types_notations types_lemmas consistency consistency_lemmas.
Require Import Relation_Operators.
Require Import Transitive_Closure.
From Coq.Wellfounded Require Import Lexicographic_Product Union.
From Coq.Program Require Import Wf.


Lemma smart_lookup (l : list (type * type)) (x : type * type) : (sum { i : nat & l !! i = Some x } (x ∉ l)).
Proof.
  destruct (decide (x ∈ l)).
  - left.
    induction l.
    + exfalso. inversion e.
    + destruct (decide (x = a)).
      * rewrite e0. by exists 0.
      * destruct (decide (x ∈ l)).
        destruct (IHl e0). exists (S x0). by simpl.
        exfalso. inversion e. simplify_eq. by apply n0.
  - by right.
Qed.

Definition lexord : relation (@sigT nat (fun _ => nat)) :=
  (lexprod _ _ lt (fun _ => lt)).

Lemma ord_left n n' m m' : n < n' → lexord (existT n m) (existT n' m').
Proof.
  intros. by apply left_lex.
Qed.

Lemma ord_right n n' m m' : n ≤ n' → m < m' → lexord (existT n m) (existT n' m').
Proof.
  intros.
  destruct (decide (n < n')).
  - by apply left_lex.
  - assert (triv : n = n'). lia. rewrite triv. clear triv.
    by apply right_lex.
Qed.

Fixpoint size (τ : type) : nat :=
  match τ with
  | TUnit => 1
  | TProd τ1 τ2 => size τ1 + size τ2
  | TSum τ1 τ2 => size τ1 + size τ2
  | TArrow τ1 τ2 => size τ1 + size τ2
  | TRec τ => S (size τ)
  | TVar x => 1
  | TUnknown => 1
  end.

Lemma size_gt_0 τ : 0 < size τ.
Proof. induction τ; simpl; lia. Qed.

Definition size_pair (p : type * type) : nat :=
  match p with | pair x x0 => size x + size x0 end.

Require Import JMeq.

(** TODO; remove program fixpoint... *)

(* Lemma struct_validity (A : list (type * type)) (pA : Forall (fun p => Closed p.1 ∧ Closed p.2) A) *)
(*       τ (pτC : Closed τ) τ' (pτ'C : Closed τ') (pStand : consistency τ τ') : alternative_consistency_pre A τ τ'. *)
(* Proof. *)

Inductive Cat : type → Type :=
  | CUnknown : Cat TUnknown
  | CGroundUnit : Ground TUnit → Cat TUnit
  | CGroundProd : Ground (TProd TUnknown TUnknown) → Cat (TProd TUnknown TUnknown)
  | CGroundSum : Ground (TSum TUnknown TUnknown) → Cat (TSum TUnknown TUnknown)
  | CGroundArrow : Ground (TArrow TUnknown TUnknown) → Cat (TArrow TUnknown TUnknown)
  | CGroundRec : Ground (TRec TUnknown) → Cat (TRec TUnknown)
  | CProd τ1 τ2 : (τ1 ≠ TUnknown ∨ τ2 ≠ TUnknown) → Cat (TProd τ1 τ2)
  | CSum τ1 τ2 : (τ1 ≠ TUnknown ∨ τ2 ≠ TUnknown) → Cat (TSum τ1 τ2)
  | CArrow τ1 τ2 : (τ1 ≠ TUnknown ∨ τ2 ≠ TUnknown) → Cat (TArrow τ1 τ2)
  | CRec τ : (τ ≠ TUnknown) → Cat (TRec τ)
  | CVar i : Cat (TVar i).

Lemma categorize (τ : type) : Cat τ.
Proof.
  destruct τ; try by do 2 constructor.
  - destruct (decide (τ1 = ⋆)); simplify_eq.
    destruct (decide (τ2 = ⋆)); simplify_eq.
    constructor. constructor. constructor; auto. constructor; auto.
  - destruct (decide (τ1 = ⋆)); simplify_eq.
    destruct (decide (τ2 = ⋆)); simplify_eq.
    constructor. constructor. constructor; auto. constructor; auto.
  - destruct (decide (τ1 = ⋆)); simplify_eq.
    destruct (decide (τ2 = ⋆)); simplify_eq.
    constructor. constructor. constructor; auto. constructor; auto.
  - destruct (decide (τ = ⋆)); simplify_eq.
    constructor. constructor. constructor; auto.
Qed.


Program Fixpoint struct_validity (A : list (type * type)) (pA : Forall (fun p => Closed p.1 ∧ Closed p.2) A) τ (pτC : Closed τ) τ' (pτ'C : Closed τ') (pStand : consistency_open τ τ')
        {measure (existT (upper_bound A τ τ') (size_pair (τ , τ'))) lexord} : alternative_consistency_pre A τ τ' :=
  match pStand with
  | GenSymUnit => consp_BaseBase A
  | GenSymUnknownL τr => _
  | GenSymUnknownR τl => _
  | GenSymProd τ1 τ1' τ2 τ2' s1 s2 =>
    consp_TProdTProd A τ1 τ1' τ2 τ2'
                     (struct_validity A pA τ1 ltac:(simplify_eq; by apply (TProd_closed1 pτC)) τ1' ltac:(simplify_eq; by apply (TProd_closed1 pτ'C)) s1)
                     (struct_validity A pA τ2 ltac:(simplify_eq; by apply (TProd_closed2 pτC)) τ2' ltac:(simplify_eq; by apply (TProd_closed2 pτ'C)) s2)
  | GenSymSum τ1 τ1' τ2 τ2' s1 s2 =>
    consp_TSumTSum A τ1 τ1' τ2 τ2'
                     (struct_validity A pA τ1 ltac:(simplify_eq; by apply (TSum_closed1 pτC)) τ1' ltac:(simplify_eq; by apply (TSum_closed1 pτ'C)) s1)
                     (struct_validity A pA τ2 ltac:(simplify_eq; by apply (TSum_closed2 pτC)) τ2' ltac:(simplify_eq; by apply (TSum_closed2 pτ'C)) s2)
  | GenSymArrow τ1 τ1' τ2 τ2' s1 s2 =>
    consp_TArrowTArrow A τ1 τ1' τ2 τ2'
                     (struct_validity A pA τ1' ltac:(simplify_eq; by apply (TArrow_closed1 pτ'C)) τ1 ltac:(simplify_eq; by apply (TArrow_closed1 pτC)) (consistency_open_sym s1))
                     (struct_validity A pA τ2 ltac:(simplify_eq; by apply (TArrow_closed2 pτC)) τ2' ltac:(simplify_eq; by apply (TArrow_closed2 pτ'C)) s2)
  | GenSymVar i => ltac:(simplify_eq; exfalso; apply (no_var_is_closed i pτC))
  | GenSymRec τ τ' P => _
    (* match decide (exists (i : nat), A !! i = Some (TRec τ , TRec τ')) with *)
    (* | left pYes => atomic_UseRecursion A τ τ' _ _ *)
    (* | right pNo => exposeRecursiveCAll A τ τ' _ (struct_validity ((TRec τ, TRec τ') :: A) τ.[TRec τ/] ltac:(simplify_eq; by apply (TRec_closed_unfold pτC)) τ'.[TRec τ'/] ltac:(simplify_eq; by apply (TRec_closed_unfold pτ'C)) (consistency_unfold P)) *)
    (* end *)
  end.

Next Obligation.
Proof.
  intros; simplify_eq.
  destruct (categorize τ'); (try (by apply consp_StarTGround)); try apply consp_StarStar.
  - apply consp_GroundProdTau; auto.
    apply (struct_validity A pA TUnknown pτC τ1 (TProd_closed1 pτ'C) (GenSymUnknownL τ1)).
    { simpl. apply ord_right. apply upper_bound_le_unknown_prod1. pose (p := size_gt_0 τ2). lia. }
    apply (struct_validity A pA TUnknown pτC τ2 (TProd_closed2 pτ'C) (GenSymUnknownL τ2)).
    { simpl. apply ord_right. apply upper_bound_le_unknown_prod2. pose (p := size_gt_0 τ1). lia. }
  - apply consp_GroundSumTau; auto.
    apply (struct_validity A pA TUnknown pτC τ1 (TSum_closed1 pτ'C) (GenSymUnknownL τ1)).
    { simpl. apply ord_right. apply upper_bound_le_unknown_sum1. pose (p := size_gt_0 τ2). lia. }
    apply (struct_validity A pA TUnknown pτC τ2 (TSum_closed2 pτ'C) (GenSymUnknownL τ2)).
    { simpl. apply ord_right. apply upper_bound_le_unknown_sum2. pose (p := size_gt_0 τ1). lia. }
  - apply consp_GroundArrowTau; auto.
    apply (struct_validity A pA τ1 (TArrow_closed1 pτ'C) TUnknown pτC (GenSymUnknownR τ1)).
    { simpl. apply ord_right. apply upper_bound_le_unknown_arrow_con. pose (p := size_gt_0 τ2). lia. }
    apply (struct_validity A pA TUnknown pτC τ2 (TArrow_closed2 pτ'C) (GenSymUnknownL τ2)).
    { simpl. apply ord_right. apply upper_bound_le_unknown_arrow_cov.  pose (p := size_gt_0 τ1). lia. }
  - destruct (smart_lookup A (TRec TUnknown , TRec τ)) as [[i p] | np].
    + by apply (consp_GroundRecTauUseCall A τ i).
    + apply consp_GroundRecTauExposeCall; auto.
      apply (struct_validity ((TRec TUnknown, TRec τ) :: A)). constructor; simpl; auto. split; auto. done. done. apply (TRec_closed_unfold pτ'C).
      assert (H : TUnknown = TUnknown.[TRec TUnknown/]). by asimpl. rewrite H.
      apply GenSymUnknownL.
      { simpl. apply ord_left. apply upper_bound_lt_star_rec; auto. }
  - exfalso. apply (no_var_is_closed i pτ'C).
Qed.

Next Obligation.
  intros; simplify_eq.
  destruct (categorize τ); (try (by apply consp_TGroundStar)); try apply consp_StarStar.
  - apply consp_TauGroundProd; auto.
    apply (struct_validity A pA τ1 (TProd_closed1 pτC) TUnknown pτ'C (GenSymUnknownR τ1)).
    { simpl. apply ord_right. apply upper_bound_le_prod_unknown1. pose (p := size_gt_0 τ2). lia. }
    apply (struct_validity A pA τ2 (TProd_closed2 pτC) TUnknown pτ'C (GenSymUnknownR τ2)).
    { simpl. apply ord_right. apply upper_bound_le_prod_unknown2. pose (p := size_gt_0 τ1). lia. }
  - apply consp_TauGroundSum; auto.
    apply (struct_validity A pA τ1 (TSum_closed1 pτC) TUnknown pτ'C (GenSymUnknownR τ1)).
    { simpl. apply ord_right. apply upper_bound_le_sum_unknown1. pose (p := size_gt_0 τ2). lia. }
    apply (struct_validity A pA τ2 (TSum_closed2 pτC) TUnknown pτ'C (GenSymUnknownR τ2)).
    { simpl. apply ord_right. apply upper_bound_le_sum_unknown2. pose (p := size_gt_0 τ1). lia. }
  - apply consp_TauGroundArrow; auto.
    apply (struct_validity A pA TUnknown pτ'C τ1 (TArrow_closed1 pτC) (GenSymUnknownL τ1)).
    { simpl. apply ord_right. apply upper_bound_le_arrow_unknown_con. pose (p := size_gt_0 τ2). lia. }
    apply (struct_validity A pA τ2 (TArrow_closed2 pτC) TUnknown pτ'C (GenSymUnknownR τ2)).
    { simpl. apply ord_right. apply upper_bound_le_arrow_unknown_cov. pose (p := size_gt_0 τ1). lia. }
  - destruct (smart_lookup A (TRec τ , TRec TUnknown)) as [[i p] | np].
    + by apply (consp_TauGroundRecUseCall A τ i).
    + apply consp_TauGroundRecExposeCall; auto.
      apply (struct_validity ((TRec τ, TRec TUnknown) :: A)). constructor; simpl; auto. split; auto. done. apply (TRec_closed_unfold pτC). done.
      assert (H : TUnknown = TUnknown.[TRec TUnknown/]). by asimpl.
      apply GenSymUnknownR.
      { apply ord_left. apply upper_bound_lt_rec_star; auto. }
  - exfalso. apply (no_var_is_closed i pτC).
Qed.


Next Obligation. Proof. intros; simplify_eq. apply ord_right. apply upper_bound_le_prod1. simpl. pose (p := size_gt_0 τ2). lia. Qed.
Next Obligation. Proof. intros; simplify_eq. apply ord_right. apply upper_bound_le_prod2. simpl. pose (p := size_gt_0 τ1). lia. Qed.
Next Obligation. Proof. intros; simplify_eq. apply ord_right. apply upper_bound_le_sum1. simpl. pose (p := size_gt_0 τ2). lia. Qed.
Next Obligation. Proof. intros; simplify_eq. apply ord_right. apply upper_bound_le_sum2. simpl. pose (p := size_gt_0 τ1). lia. Qed.



(** TArrow *)

Next Obligation.
Proof.
  intros; simplify_eq.
  apply ord_right. apply upper_bound_le_arrow_l. simpl.
  pose (p := size_gt_0 τ2). lia.
Qed.


Next Obligation.
Proof.
  intros; simplify_eq.
  apply ord_right. apply upper_bound_le_arrow_r.
  simpl. pose (p1 := size_gt_0 τ1). lia.
Qed.

(** TRec *)

Next Obligation.
Proof.
  intros.
  destruct (smart_lookup A (TRec τ , TRec τ')) as [[i p] | np].
  + by apply (consp_TRecTRecUseCall A τ τ' i).
  + apply consp_TRecTRecExposeCall; auto.
    simplify_eq.
    apply (struct_validity ((TRec τ, TRec τ') :: A)). constructor; simpl; auto. apply (TRec_closed_unfold pτC). apply (TRec_closed_unfold pτ'C).
    (* apply (struct_validity ((TRec τ, TRec τ') :: A) τ.[TRec τ/] (TRec_closed_unfold pτC) τ'.[TRec τ'/] (TRec_closed_unfold pτ'C)). *)
    by apply consistency_open_unfold.
    { apply ord_left. apply upper_bound_lt_rec_rec; auto. }
Qed.


(** WF *)

Next Obligation.
Proof.
  apply measure_wf.
  apply wf_lexprod.
  apply lt_wf. intros _.
  apply lt_wf.
Qed.
