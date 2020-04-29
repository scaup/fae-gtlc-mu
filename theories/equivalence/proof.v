From stdpp Require Import base list.
From Autosubst Require Export Autosubst.
Require Export Utf8_core.
From fae_gtlc_mu.equivalence Require Import types consistency_standard consistency_intermediate upper_bound.
Require Import Relation_Operators.
Require Import Transitive_Closure.
From Coq.Wellfounded Require Import Lexicographic_Product Union.
From Coq.Program Require Import Wf.


Lemma smart_lookup (l : list (type * type)) (x : type * type) : (sum { i : nat & l !! i = Some x } (x ∉ l)).
Proof.
  destruct (decide (x ∈ l)).
  - left. admit.
    (* destruct (elem_of_list_lookup_1 l x e) as [i eq]. *)
  - auto.
Admitted.

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

(* Lemma struct_validity (A : list (type * type)) (pA : Forall (fun p => TClosed p.1 ∧ TClosed p.2) A) *)
(*       τ (pτC : TClosed τ) τ' (pτ'C : TClosed τ') (pStand : cons_stand τ τ') : cons_struct_pre A τ τ'. *)
(* Proof. *)

Program Fixpoint struct_validity (A : list (type * type)) (pA : Forall (fun p => TClosed p.1 ∧ TClosed p.2) A) τ (pτC : TClosed τ) τ' (pτ'C : TClosed τ') (pStand : cons_stand τ τ')
        {measure (existT (upper_bound A τ τ') (size_pair (τ , τ'))) lexord} : cons_struct_pre A τ τ' :=
  match pStand with
  | GenSymUnit => consBaseBase A
  | GenSymUnknownL τr => _
  | GenSymUnknownR τl => _
  | GenSymArrow τ1 τ1' τ2 τ2' s1 s2 =>
    consTArrowTArrow A τ1 τ1' τ2 τ2'
                     (struct_validity A pA τ1' ltac:(simplify_eq; by apply (TArrow_closed1 pτ'C)) τ1 ltac:(simplify_eq; by apply (TArrow_closed1 pτC)) (cons_stand_sym s1))
                     (struct_validity A pA τ2 ltac:(simplify_eq; by apply (TArrow_closed2 pτC)) τ2' ltac:(simplify_eq; by apply (TArrow_closed2 pτ'C)) s2)
  | GenSymVar i => ltac:(simplify_eq; exfalso; apply (no_var_is_closed i pτC))
  | GenSymRec τ τ' P => _
    (* match decide (exists (i : nat), A !! i = Some (TRec τ , TRec τ')) with *)
    (* | left pYes => consTRecTRecUseCall A τ τ' _ _ *)
    (* | right pNo => consTRecTRecExposeCall A τ τ' _ (struct_validity ((TRec τ, TRec τ') :: A) τ.[TRec τ/] ltac:(simplify_eq; by apply (TRec_closed_unfold pτC)) τ'.[TRec τ'/] ltac:(simplify_eq; by apply (TRec_closed_unfold pτ'C)) (cons_stand_unfold P)) *)
    (* end *)
  end.

Next Obligation.
Proof.
  intros; simplify_eq.
  destruct (categorize τ').
  - apply consStarStar.
  - by apply consStarTGround.
  - by apply consStarTGround.
  - by apply consStarTGround.
  - apply consGroundArrowTau; auto.
    apply (struct_validity A pA τ1 (TArrow_closed1 pτ'C) TUnknown pτC (GenSymUnknownR τ1)).
    { simpl. apply ord_right. apply upper_bound_le_unknown_arrow_con. pose (p := size_gt_0 τ2). lia. }
    apply (struct_validity A pA TUnknown pτC τ2 (TArrow_closed2 pτ'C) (GenSymUnknownL τ2)).
    { simpl. apply ord_right. apply upper_bound_le_unknown_arrow_cov.  pose (p := size_gt_0 τ1). lia. }
  - destruct (smart_lookup A (TRec TUnknown , TRec τ)) as [[i p] | np].
    + by apply (consGroundRecTauUseCall A τ i).
    + apply consGroundRecTauExposeCall; auto.
      apply (struct_validity ((TRec TUnknown, TRec τ) :: A)). constructor; simpl; auto. split; auto. done. done. apply (TRec_closed_unfold pτ'C).
      assert (H : TUnknown = TUnknown.[TRec TUnknown/]). by asimpl. rewrite H.
      apply GenSymUnknownL.
      { simpl. apply ord_left. apply upper_bound_lt_star_rec; auto. }
  - exfalso. apply (no_var_is_closed i pτ'C).
Qed.

Next Obligation.
  intros; simplify_eq.
  destruct (categorize τ).
  - apply consStarStar.
  - by apply consTGroundStar.
  - by apply consTGroundStar.
  - by apply consTGroundStar.
  - apply consTauGroundArrow; auto.
    apply (struct_validity A pA TUnknown pτ'C τ1 (TArrow_closed1 pτC) (GenSymUnknownL τ1)).
    { simpl. apply ord_right. apply upper_bound_le_arrow_unknown_con. pose (p := size_gt_0 τ2). lia. }
    apply (struct_validity A pA τ2 (TArrow_closed2 pτC) TUnknown pτ'C (GenSymUnknownR τ2)).
    { simpl. apply ord_right. apply upper_bound_le_arrow_unknown_cov. pose (p := size_gt_0 τ1). lia. }
  - destruct (smart_lookup A (TRec τ , TRec TUnknown)) as [[i p] | np].
    + by apply (consTauGroundRecUseCall A τ i).
    + apply consTauGroundRecExposeCall; auto.
      apply (struct_validity ((TRec τ, TRec TUnknown) :: A)). constructor; simpl; auto. split; auto. done. apply (TRec_closed_unfold pτC). done.
      assert (H : TUnknown = TUnknown.[TRec TUnknown/]). by asimpl.
      apply GenSymUnknownR.
      { apply ord_left. apply upper_bound_lt_rec_star; auto. }
  - exfalso. apply (no_var_is_closed i pτC).
Qed.

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
  + by apply (consTRecTRecUseCall A τ τ' i).
  + apply consTRecTRecExposeCall; auto.
    simplify_eq.
    apply (struct_validity ((TRec τ, TRec τ') :: A)). constructor; simpl; auto. apply (TRec_closed_unfold pτC). apply (TRec_closed_unfold pτ'C).
    (* apply (struct_validity ((TRec τ, TRec τ') :: A) τ.[TRec τ/] (TRec_closed_unfold pτC) τ'.[TRec τ'/] (TRec_closed_unfold pτ'C)). *)
    by apply cons_stand_unfold.
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
