From stdpp Require Import base list.
From Autosubst Require Export Autosubst.
Require Export Utf8_core.
From fae_gtlc_mu.equivalence Require Import types consistency_standard consistency_intermediate wf_order upper_bound.
Require Import Relation_Operators.
Require Import Transitive_Closure.
From Coq.Wellfounded Require Import Lexicographic_Product Union.
From Coq.Program Require Import Wf.


Definition smart_lookup {A} (l : list A) (x : A) : (sum { i : nat & l !! i = Some x } (x ∉ l)).
Admitted.

(** maybe better to avoid program fixpoint altogether? *)

Require Import JMeq.

Program Fixpoint struct_validity (A : list (type * type)) (pA : Forall (fun p => TClosed p.1 ∧ TClosed p.2) A) τ (pτC : TClosed τ) τ' (pτ'C : TClosed τ') (pStand : cons_stand τ τ')
        {measure (existT (upper_bound A τ τ') (τ , τ')) lexord} : cons_struct_pre A τ τ' :=
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
    { admit. }
    apply (struct_validity A pA TUnknown pτC τ2 (TArrow_closed2 pτ'C) (GenSymUnknownL τ2)).
    { admit. }
  - destruct (smart_lookup A (TRec TUnknown , TRec τ)) as [[i p] | np].
    + by apply (consGroundRecTauUseCall A τ i).
    + apply consGroundRecTauExposeCall; auto.
      apply (struct_validity ((TRec TUnknown, TRec τ) :: A)). constructor; simpl; auto. split; auto. done. done. apply (TRec_closed_unfold pτ'C).
      assert (H : TUnknown = TUnknown.[TRec TUnknown/]). by asimpl. rewrite H.
      apply GenSymUnknownL.
      { apply t_step. apply left_lex. simpl. apply upper_bound_lt_star_rec; auto. }
  - exfalso. apply (no_var_is_closed i pτ'C).
Admitted.

Next Obligation.
  intros; simplify_eq.
  destruct (categorize τ).
  - apply consStarStar.
  - by apply consTGroundStar.
  - by apply consTGroundStar.
  - by apply consTGroundStar.
  - apply consTauGroundArrow; auto.
    apply (struct_validity A pA TUnknown pτ'C τ1 (TArrow_closed1 pτC) (GenSymUnknownL τ1)).
    { admit. }
    apply (struct_validity A pA τ2 (TArrow_closed2 pτC) TUnknown pτ'C (GenSymUnknownR τ2)).
    { admit. }
  - destruct (smart_lookup A (TRec τ , TRec TUnknown)) as [[i p] | np].
    + by apply (consTauGroundRecUseCall A τ i).
    + apply consTauGroundRecExposeCall; auto.
      apply (struct_validity ((TRec τ, TRec TUnknown) :: A)). constructor; simpl; auto. split; auto. done. apply (TRec_closed_unfold pτC). done.
      assert (H : TUnknown = TUnknown.[TRec TUnknown/]). by asimpl.
      apply GenSymUnknownR.
      { apply t_step. apply left_lex. simpl. apply upper_bound_lt_rec_star; auto. }
  - exfalso. apply (no_var_is_closed i pτC).
Admitted.

(** TArrow *)

Next Obligation.
Proof.
  intros; simplify_eq.
Admitted.


Next Obligation.
Proof.
  intros; simplify_eq.
Admitted.

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
    { apply t_step. apply left_lex. apply upper_bound_lt_rec_rec; auto. }
Admitted.


(** WF *)

Next Obligation.
Proof.
  apply measure_wf.
  apply wf_clos_trans. apply wf_lexprod.
  apply lt_wf. intros _.
  apply wf_ord.
Qed.
