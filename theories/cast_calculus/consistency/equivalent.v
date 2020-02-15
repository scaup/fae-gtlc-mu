From Autosubst Require Export Autosubst.
From fae_gtlc_mu Require Import prelude.
From fae_gtlc_mu.cast_calculus Require Import types consistency.standard consistency.structural.
(* Require Coq.Logic.JMeq. *)

Lemma cons_struct_symmetric (A : list Assumption) (τ τ' : type) (P : cons_struct A τ τ') : cons_struct (map flip A) τ' τ.
Proof.
  induction P; try by constructor.
  - apply consStarTau with (τG := τG); by (done || rewrite map_length).
  - apply consTauStar with (τG := τG); by (done || rewrite map_length).
  - apply consExposeRecursion with (Pi := Pf) (Pf := Pi).
    by rewrite map_cons in IHP.
  - apply (consExposeExtraRecursionLStar (map flip A) i τb' τb P' P); first by apply map_lookup; unfold flip.
    by rewrite map_update in IHP.
  - apply (consExposeExtraRecursionRStar (map flip A) i τb' τb P' P); first by apply map_lookup; unfold flip.
    by rewrite map_update in IHP.
  (* - by apply consUseRecursion with (a := flip a). *)
  - apply consUseRecursion.
    (* apply map_lookup. *)
    by rewrite map_length.
    (* by rewrite flipflip. *)
  - apply consUseRecursionRStar.
    by apply map_lookup.
  - apply consUseRecursionLStar.
    by apply map_lookup.
  - apply consUseExtraRecursionRStar.
    by apply map_lookup.
  - apply consUseExtraRecursionLStar.
    by apply map_lookup.
Qed.

Lemma cons_struct_symmetric' (A : list Assumption) (τ τ' : type) (P : cons_struct (map flip A) τ τ') : cons_struct A τ' τ.
Proof.
  rewrite -(flipflipmap A).
  by apply cons_struct_symmetric.
Qed.


(* Inductive AmountMissa *)

Fixpoint possible_unfoldings (A : list Assumption) : nat :=
  match A with
  | nil => 0
  | cons x x0 => match x with
                | Unfolded => possible_unfoldings x0
                | LogBodies τ1 τ2 P1 P2 => S (possible_unfoldings x0)
                | LogStar => possible_unfoldings x0
                end
  end.

Lemma unfold_in_assumptions A x k τ1 τ2 P1 P2 :
  (A !! x = Some (LogBodies τ1 τ2 P1 P2)) ->
  possible_unfoldings A = S k ->
  possible_unfoldings (update A x Unfolded) = k.
Admitted.

Lemma xf_possible_unfoldings A l τ1 τ2 P1 P2 : possible_unfoldings A = 0 -> A !! l = Some (LogBodies τ1 τ2 P1 P2) -> False.
Proof.
Admitted.

Lemma possible_unfoldings_flip l : possible_unfoldings (map flip l) = possible_unfoldings l.
Admitted.

Lemma cons_struct_star_zero_unfoldings (τ : type) (A : list Assumption) (PAub : UBAssumptions A) (P : UB (length A) τ) (S : possible_unfoldings A = 0) : A ⊢ τ ~ ⋆.
Proof.
  generalize dependent A.
  induction τ; intros.
  - apply consTGroundStar; by constructor.
  - destruct (Is_Unknown_dec τ1); simplify_eq.
    + (* τ1 = ⋆ *) destruct (Is_Unknown_dec τ2); simplify_eq.
      * (* τ2 = ⋆ *) apply consTGroundStar; by constructor.
      * (* τ2 ≠ ⋆ *) apply consTauStar with (τG := ⋆ × ⋆).
        auto.
        intro abs; inversion abs; apply n; symmetry; apply H0.
        intro abs; inversion abs.
        by simpl.
        apply consTProdTProd. apply consStarStar. apply IHτ2.
        by inversion P.
        by inversion P.
        auto.
    + (* τ1 ≠ ⋆ *)
      apply consTauStar with (τG := ⋆ × ⋆). auto.
        intro abs; inversion abs; apply n; symmetry; apply H0.
        intro abs; inversion abs.
        by simpl.
        apply consTProdTProd. apply IHτ1.
          by inversion P.
          by inversion P.
          auto. apply IHτ2. by inversion P. auto.
          by inversion P. auto.
  - destruct (Is_Unknown_dec τ1); simplify_eq.
    + (* τ1 = ⋆ *) destruct (Is_Unknown_dec τ2); simplify_eq.
      * (* τ2 = ⋆ *) apply consTGroundStar; by constructor.
      * (* τ2 ≠ ⋆ *) apply consTauStar with (τG := TSum ⋆ ⋆).
        auto.
        intro abs; inversion abs; apply n; symmetry; apply H0.
        intro abs; inversion abs.
        by simpl.
        apply consTSumTSum. apply consStarStar. apply IHτ2. by inversion P. auto.
          by inversion P. auto.
    + (* τ1 ≠ ⋆ *)
      apply consTauStar with (τG := TSum ⋆ ⋆).
        auto.
        intro abs; inversion abs; apply n; symmetry; apply H0.
        intro abs; inversion abs.
        by simpl.
        apply consTSumTSum. apply IHτ1. by inversion P. auto.
          by inversion P. auto.
        apply IHτ2. by inversion P. auto.
          by inversion P. auto.
  - destruct (Is_Unknown_dec τ1); simplify_eq.
    + (* τ1 = ⋆ *) destruct (Is_Unknown_dec τ2); simplify_eq.
      * (* τ2 = ⋆ *) apply consTGroundStar; by constructor.
      * (* τ2 ≠ ⋆ *) apply consTauStar with (τG := TArrow ⋆ ⋆).
        done.
        intro abs; inversion abs; apply n; symmetry; apply H0.
        intro abs; inversion abs.
        by simpl.
        apply consTArrowTArrow. apply consStarStar. apply IHτ2.
        by inversion P. auto.
          by inversion P. auto.
    + (* τ1 ≠ ⋆ *)
      apply consTauStar with (τG := TArrow ⋆ ⋆).
        done.
        intro abs; inversion abs; apply n; symmetry; apply H0.
        intro abs; inversion abs.
        by simpl.
        apply consTArrowTArrow.
        apply cons_struct_symmetric'; apply IHτ1.
          apply ubass_flip.
          by inversion P. auto.
        rewrite map_length. by inversion P.
        by rewrite possible_unfoldings_flip.
        apply IHτ2. by inversion P.
          by inversion P. auto.
  - destruct (Is_Unknown_dec τ); simplify_eq.
    + (* τ = ⋆ *) apply consTGroundStar; constructor.
    + (* τ ≠ ⋆ *) apply consTauStar with (τG := TRec ⋆).
        done.
        intro abs; inversion abs; apply n; symmetry; apply H0.
        intro abs; inversion abs.
        auto.
        apply consExposeRecursionRStar.
        apply IHτ.
        by apply consLogStar.
        by inversion P.
        done.
  - apply consTauStar with (τG := TRec ⋆).
    done.
    intro abs; inversion abs; apply n; symmetry; apply H0.
    intro abs; inversion abs.
    auto.
    inversion P; simplify_eq.
    destruct (A !! x) eqn:eq.
    + destruct a.
      * by apply consUseExtraRecursionRStar.
      * exfalso. eapply xf_possible_unfoldings; done.
      * by apply consUseRecursionRStar.
    + exfalso. rewrite <- lookup_lt_is_Some in H0.
      destruct H0; rewrite H in eq; inversion eq.
  - apply consStarStar.
Qed.


Lemma cons_struct_starR (A : list Assumption) (PAub : UBAssumptions A) (k : nat) (S : possible_unfoldings A = k) (τ : type) (P : UB (length A) τ) : A ⊢ τ ~ ⋆.
Proof.
  generalize dependent A.
  generalize dependent τ.
  induction k; first by intros; by apply cons_struct_star_zero_unfoldings.
  intros τ.
  induction τ; intros.
  - apply consTGroundStar; by constructor.
  - destruct (Is_Unknown_dec τ1); simplify_eq.
    + (* τ1 = ⋆ *) destruct (Is_Unknown_dec τ2); simplify_eq.
      * (* τ2 = ⋆ *) apply consTGroundStar; by constructor.
      * (* τ2 ≠ ⋆ *) apply consTauStar with (τG := ⋆ × ⋆).
        auto.
        intro abs; inversion abs; apply n; symmetry; apply H0.
        intro abs; inversion abs.
        by simpl.
        apply consTProdTProd. apply consStarStar. apply IHτ2.
        by inversion P.
        inversion P. auto.
        inversion P. auto.
    + (* τ1 ≠ ⋆ *)
      apply consTauStar with (τG := ⋆ × ⋆). auto.
        intro abs; inversion abs; apply n; symmetry; apply H0.
        intro abs; inversion abs.
        by simpl.
        apply consTProdTProd. apply IHτ1. by inversion P. inversion P. auto.
        inversion P. auto.
        apply IHτ2. by inversion P. inversion P. auto.
        inversion P. auto.
  - destruct (Is_Unknown_dec τ1); simplify_eq.
    + (* τ1 = ⋆ *) destruct (Is_Unknown_dec τ2); simplify_eq.
      * (* τ2 = ⋆ *) apply consTGroundStar; by constructor.
      * (* τ2 ≠ ⋆ *) apply consTauStar with (τG := TSum ⋆ ⋆).
        auto.
        intro abs; inversion abs; apply n; symmetry; apply H0.
        intro abs; inversion abs.
        by simpl.
        apply consTSumTSum. apply consStarStar. apply IHτ2. by inversion P. inversion P. auto.
        inversion P. auto.
    + (* τ1 ≠ ⋆ *)
      apply consTauStar with (τG := TSum ⋆ ⋆).
        auto.
        intro abs; inversion abs; apply n; symmetry; apply H0.
        intro abs; inversion abs.
        by simpl.
        apply consTSumTSum. apply IHτ1. by inversion P. auto. by inversion P. apply IHτ2. by inversion P. auto. by inversion P.
  - destruct (Is_Unknown_dec τ1); simplify_eq.
    + (* τ1 = ⋆ *) destruct (Is_Unknown_dec τ2); simplify_eq.
      * (* τ2 = ⋆ *) apply consTGroundStar; by constructor.
      * (* τ2 ≠ ⋆ *) apply consTauStar with (τG := TArrow ⋆ ⋆).
        done.
        intro abs; inversion abs; apply n; symmetry; apply H0.
        intro abs; inversion abs.
        by simpl.
        apply consTArrowTArrow. apply consStarStar. apply IHτ2.
        by inversion P. auto. by inversion P.
    + (* τ1 ≠ ⋆ *)
      apply consTauStar with (τG := TArrow ⋆ ⋆).
        done.
        intro abs; inversion abs; apply n; symmetry; apply H0.
        intro abs; inversion abs.
        by simpl.
        apply consTArrowTArrow.
        apply cons_struct_symmetric'; apply IHτ1. simpl. by apply ubass_flip. rewrite possible_unfoldings_flip. by inversion P. rewrite map_length. by inversion P.
        (* by rewrite possible_unfoldings_flip. *)
        apply IHτ2. by inversion P. by inversion P.
        by inversion P.
  - destruct (Is_Unknown_dec τ); simplify_eq.
    + (* τ = ⋆ *) apply consTGroundStar; constructor.
    + (* τ ≠ ⋆ *) apply consTauStar with (τG := TRec ⋆).
        done.
        intro abs; inversion abs; apply n; symmetry; apply H0.
        intro abs; inversion abs.
        auto.
        apply consExposeRecursionRStar.
        apply IHτ.
        apply consLogStar.
        by inversion P.
        by inversion P.
        by inversion P.
  - apply consTauStar with (τG := TRec ⋆).
    done.
    intro abs; inversion abs; apply n; symmetry; apply H0.
    intro abs; inversion abs.
    auto.
    inversion P; simplify_eq.
    destruct (A !! x) eqn:eq.
    + destruct a.
      * by apply consUseExtraRecursionRStar.
      * eapply consExposeExtraRecursionRStar; first done.
        (** Induction Hypothesis *) apply IHk.
        by apply ubass1.
        eapply unfold_in_assumptions; done.
        (** Assumptions need to be below *)
        rewrite alter_length.
        eapply ubass2. auto. apply eq.
      * by apply consUseRecursionRStar.
    + exfalso. rewrite <- lookup_lt_is_Some in H0.
      destruct H0; rewrite H in eq; inversion eq.
  - apply consStarStar.
Qed.

Lemma cons_struct_starL (A : list Assumption) (PAub : UBAssumptions A) (k : nat) (S : possible_unfoldings A = k) (τ : type) (P : UB (length A) τ) : A ⊢ ⋆ ~ τ.
Proof.
  apply cons_struct_symmetric'.
  apply cons_struct_starR with (k := k).
  apply ubass_flip. auto.
  by rewrite possible_unfoldings_flip.
  by rewrite map_length.
Qed.

Lemma cons_stand_implies_struct (A : list Assumption) (PAub : UBAssumptions A) (k : nat) (S : possible_unfoldings A = k) (τ τ' : type) (P : UB (length A) τ) (P' : UB (length A) τ') (Pstand : cons_stand 0 τ τ') : A ⊢ τ ~ τ'.
Proof.
  generalize dependent A.
  generalize dependent k.
  induction Pstand; intros.
  - apply consBaseBase.
  - apply cons_struct_starL with (k := k); (constructor || auto).
  - apply cons_struct_starR with (k := k); (constructor || auto).
  - apply consTSumTSum.
    apply IHPstand1 with (k := k); try auto. by inversion P. by inversion P'.
    apply IHPstand2 with (k := k); try auto. by inversion P. by inversion P'.
  - apply consTProdTProd.
    apply IHPstand1 with (k := k); try auto. by inversion P. by inversion P'.
    apply IHPstand2 with (k := k); try auto. by inversion P. by inversion P'.
  - apply consTArrowTArrow.
    apply cons_struct_symmetric'.
    apply IHPstand1 with (k := k). apply ubass_flip. try auto. by rewrite possible_unfoldings_flip. rewrite map_length. by inversion P. rewrite map_length. by inversion P'.
    apply IHPstand2 with (k := k).
      by inversion P. by inversion P'.
      by inversion P. by inversion P'.
  - apply consUseRecursion. by inversion P'.
  - destruct (Is_Unknown_dec τ); simplify_eq.
    + apply consExposeRecursionLStar.
      apply IHPstand with (k := (possible_unfoldings A)).
      apply consLogStar. auto. by simpl. constructor. inversion P'. by simpl.
    + destruct (Is_Unknown_dec τ'); simplify_eq.
      * apply consExposeRecursionRStar.
        apply IHPstand with (k := possible_unfoldings A).
        apply consLogStar. auto. by simpl. simpl. inversion P'. by inversion P. constructor.
      * apply consExposeRecursion with (Pi := n0) (Pf := n1).
        apply IHPstand with (k := S (possible_unfoldings A)).
        apply consLogBodies. auto. by inversion P. by inversion P'. by simpl.
        simpl. by inversion P. by inversion P'.
Qed.
