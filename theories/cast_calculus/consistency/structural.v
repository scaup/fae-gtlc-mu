From Autosubst Require Export Autosubst.
From fae_gtlc_mu.stlc_mu Require Export typing.
From fae_gtlc_mu.cast_calculus Require Export types.
From fae_gtlc_mu Require Import prelude.
Require Coq.Logic.JMeq.

Inductive Assumption : Type :=
  | Unfolded
  | LogBodies (τ1 τ2 : type) (P1 : not (τ1 = ⋆)) (P2 : ¬ (τ2 = ⋆)) : Assumption
  | LogStar : Assumption. (* can be of μ.τ ~ μ.⋆ or μ.⋆ ~ μ.τ *)

(** ######################################################################## *)

Definition helper1 (a : Assumption) : (type * type) :=
  match a with
  | Unfolded => (TUnit , TUnit)
  | LogBodies τ1 τ2 P1 P2 => (TRec τ1 , TRec τ2)
  | LogStar => (TUnit , TUnit)
  end.

Fixpoint close_up (τ1τ2 : type * type) (Γ : list (type * type)) :=
  match Γ with
  | nil => τ1τ2
  | cons τ1'τ2' Γ' => close_up ((fst τ1τ2).[fst τ1τ2/] , (snd τ1τ2).[snd τ1τ2/]) Γ'
  end.

Fixpoint close_up_list (Γ : list (type * type)) : list (type * type) :=
  match Γ with
  | nil => nil
  | cons openτ openΓ => (close_up openτ openΓ) :: (close_up_list openΓ)
  end.

Definition assumptions_to_closed_gradual_pairs (A : list Assumption) : list (type * type) :=
  close_up_list (fmap helper1 A).

(*
Fixpoint subs_list (τ : type) (Γ : list type) :=
  match Γ with
  | nil => τ
  | cons τ' Γ' => subs_list τ.[τ'/] Γ'
  end.

Fixpoint close_up (openΓ : list type) : list type :=
  match openΓ with
  | nil => nil
  | cons openτ openΓ => subs_list openτ openΓ :: (close_up openΓ)
  end.

Definition assumptions_to_initial_gradual_context (A : list Assumption) : list type :=
  close_up (map (compose fst assumption_to_open_pair) A).

Definition assumptions_to_final_gradual_context (A : list Assumption) : list type :=
  close_up (map (compose snd assumption_to_open_pair) A).

Definition assumptions_to_gradual_pairs (A : list Assumption) : list (type * type) :=
  zip (assumptions_to_initial_gradual_context A)
      (assumptions_to_final_gradual_context A).
*)

(** ######################################################################## *)


Inductive UBAssumptions : list Assumption -> Type :=
  | empty : UBAssumptions []
  | consUnfolded A : UBAssumptions A -> UBAssumptions (Unfolded :: A)
  | consLogStar A : UBAssumptions A -> UBAssumptions (LogStar :: A)
  | consLogBodies A τ1 τ2 P1 P2 :
      UBAssumptions A -> UB (S (length A)) τ1 -> UB (S (length A)) τ2 -> UBAssumptions (LogBodies τ1 τ2 P1 P2 :: A).
          (* we only need n = 0? *)

Lemma ubass1 A x : UBAssumptions A -> UBAssumptions (update A x Unfolded).
Admitted.

Definition UBAssumption (a : Assumption) (n : nat) : Type :=
  match a with
  | Unfolded => True
  | LogBodies τ1 τ2 P1 P2 => UB n τ1 * UB n τ2
  | LogStar => True
  end.

Lemma ubass2 A (PAub : UBAssumptions A) x τ1 τ2 P1 P2 (eq : A !! x = Some (LogBodies τ1 τ2 P1 P2)) : UB (length A) τ1.
Admitted.

Definition flip (A : Assumption) : Assumption :=
  match A with
  | Unfolded => Unfolded
  | LogBodies τ1 τ2 P1 P2 => LogBodies τ2 τ1 P2 P1
  | LogStar => LogStar
  end.

Lemma ubass_flip A : UBAssumptions A -> UBAssumptions (map flip A).
Admitted.

Lemma flipflip a : flip (flip a) = a.
  by destruct a.
Qed.

Lemma flipflipmap l : map flip (map flip l) = l.
  induction l.
  by simpl.
  simpl. by rewrite flipflip IHl.
Qed.

Lemma map_lookup (l : list Assumption) (f : Assumption -> Assumption) (i : nat) (a : Assumption) :
  l !! i = Some (f a) -> ((map f l) !! i = Some a).
Proof.
Admitted.

Lemma map_update (f : Assumption -> Assumption) (l : list Assumption) i a :
  map f (update l i a) = update (map f l) i (f a).
Proof.
Admitted.




Reserved Notation "A ⊢ τ ~ τ'" (at level 4, τ, τ' at next level).
Inductive cons_struct (A : list Assumption) : type -> type -> Type :=
  (** ground and star *)
  (* downcasting from star to ground *)
  | consStarTGround τ :
      Ground τ →
      A ⊢ ⋆ ~ τ
  (* upcasting from ground to star *)
  | consTGroundStar τ :
      Ground τ →
      A ⊢ τ ~ ⋆
  (** factorization through ground types *)
  | consTauStar τ τG :
      UB (length A) τ ->
      (Ground τ -> False) ->
      (not (τ = ⋆)) →
      (get_shape τ = Some τG) ->
      A ⊢ τ ~ τG ->
      A ⊢ τ ~ ⋆
  | consStarTau τ τG :
      UB (length A) τ ->
      (Ground τ -> False) ->
      (not (τ = ⋆)) →
      (get_shape τ = Some τG) ->
      A ⊢ τG ~ τ ->
      A ⊢ ⋆ ~ τ
  (** identiy casts between Base and ⋆ *)
  | consBaseBase :
      A ⊢ TUnit ~ TUnit
  | consStarStar :
      A ⊢ ⋆ ~ ⋆
  (** between types of same structure *)
  (* between + types *)
  | consTSumTSum τ1 τ1' τ2 τ2' :
      A ⊢ τ1 ~ τ1' ->
      A ⊢ τ2 ~ τ2' ->
      A ⊢ (τ1 + τ2)%type ~ (τ1' + τ2')%type
  (* between × types *)
  | consTProdTProd τ1 τ1' τ2 τ2' :
      A ⊢ τ1 ~ τ1' ->
      A ⊢ τ2 ~ τ2' ->
      A ⊢ (τ1 × τ2) ~ (τ1' × τ2')
  (* between → types *)
  | consTArrowTArrow τ1 τ2 τ3 τ4 :
      A ⊢ τ3 ~ τ1 ->
      A ⊢ τ2 ~ τ4 ->
      A ⊢ (TArrow τ1 τ2) ~ (TArrow τ3 τ4)
  (* between μ types; exposing recursive call *)
  | consExposeRecursion τi τf (Pi : τi = ⋆ → False) (Pf : τf = ⋆ → False) :
    (LogBodies τi τf Pi Pf :: A) ⊢ τi ~ τf →
    A ⊢ (TRec τi) ~ (TRec τf)
  | consExposeRecursionLStar τ :
      (LogStar :: A) ⊢ ⋆ ~ τ ->
      A ⊢ (TRec ⋆) ~ (TRec τ)
  | consExposeRecursionRStar τ :
      (LogStar :: A) ⊢ τ ~ ⋆ ->
      A ⊢ (TRec τ) ~ (TRec ⋆)
  (* exposing "extra" recursive call *)
  | consExposeExtraRecursionRStar i τb τb' P P' :
      (A !! i) = Some (LogBodies τb τb' P P') ->
      (update A i Unfolded) ⊢ τb ~ ⋆ ->
      A ⊢ (TVar i) ~ (TRec ⋆)
  | consExposeExtraRecursionLStar i τb τb' P P' :
      (A !! i) = Some (LogBodies τb τb' P P') ->
      (update A i Unfolded) ⊢ ⋆ ~ τb' ->
      A ⊢ (TRec ⋆) ~ (TVar i)
  (** Variables *)
  (* consuming assumption; using previously exposed recursive call *)
  (* | consUseRecursion i : *)
  | consUseRecursion i :
      (* (A !! i) = Some a -> (* we will only need rule with = Some (LogBodies ... )*) *)
      i < length A ->
      (* is_Some (A !! i) -> *)
      A ⊢ (TVar i) ~ (TVar i)
  | consUseRecursionLStar i :
      (A !! i) = Some LogStar ->
      A ⊢ (TRec ⋆) ~ (TVar i)
  | consUseRecursionRStar i :
      (A !! i) = Some LogStar ->
      A ⊢ (TVar i) ~ (TRec ⋆)
  (* consuming assumption; using previously "extra" exposed recursive call *)
  | consUseExtraRecursionLStar i :
      (A !! i) = Some Unfolded ->
      A ⊢ (TRec ⋆) ~ (TVar i)
  | consUseExtraRecursionRStar i :
      (A !! i) = Some Unfolded ->
      A ⊢ (TVar i) ~ (TRec ⋆)
  (* initiating new assumption; exposing new recursive call to use later *)
  (* .... *)
  (* factorizing through μ.⋆ for variables; !needs to be a separate case! *)
  (* | consVarStar i : *)
      (* i < length A -> (* because of this reason we cannot use consTauStar*) *)
      (* A ⊢ (TVar i) ~ (TRec ⋆) -> *)
      (* A ⊢ (TVar i) ~ ⋆ *)
  (* | consStarVar i : *)
      (* i < length A -> (* because of this reason we cannot use consStarTau*) *)
      (* A ⊢ (TRec ⋆) ~ (TVar i) -> *)
      (* A ⊢ ⋆ ~ (TVar i) *)
where "A ⊢ τ ~ τ'" := (cons_struct A τ τ').


