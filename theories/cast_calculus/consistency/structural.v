From Autosubst Require Export Autosubst.
From fae_gtlc_mu.cast_calculus Require Export types.
From fae_gtlc_mu Require Import prelude.
Require Coq.Logic.JMeq.

Inductive Assumption : Type :=
  | Unfolded
  | LogBodies (τ1 τ2 : type) (P1 : not (τ1 = ⋆)) (P2 : ¬ (τ2 = ⋆)) : Assumption
  | LogStar : Assumption. (* can be of μ.τ ~ μ.⋆ or μ.⋆ ~ μ.τ *)

(*
Inductive Shape : Type :=
  | Arrow
  | Sum
  | Prod
  | Rec.
*)


(* possibly with sigma type and proof of groundness *)
Definition get_shape (τ : type) : option type :=
  match τ with
  | TUnit => None
  | TProd x x0 => Some (TProd ⋆ ⋆)
  | TSum x x0 => Some (TSum ⋆ ⋆)
  | TArrow x x0 => Some (TArrow ⋆ ⋆)
  | TRec τ => Some (TRec ⋆)
  | TVar x => Some (TRec ⋆)
  | TUnknown => None
  end.

(*
Definition to_ground (τ : type) : option type :=
  match τ with
  | TUnit => None
  | TProd τ1 τ2 => match (Is_Unknown_dec τ1) with
                    | left _ => match (Is_Unknown_dec τ2) with
                               | left _ => None
                               | right _ => Some (⋆ × ⋆)
                             end
                    | right _ => Some (⋆ × ⋆)
                  end
  | TSum τ1 τ2 => match (Is_Unknown_dec τ1) with
                    | left _ => match (Is_Unknown_dec τ2) with
                               | left _ => None
                               | right _ => Some (⋆ + ⋆)%type
                             end
                    | right _ => Some (⋆ + ⋆)%type
                  end
  | TArrow τ1 τ2 => match (Is_Unknown_dec τ1) with
                    | left _ => match (Is_Unknown_dec τ2) with
                               | left _ => None
                               | right _ => Some (TArrow ⋆ ⋆)%type
                             end
                    | right _ => Some (TArrow ⋆ ⋆)%type
                  end
  | TRec τ => match (Is_Unknown_dec τ) with
               | left _ => None
               | right _ => Some (TRec ⋆)
             end
  | TVar x => Some (TRec ⋆)
  | TUnknown => None
  end.
*)

Definition update {A : Type} (l : list A) (i : nat) (a : A) : list A :=
  alter (fun _ => a) i l.

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
  | consUseRecursion i τb τb' P P' :
      (A !! i) = Some (LogBodies τb τb' P P') -> (* we will only need rule with = Some (LogBodies ... )*)
      (* i < length A -> *)
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
