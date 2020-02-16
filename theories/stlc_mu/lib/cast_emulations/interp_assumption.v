From Autosubst Require Export Autosubst.
From fae_gtlc_mu.cast_calculus Require Export types consistency.structural.assumption.
From fae_gtlc_mu Require Import prelude.
Require Coq.Logic.JMeq.

Definition assumption_to_open_pair (a : Assumption) : (type * type) :=
  match a with
  | NoStars _ τl τr _ _ => (τl , τr)
  | StarOnLeft τr => (⋆ , τr)
  | StarOnRight τl => (τl , ⋆)
  end.

Definition assumption_to_open_initial (a : Assumption) : type := (assumption_to_open_pair a).1.

Definition assumption_to_open_final (a : Assumption) : type := (assumption_to_open_pair a).2.

(* lemma's about the trivial relation between these.. *)

Fixpoint close_up (τ : type) (Γ : list type) :=
  match Γ with
  | nil => τ
  | cons τ' Γ' => close_up τ.[τ'/] Γ'
  end.

Fixpoint close_up_list (Γ : list type) : list type :=
  match Γ with
  | nil => []
  | cons τ' Γ' => cons (close_up τ' Γ') (close_up_list Γ')
  end.

Fixpoint close_up_pair (p : type * type) (Γ : list (type * type)) :=
  match Γ with
  | nil => p
  | cons (τ1' , τ2') Γ' =>
    match p with
    | pair τ1 τ2 => close_up_pair (τ1.[τ1'/] , τ2.[τ2'/]) Γ'
    end
  end.

Fixpoint close_up_list_pairs (Γ : list (type * type)) : list (type * type) :=
  match Γ with
  | nil => nil
  | cons openτ openΓ => (close_up_pair openτ openΓ) :: (close_up_list_pairs openΓ)
  end.

Definition assumptions_to_closed_gradual_pairs (A : list Assumption) : list (type * type) :=
  (* map (fun p => (TRec p.1 , TRec p.2)) $ close_up_list (map assumption_to_open_pair A) *)
  close_up_list_pairs (map (compose (fun p => (TRec p.1 , TRec p.2)) assumption_to_open_pair) A).

Definition assumptions_to_closed_gradual_initial_types (A : list Assumption) : list type :=
  close_up_list (map (compose TRec assumption_to_open_initial) A).
  (* fmap fst (assumptions_to_closed_gradual_pairs A). *)

Definition assumptions_to_closed_gradual_final_types (A : list Assumption) : list type :=
  close_up_list (map (compose TRec assumption_to_open_final) A).
  (* fmap fst (assumptions_to_closed_gradual_pairs A). *)

From fae_gtlc_mu.stlc_mu Require Export typing lang lib.universe.
From fae_gtlc_mu.backtranslation Require Export types.

Definition closed_gradual_pair_to_type (ττ' : cast_calculus.types.type * cast_calculus.types.type) : stlc_mu.typing.type :=
  match ττ' with
  | pair τ τ' => TArrow (backtranslate_type τ) (backtranslate_type τ')
  end.

Definition assumptions_to_context (A : list Assumption) : list stlc_mu.typing.type :=
  map closed_gradual_pair_to_type (assumptions_to_closed_gradual_pairs A).

Definition the_initial_type (A : list Assumption) (τi : cast_calculus.types.type) : stlc_mu.typing.type :=
  << (close_up τi (assumptions_to_closed_gradual_initial_types A)) >>.

Definition the_final_type (A : list Assumption) (τf : cast_calculus.types.type) : stlc_mu.typing.type :=
  << (close_up τf (assumptions_to_closed_gradual_initial_types A)) >>.

(** ### rewrite lemmas ### *)

(* ### closed types ### *)

Lemma the_initial_closed_type_rewrite (A : list Assumption) (τ : cast_calculus.types.type) (P : UB 0 τ) :
  the_initial_type A τ = <<τ>>.
Admitted.

Lemma the_final_closed_type_rewrite (A : list Assumption) (τ : cast_calculus.types.type) (P : UB 0 τ) :
  the_final_type A τ = <<τ>>.
Admitted.

(* ### star types ### *)

Lemma the_initial_star_type_rewrite (A : list Assumption) :
  the_initial_type A ⋆ = Universe.
Admitted.

Lemma the_final_star_type_rewrite (A : list Assumption) :
  the_final_type A ⋆ = Universe.
Admitted.

(* ### ground types ### *)

Lemma the_initial_ground_type_rewrite (A : list Assumption) (τ : cast_calculus.types.type) (G : Ground τ) :
  the_initial_type A τ = <<τ>>.
Admitted.

Lemma the_final_ground_type_rewrite (A : list Assumption) (τ : cast_calculus.types.type) (G : Ground τ) :
  the_final_type A τ = <<τ>>.
Admitted.

(* ### sum types ### *)

Lemma the_initial_sum_type_rewrite (A : list Assumption) (τ1 τ2 : cast_calculus.types.type) :
  the_initial_type A (cast_calculus.types.TSum τ1 τ2) = stlc_mu.typing.TSum (the_initial_type A τ1) (the_initial_type A τ2).
Admitted.

Lemma the_final_sum_type_rewrite (A : list Assumption) (τ1 τ2 : cast_calculus.types.type) :
  the_final_type A (cast_calculus.types.TSum τ1 τ2) = stlc_mu.typing.TSum (the_final_type A τ1) (the_final_type A τ2).
Admitted.

(* ### arrow types ### *)

Lemma the_initial_arrow_type_rewrite (A : list Assumption) (τ1 τ2 : cast_calculus.types.type) :
  the_initial_type A (cast_calculus.types.TArrow τ1 τ2) = stlc_mu.typing.TArrow (the_initial_type A τ1) (the_initial_type A τ2).
Admitted.

Lemma the_final_arrow_type_rewrite (A : list Assumption) (τ1 τ2 : cast_calculus.types.type) :
  the_final_type A (cast_calculus.types.TArrow τ1 τ2) = stlc_mu.typing.TArrow (the_final_type A τ1) (the_final_type A τ2).
Admitted.

(* ### prod types ### *)

Lemma the_initial_prod_type_rewrite (A : list Assumption) (τ1 τ2 : cast_calculus.types.type) :
  the_initial_type A (cast_calculus.types.TProd τ1 τ2) = stlc_mu.typing.TProd (the_initial_type A τ1) (the_initial_type A τ2).
Admitted.

Lemma the_final_prod_type_rewrite (A : list Assumption) (τ1 τ2 : cast_calculus.types.type) :
  the_final_type A (cast_calculus.types.TProd τ1 τ2) = stlc_mu.typing.TProd (the_final_type A τ1) (the_final_type A τ2).
Admitted.

(*
Inductive UBAssumptions : list Assumption -> Type :=
  | empty : UBAssumptions []
  | consUnfoldedable A τ1 τ2 : UB (S (length A)) τ1 -> UB (S (length A)) τ2 -> UBAssumptions (Unfoldable τ1 τ2 :: A)
  | consUnfolded A τ1 τ2 : UB (S (length A)) τ1 -> UB (S (length A)) τ2 -> UBAssumptions (Unfolded τ1 τ2 :: A)
  | consNotUnfoldableLS A τ : UB (S (length A)) τ -> UBAssumptions (NotUnfoldableLS τ :: A)
  | consNotUnfoldableRS A τ : UB (S (length A)) τ -> UBAssumptions (NotUnfoldableRS τ :: A).
*)

(* Lemma ubass1 A x : UBAssumptions A -> UBAssumptions (update A x Unfolded). *)
(* Admitted. *)

(* Definition UBAssumption (a : Assumption) (n : nat) : Type := *)
(*   match a with *)
(*   | Unfolded => True *)
(*   | LogBodies τ1 τ2 P1 P2 => UB n τ1 * UB n τ2 *)
(*   | LogStar => True *)
(*   end. *)
