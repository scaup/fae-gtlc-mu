From Autosubst Require Export Autosubst.
(* Require Export Utf8_core. *)
From iris.algebra Require Export base.
(* Require Coq.Program.Wf. *)
Require Import Relation_Operators.
Require Import Transitive_Closure.
From Coq.Wellfounded Require Import Lexicographic_Product Union.
(* From Coq.Program Require Import Wf. *)

From fae_gtlc_mu.equivalence Require Export types.

(* structurally smaller relation *)
Inductive ss : type -> type -> Prop :=
  | ss_arrow_l τ1 τ2 : ss τ1 (TArrow τ1 τ2)
  | ss_arrow_r τ1 τ2 : ss τ2 (TArrow τ1 τ2)
  | ss_rec_r τ : ss τ (TRec τ).

Lemma ss_wf : wf ss.
Proof.
  intro τ. induction τ; constructor; intros τ' pss; inversion pss; by simplify_eq.
Qed.

Inductive ord : relation (type * type) :=
| left_sym :
    forall x x':type, ss x x' -> forall y:type, ord (x, y) (x', y)
| right_sym :
    forall y y':type, ss y y' -> forall x:type, ord (x, y) (x, y')
| contra_middle :
  forall x x':type, ss x x' → forall y:type, ord (x , y) (y , x')
| contra_outward : (* hmm *)
  forall y y':type, ss y y' → forall x:type, ord (x , y) (y' , x).

Lemma Acc_ord :
  forall x:type, Acc ss x -> forall y:type, Acc ss y -> Acc ord (x, y) ∧ Acc ord (y , x).
Proof.
  induction 1 as [x _ IHAcc]. intros y H2.
  induction H2 as [x1 H3 IHAcc1].
  split.
  - apply Acc_intro. intros y H5. inversion_clear H5; clear y; try (by apply IHAcc1).
    + apply (IHAcc x0). done. apply ss_wf.
    + apply (IHAcc y0). done. apply ss_wf.
  - apply Acc_intro. intros y H5. inversion_clear H5; clear y; try (by apply IHAcc1).
    + apply IHAcc. done. apply ss_wf.
    + apply (IHAcc x0). done. apply ss_wf.
Qed.

(** why isn't the sum of type sizes sufficient???; we could just used lia...
    check this... *)

Lemma wf_ord :
  well_founded ord.
Proof.
  red. destruct a.
  apply Acc_ord; apply ss_wf.
Qed.

Definition lexord : relation (@sigT nat (fun _ => (prod type type))) :=
  clos_trans _ (lexprod _ _ lt (fun _ => ord)).

Lemma lexord_wf : wf lexord.
Proof.
  apply wf_clos_trans. apply wf_lexprod.
  apply lt_wf. intros _. apply wf_ord.
Qed.

(** lemma to facilitate upper_bound to be le *)
