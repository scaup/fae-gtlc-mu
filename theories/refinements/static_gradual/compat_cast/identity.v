From fae_gtlc_mu.refinements.static_gradual Require Export logical_relation resources_right compat_easy compat_cast.defs.
From fae_gtlc_mu.cast_calculus Require Export types typing.
From fae_gtlc_mu.stlc_mu Require Export lang.
From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import lifting.
From fae_gtlc_mu.backtranslation Require Export cast_help.general_def cast_help.extract cast_help.embed.
From fae_gtlc_mu.cast_calculus Require Export lang types.

Section compat_cast_identity.
  Context `{!implG Σ,!specG Σ}.
  Notation D := (prodO stlc_mu.lang.valO cast_calculus.lang.valO -n> iPropO Σ).
  (* Implicit Types e : stlc_mu.lang.expr. *)
  (* Implicit Types e : stlc_mu.lang.expr. *)
  Implicit Types fs : list stlc_mu.lang.val.
  (* Implicit Types f : stlc_mu.lang.val. *)
  Implicit Types A : list (cast_calculus.types.type * cast_calculus.types.type).
  (* Implicit Types a : (cast_calculus.types.type * cast_calculus.types.type). *)
  Local Hint Resolve to_of_val : core.
  Local Hint Resolve stlc_mu.lang.to_of_val : core.

  (** Proving it *)

  (* Lemma rewrite_subs_app (e1 e2 : expr) σ : *)
  (*   (App e1 e2).[σ] = App e1.[σ] e2.[σ]. *)
  (* Proof. *)
  (*     by simpl. *)
  (* Qed. *)


  Lemma back_cast_ar_base_base:
    ∀ A : list (type * type), back_cast_ar (atomic_Base A).
  Proof.
    intros A.
    rewrite /back_cast_ar. iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    rewrite interp_rw_TUnit.
    iDestruct "Hvv'" as "%"; inversion H. simpl in *. rewrite H0 H1. clear v v' H H0 H1.
    asimpl. wp_head.
    iMod (step_pure _ ei' K'
                    (Cast Unit TUnit TUnit)
                    Unit with "[Hv']") as "Hv'". intros. eapply IdBase. by simpl. auto.
    iSplitR. done. done. asimpl. wp_value. iExists UnitV. iSplitL. done. rewrite interp_rw_TUnit. done.
  Qed.

  Lemma back_cast_ar_star_star:
    ∀ A : list (type * type), back_cast_ar (consStarStar A).
  Proof.
    intros A.
    rewrite /back_cast_ar. iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    asimpl. wp_head.
    iMod (step_pure _ ei' K'
                    (Cast (# v') ⋆ ⋆)
                    (# v') with "[Hv']") as "Hv'". intros. eapply IdStar. by simpl. auto.
    iSplitR. done. done. asimpl. wp_value. iExists v'. iSplitL. done. done.
  Qed.

End compat_cast_identity.
