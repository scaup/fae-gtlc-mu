From fae_gtlc_mu.stlc_mu Require Export types typing.
From fae_gtlc_mu.cast_calculus Require Export lang.
From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import lifting.
From fae_gtlc_mu.backtranslation.cast_help Require Export general_def general_def_lemmas extract embed.
From fae_gtlc_mu.stlc_mu Require Export lang.
From fae_gtlc_mu.refinements.gradual_static Require Export logical_relation resources_left resources_right compat_easy compat_cast.defs.
From fae_gtlc_mu.cast_calculus Require Export types.

Section compat_cast_identity.
  Context `{!implG Σ,!specG Σ}.
  Notation D := (prodO cast_calculus.lang.valO stlc_mu.lang.valO -n> iPropO Σ).
  (* Implicit Types e : cast_calculus.lang.expr. *)
  (* Implicit Types e : cast_calculus.lang.expr. *)
  Implicit Types fs : list cast_calculus.lang.val.
  (* Implicit Types f : cast_calculus.lang.val. *)
  (* Implicit Types a : (stlc_mu.types.type * stlc_mu.types.type). *)
  Local Hint Resolve to_of_val : core.
  Local Hint Resolve cast_calculus.lang.to_of_val : core.


  Hint Extern 5 (AsVal _) => eexists; simpl; try done; eapply cast_calculus.lang.of_to_val; fast_done : typeclass_instances.

  Lemma back_cast_ar_base_base:
    ∀ A : list (type * type), back_cast_ar (atomic_Base A).
  Proof.
    intros A.
    rewrite /back_cast_ar. iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    rewrite /𝓕c /𝓕. asimpl.
    iMod ((step_lam _ ei' K') with "[Hv']") as "Hv'"; auto; simpl.
    wp_head. wp_value. iExists v'. auto.
  Qed.

  Lemma back_cast_ar_star_star:
    ∀ A : list (type * type), back_cast_ar (consStarStar A).
  Proof.
    intros A.
    rewrite /back_cast_ar. iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    rewrite /𝓕c /𝓕. asimpl.
    iMod ((step_lam _ ei' K') with "[Hv']") as "Hv'"; auto; simpl.
    wp_head. wp_value. iExists v'. auto.
  Qed.

End compat_cast_identity.
