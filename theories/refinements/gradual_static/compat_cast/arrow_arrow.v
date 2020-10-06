From fae_gtlc_mu.stlc_mu Require Export types typing.
From fae_gtlc_mu.cast_calculus Require Export lang.
From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import lifting.
From fae_gtlc_mu.backtranslation Require Export cast_help.general_def_lemmas cast_help.extract cast_help.embed.
From fae_gtlc_mu.stlc_mu Require Export lang.
From fae_gtlc_mu.refinements.gradual_static Require Export logical_relation resources_left resources_right compat_easy compat_cast.defs.
From fae_gtlc_mu.cast_calculus Require Export types.

Section compat_cast_arrow_arrow.
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
  Hint Extern 5 (AsVal _) => eexists; simpl; try done; eapply cast_calculus.lang.of_to_val; fast_done : typeclass_instances.

  Lemma back_cast_ar_arrow_arrow:
    ∀ (A : list (type * type)) (τ1 τ1' τ2 τ2' : type) (pC1 : alternative_consistency A τ1' τ1) (pC2 : alternative_consistency A τ2 τ2')
      (IHpC1 : back_cast_ar pC1) (IHpC2 : back_cast_ar pC2),
      back_cast_ar (throughArrow A τ1 τ1' τ2 τ2' pC1 pC2).
  Proof.
    intros A τ1 τ1' τ2 τ2' pC1 pC2 IHpC1 IHpC2.
    rewrite /back_cast_ar. iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    iDestruct "Hfs" as "[% Hfs']"; iAssert (rel_cast_functions A fs) with "[Hfs']" as "Hfs". iSplit; done. iClear "Hfs'".
    rewrite /𝓕c /𝓕. fold (𝓕 pC1) (𝓕 pC2). rewrite between_TArrow_subst_rewrite.
    rename v into f. rename v' into f'. iDestruct "Hv'" as "Hf'". iDestruct "Hvv'" as "Hff'".
    fold (𝓕c pC1 fs) (𝓕c pC2 fs).
    unfold between_TArrow.
    iMod ((step_lam _ ei' K') with "[Hf']") as "Hf'"; auto. asimpl.
    iApply wp_value.
    iExists (LamV _). iFrame "Hf'".
    do 2 rewrite interp_rw_TArrow. simpl.
    iModIntro.
    (** actual thing to prove *)
    (** ===================== *)
    iIntros ((a , a')) "#Haa'". simpl. clear K'.
    iIntros (K') "Hf'".
    simpl in *.
    (** implementation *)
    wp_head.
    (** specification *)
    iMod ((step_lam _ ei' K') with "[Hf']") as "Hf'"; auto. asimpl.
    (** IH for arguments *)
    iApply (wp_bind [cast_calculus.lang.AppRCtx f ; cast_calculus.lang.CastCtx _ _]).
    rewrite 𝓕c_rewrite.
    iApply (wp_wand with "[Hf']").
    iApply (IHpC1 ei' (AppRCtx f' :: AppRCtx _ :: K')); auto.
    (** ... *)
    iIntros (b) "HHH".
    iDestruct "HHH" as (b') "[Hb' #Hbb']". simpl.
    (** use relatedness of functions *)
    iApply (wp_bind [CastCtx _ _]).
    iApply (wp_wand with "[Hb']").
    iDestruct ("Hff'" with "Hbb'") as "Hfbf'b'/=".
    iApply ("Hfbf'b'" $! (AppRCtx _ :: K')). iFrame "Hb'".
    (** ... *)
    iIntros (r) "HHH". iDestruct "HHH" as (r') "[Hr' Hrr']". simpl.
    iApply (wp_wand with "[-]").
    rewrite -𝓕c_rewrite.
    (** second IH for the results *)
    iApply (IHpC2 ei' K' r r' with "[-]"). auto.
    (** ... *)
    iIntros; auto.
  Qed.

End compat_cast_arrow_arrow.
