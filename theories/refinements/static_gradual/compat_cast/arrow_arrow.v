From fae_gtlc_mu.refinements.static_gradual Require Export logical_relation resources_right compat_easy help_left compat_cast.defs.
From fae_gtlc_mu.cast_calculus Require Export types typing.
From fae_gtlc_mu.stlc_mu Require Export lang.
From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import lifting.
From fae_gtlc_mu.cast_calculus Require Export consistency.structural.
From fae_gtlc_mu.backtranslation Require Export cast_help.general cast_help.extract cast_help.embed.
From fae_gtlc_mu.cast_calculus Require Export lang types.

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

  Lemma back_cast_ar_arrow_arrow:
    ∀ (A : list (type * type)) (τ1 τ1' τ2 τ2' : type) (pC1 : cons_struct A τ1' τ1) (pC2 : cons_struct A τ2 τ2')
      (IHpC1 : back_cast_ar pC1) (IHpC2 : back_cast_ar pC2),
      back_cast_ar (consTArrowTArrow A τ1 τ1' τ2 τ2' pC1 pC2).
  Proof.
    intros A τ1 τ1' τ2 τ2' pC1 pC2 IHpC1 IHpC2.
    rewrite /back_cast_ar. iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    fold interp.
    iDestruct "Hfs" as "[% Hfs']"; iAssert (rel_cast_functions A fs) with "[Hfs']" as "Hfs". iSplit; done. iClear "Hfs'".
    rewrite /𝓕c /𝓕. fold (𝓕 pC1) (𝓕 pC2). rewrite between_TArrow_subst_rewrite.
    rename v into f. rename v' into f'. iDestruct "Hv'" as "Hf'". iDestruct "Hvv'" as "Hff'".
    (* iClear "Hvv'". *)
    fold (𝓕c pC1 fs) (𝓕c pC2 fs).
    iDestruct "Hfs" as "[% Hfs']"; iAssert (rel_cast_functions A fs) with "[Hfs']" as "Hfs". iSplit; done. iClear "Hfs'".
    do 2 rewrite 𝓕c_rewrite.
    unfold between_TArrow.
    wp_head.
    asimpl.
    iApply wp_value.
    iExists (CastV f' (TArrow τ1 τ2) (TArrow τ1' τ2') (TArrow_TArrow_icp τ1 τ2 τ1' τ2')).
    rewrite interp_rw_TArrow.
    iSplitL "Hf'"; auto.
    rewrite interp_rw_TArrow.
    iModIntro.
    (** actual thing to prove *)
    (** ===================== *)
    iIntros ((a , a')) "#Haa'".
    simpl. clear K'.
    iIntros (K') "Hf'".
    simpl in *.
    (** implementation *)
    wp_head. asimpl.
    (** specification *)
    iMod (step_pure _ ei' K'
                    (App (Cast (# f') (TArrow τ1 τ2) (TArrow τ1' τ2')) (# a'))
                    (Cast (App (# f') (Cast (# a') τ1' τ1)) τ2 τ2') with "[Hf']") as "Hf'".
    intros. eapply AppCast; try by rewrite -to_of_val. auto. by iFrame.
    (** first IH for the arguments *)
    iApply (wp_bind (fill $ [stlc_mu.lang.AppRCtx _ ; stlc_mu.lang.AppRCtx _])).
    iApply (wp_wand with "[-]").
    rewrite -𝓕c_rewrite.
    iApply (IHpC1 ei' (AppRCtx f' :: CastCtx τ2 τ2' :: K') with "[Hf']").
    (* iApply (IHpC1 ei' (CastCtx τ2 τ4 :: AppRCtx f' :: K') with "[Hf']"). *)
    iSplitR. done.
    iSplitR. done.
    iSplitR. done.
    simpl. done.
    iIntros (b) "HHH".
    iDestruct "HHH" as (b') "[Hb' #Hbb']".
    simpl.
    iClear "Haa'". clear a a'.
    (** using the relatedness of functions *)
    iApply (wp_bind (fill $ [stlc_mu.lang.AppRCtx _ ])).
    iApply (wp_wand with "[-]").
    iDestruct ("Hff'" with "Hbb'") as "Hfbf'b' /=".
    iApply ("Hfbf'b'" $! (CastCtx τ2 τ2' :: K')).
    simpl.
    iExact "Hb'".
    iIntros (r) "HHH". iDestruct "HHH" as (r') "[Hr' Hrr']".
    simpl.
    iClear "Hbb'". clear b b'.
    (** second IH for the results *)
    iApply (wp_wand with "[-]").
    rewrite -𝓕c_rewrite.
    iApply (IHpC2 ei' K' r r' with "[-]").
    iSplitR. done.
    iSplitL "Hrr'"; try done.
    iSplitR. done.
    done.
    iIntros (s) "HHH". done.
    Unshelve. all:apply hack.
  Qed.


End compat_cast_arrow_arrow.
