From fae_gtlc_mu.stlc_mu Require Export types typing.
From fae_gtlc_mu.cast_calculus Require Export lang.
From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import lifting.
From fae_gtlc_mu.backtranslation Require Export cast_help.general cast_help.extract cast_help.embed cast_help.props.between_rec_fix.
From fae_gtlc_mu.stlc_mu Require Export lang.
From fae_gtlc_mu.refinements.gradual_static Require Export logical_relation resources_left resources_right compat_easy compat_cast.defs.
From fae_gtlc_mu.cast_calculus Require Export consistency.structural types.

Section between_rec.
  Context `{!implG Σ,!specG Σ}.
  Notation D := (prodO cast_calculus.lang.valO stlc_mu.lang.valO -n> iPropO Σ).
  (* Implicit Types e : cast_calculus.lang.expr. *)
  Implicit Types fs : list stlc_mu.lang.val.
  (* Implicit Types f : cast_calculus.lang.val. *)
  Implicit Types A : list (cast_calculus.types.type * cast_calculus.types.type).
  (* Implicit Types a : (stlc_mu.types.type * stlc_mu.types.type). *)
  Local Hint Resolve to_of_val : core.

  Hint Extern 5 (AsVal _) => eexists; simpl; try done; eapply cast_calculus.lang.of_to_val; fast_done : typeclass_instances.

  (** Proving it *)

  Lemma back_cast_ar_trec_trec_use:
    ∀ (A : list (type * type)) (τl τr : {bind type}) (i : nat) (pμτlμtrinA : A !! i = Some (TRec τl, TRec τr)),
      back_cast_ar (consTRecTRecUseCall A τl τr i pμτlμtrinA).
  Proof.
    intros A τl τr i pμτlμtr.
    rewrite /𝓕c /𝓕 /back_cast_ar; iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    rewrite /𝓕c /𝓕. asimpl.
    (** getting the information about the length of the list *)
    iDestruct "Hfs" as "[% Hfs']".
    destruct (fs !! i) as [f | abs] eqn:Hf.
    rewrite (stlc_mu.typing.env_subst_lookup _ i f); try done.
    {
      iDestruct (big_sepL2_lookup with "Hfs'") as "#Hf". exact pμτlμtr. exact Hf.
      iApply ("Hf" $! v v' with "Hvv'"). done.
    }
    { (* trivially impossible case *)
      assert (Hi : i < length fs). rewrite -H. by eapply lookup_lt_Some.
      assert (Hi' : i >= length fs). by apply lookup_ge_None_1. exfalso. lia.
    }
  Qed.

  Lemma back_cast_ar_trec_trec_expose:
    ∀ (A : list (type * type)) (τl τr : {bind type}) (pμτlμτrnotA : (TRec τl, TRec τr) ∉ A)
      (pC : cons_struct ((TRec τl, TRec τr) :: A) τl.[TRec τl/] τr.[TRec τr/]) (IHpC : back_cast_ar pC),
      back_cast_ar (consTRecTRecExposeCall A τl τr pμτlμτrnotA pC).
  Proof.
    intros A τl τr pμτlμτrnotA pC IHpC.
    rewrite /𝓕c /𝓕 /back_cast_ar; iIntros (ei' K' v v' fs) "(#Hfs & #Hvv' & #Hei' & Hv')".
    iDestruct "Hfs" as "[% Hfs']"; iAssert (rel_cast_functions A fs) with "[Hfs']" as "Hfs". iSplit; done. rename H into Hl.
    (** setting up iLöb *)
    iLöb as "IHlob" forall (v v' ei' K') "Hvv' Hei'".
    (** ... *)
    rewrite {2}/𝓕c. rewrite /𝓕.
    fold (𝓕 pC).
    (** rewriting value relation for v and v' *)
    rewrite interp_rw_TRec.
    iDestruct "Hvv'" as (w w') "#[% Hww']".
    inversion H; clear v v' H H1 H2.
    (** implementation side *)
    wp_head.
    iApply (wp_bind [CastCtx _ _; cast_calculus.lang.FoldCtx]).
    wp_head. fold (cast_calculus.lang.of_val w). wp_value. simpl (lang.fill _ _).
    (** specification side *)
    iMod (steps_pure _ ei' K' _ _ _ (between_TRec_steps pC fs Hl pμτlμτrnotA w') with "[Hv']") as "Hv'"; auto.
    (** IH *)
    iApply (wp_bind [cast_calculus.lang.FoldCtx]).
    iApply (wp_wand with "[-]").
    iApply (IHpC ei' (FoldCtx :: K') w w' (𝓕cV (consTRecTRecExposeCall A τl τr pμτlμτrnotA pC) fs Hl :: fs)).
    iFrame "Hei' Hww' Hv'". iSplit; first by (simpl; iPureIntro; lia). iSplit; try done.
    (** iLob *)
    iModIntro. iIntros (v v') "#Hvv'".
    clear K'. iIntros (K') "Hv'". iSimpl in "Hv'".
    rewrite -𝓕c_rewrite.
    iApply ("IHlob" $! v v' with "Hv' Hvv' Hei'").
    (** ... *)
    iIntros (v) "H".
    iDestruct "H" as (v') "[Hv' #Hvv']".
    iApply wp_value.
    iExists (FoldV v').
    iFrame.
    rewrite interp_rw_TRec.
    simpl. iModIntro.
    iExists v , v'; auto.
  Qed.

End between_rec.
