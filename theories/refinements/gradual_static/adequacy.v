From iris.algebra Require Import frac agree.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import adequacy.

From fae_gtlc_mu Require Import refinements.gradual_static.logical_relation.
From fae_gtlc_mu Require Import cast_calculus.lang stlc_mu.lang.

Section adequacy.
  Context `{!inG Σ specR, !invPreG Σ}.

  Lemma adequacy
    (e : cast_calculus.lang.expr) (e' : stlc_mu.lang.expr) (τ : cast_calculus.types.type) :
    (∀ `{!implG Σ, !specG Σ}, [] ⊨ e ≤log≤ e' : τ) →
    (cast_calculus.lang.Halts e) →
    (stlc_mu.lang.Halts e').
  Proof.
    intros Hlog Hsteps.
    (** Using Iris' adequacy result for weakest preconditions to prove that e' Halts (assuming that the right WP holds) *)
    cut (adequate MaybeStuck e tt (λ _ _, ∃ v', rtc erased_step ([e'], tt) (of_val v' :: [], tt))).
    { rewrite /cast_calculus.lang.Halts in Hsteps. destruct 1. naive_solver. }
    eapply (wp_adequacy Σ); first by apply _.
    (** Actually prove that the right WP holds *)
    iIntros (Hinv ?).
    (* Allocate two halfs at e' to specify static part *)
    iMod (own_alloc ((((1/2)%Qp , to_agree e') ⋅ ((1/2)%Qp , to_agree e')) : specR)) as (spec_name) "[Hs1 Hs2]".
    { rewrite -pair_op frac_op' Qp_half_half agree_idemp.
      apply pair_valid; split; try done; try by apply frac_valid'. }
    set (SpecΣ := SpecG Σ inG0 spec_name).
    set (ImplΣ := ImplG Σ Hinv).
    (* Allocate invariant with e' using one of the halfs *)
    iMod (inv_alloc specN _ (initially_body e') with "[Hs1]") as "#Hinitially".
    { iNext. iExists e'. iSplit; eauto. }
    iExists (λ _ _, True%I), (λ _, True%I); iSplitR; first done.
    (* Proving goal by obtaining the WP in the conclusion of Hlog *)
    iApply wp_fupd. iApply (wp_wand with "[-]").
    - (* Using conclusion in Hlog *) iPoseProof (Hlog ImplΣ SpecΣ [] e' with "[]") as "Hrel".
      { iSplit; auto. iApply interp_env_nil. }
      replace e with (e.[cast_calculus.typing_lemmas.env_subst [] ]) at 2 by by asimpl.
      iApply ("Hrel" $! []). asimpl; iFrame.
    - (* Given postcondition in WP of Hlog and invariant, we continue proving the goal *)
      iModIntro. simpl. iIntros (v'). iDestruct 1 as (v2) "[Hj #Hinterp]".
      iExists v2.
      (* open invariant to get contents *)
      iInv specN as ">Hinv" "Hclose".
      (* prove that e'' must correspond to v2 *)
      iDestruct "Hinv" as (e'') "[He'' %]".
      iDestruct (own_valid_2 with "He'' Hj") as %Hvalid.
      rewrite -pair_op frac_op' Qp_half_half in Hvalid.
      move: Hvalid=> /pair_valid [_ /agree_op_inv' b]. apply leibniz_equiv in b. subst.
      (* close invariant *) iMod ("Hclose" with "[-]") as "_". iExists v2. auto.
      iIntros "!> !%". eauto.
  Qed.

End adequacy.

Definition actualΣ : gFunctors := #[ invΣ ; GFunctor specR ].

Instance subG_inG_specR {Σ} : subG (GFunctor specR) Σ → inG Σ specR.
Proof. solve_inG. Qed.
