From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From iris.base_logic Require Export invariants.
From iris.algebra Require Import auth frac agree gmap.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export gen_heap.
From fae_gtlc_mu.stlc_mu Require Export lang.
From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From fae_gtlc_mu.refinements.static_gradual Require Export logical_relation resources_right compat_easy help_left compat_cast.defs tactics_left.
From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import lifting.
From fae_gtlc_mu.backtranslation Require Export cast_help.general cast_help.extract cast_help.embed.
From fae_gtlc_mu.cast_calculus Require Export types.

Ltac reshape_expr e tac :=
  let rec go K e :=
      match e with
      | App ?e1 (of_val ?v2) => go (AppLCtx v2 :: K) e1
      | App ?e1 ?e2 => go (AppRCtx e1 :: K) e2
      | Pair (of_val ?v1) ?e2 => go (PairRCtx v1 :: K) e2
      | Pair ?e1 ?e2 => go (PairLCtx e2 :: K) e1
      | Fst ?e => go (FstCtx :: K) e
      | Snd ?e => go (SndCtx :: K) e
      | InjL ?e => go (InjL :: K) e
      | InjR ?e => go (InjR :: K) e
      | Case ?e0 ?e1 ?e2 => tac K e
      | Fold ?e => tac K e
      | Unfold ?e => tac K e
      | Var ?x => tac K e
      | Lam ?e => tac K e
      | Unit => tac K e
      end
      in go [] e.

Import uPred.

Section extract_embed.
  Context `{!implG Σ,!specG Σ}.
  Notation D := (prodO stlc_mu.lang.valO cast_calculus.lang.valO -n> iPropO Σ).
  (* Implicit Types e : stlc_mu.lang.expr. *)
  (* Implicit Types e : stlc_mu.lang.expr. *)
  Implicit Types fs : list stlc_mu.lang.val.
  (* Implicit Types f : stlc_mu.lang.val. *)
  Implicit Types A : list (cast_calculus.types.type * cast_calculus.types.type).
  (* Implicit Types a : (cast_calculus.types.type * cast_calculus.types.type). *)
  Local Hint Resolve to_of_val : core.

  Lemma tac_wp_expr_eval `{!implG Σ} Δ s E Φ e e' :
    (∀ (e'':=e'), e = e'') →
    envs_entails Δ (WP e' @ s; E {{ Φ }}) → envs_entails Δ (WP e @ s; E {{ Φ }}).
  Proof. by intros ->. Qed.

Tactic Notation "wp_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    eapply tac_wp_expr_eval;
      [let x := fresh in intros x; t; unfold x; reflexivity|]
  | _ => fail "wp_expr_eval: not a 'wp'"
  end.

Lemma tac_wp_pure `{!implG Σ} Δ Δ' s E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  MaybeIntoLaterNEnvs n Δ Δ' →
  envs_entails Δ' (WP e2 @ s; E {{ Φ }}) →
  envs_entails Δ (WP e1 @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ??? HΔ'. rewrite into_laterN_env_sound /=.
  rewrite HΔ' -lifting.wp_pure_step_later //.
Qed.

Lemma tac_wp_value `{!implG Σ} Δ s E Φ v :
  envs_entails Δ (Φ v) → envs_entails Δ (WP (stlc_mu.lang.of_val v) @ s; E {{ Φ }}).
Proof. rewrite envs_entails_eq=> ->. by apply wp_value. Qed.

Ltac wp_expr_simpl := wp_expr_eval simpl.

Ltac wp_value_head :=
  first [eapply tac_wp_value].

Ltac wp_finish :=
  wp_expr_simpl;      (* simplify occurences of subst/fill *)
  try wp_value_head;  (* in case we have reached a value, get rid of the WP *)
  pm_prettify.        (* prettify ▷s caused by [MaybeIntoLaterNEnvs] and
                         λs caused by wp_value *)

Ltac solve_vals_compare_safe :=
  (* The first branch is for when we have [vals_compare_safe] in the context.
     The other two branches are for when either one of the branches reduces to
     [True] or we have it in the context. *)
  fast_done || (left; fast_done) || (right; fast_done).

(** The argument [efoc] can be used to specify the construct that should be
reduced. For example, you can write [wp_pure (EIf _ _ _)], which will search
for an [EIf _ _ _] in the expression, and reduce it.

The use of [open_constr] in this tactic is essential. It will convert all holes
(i.e. [_]s) into evars, that later get unified when an occurences is found
(see [unify e' efoc] in the code below). *)
Tactic Notation "wp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' efoc;
      eapply (tac_wp_pure _ _ _ _ (fill K e'));
      [iSolveTC                       (* PureExec *)
      |try solve_vals_compare_safe    (* The pure condition for PureExec -- handles trivial goals, including [vals_compare_safe] *)
      |iSolveTC                       (* IntoLaters *)
      |wp_finish                      (* new goal *)
      ])
    || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | _ => fail "wp_pure: not a 'wp'"
  end.

(* TODO: do this in one go, without [repeat]. *)
Ltac wp_pures :=
  iStartProof;
  repeat (wp_pure _; []). (* The `;[]` makes sure that no side-condition
                             magically spawns. *)

(** Unlike [wp_pures], the tactics [wp_rec] and [wp_lam] should also reduce
lambdas/recs that are hidden behind a definition, i.e. they should use
[AsRecV_recv] as a proper instance instead of a [Hint Extern].

We achieve this by putting [AsRecV_recv] in the current environment so that it
can be used as an instance by the typeclass resolution system. We then perform
the reduction, and finally we clear this new hypothesis. *)
(** WARNING: THE LEMMA'S IN THIS FILE ARE OBSCENELY BORING!!! *)


 Lemma wp_Ω Φ : ⊢ (True -∗ (WP Ω {{ Φ }}))%I.
 Proof.
   iIntros.
   iLöb as "IH".
   iApply wp_pure_step_later; auto; iNext; asimpl.
   iApply (wp_bind $ stlc_mu.lang.fill_item $ stlc_mu.lang.AppLCtx _).
   iApply wp_pure_step_later; auto.
   iNext.
   iApply wp_value.
   fold Ω. done.
 Qed.

(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)

 Lemma wp_extract_TUnit_embed_TProd v1 v2 Φ :
   ⊢ (True -∗ WP (extract TUnit Ground_TUnit (embedV_Ground_TProd (stlc_mu.lang.PairV v1 v2))) {{ Φ }}).
 Proof.
   iIntros.
   wp_head.
   asimpl.
   iApply (wp_bind $ fill [ CaseCtx _ _ ]).
   wp_head.
   wp_value.
   simpl.
   wp_head.
   asimpl.
   wp_head. asimpl.
   wp_head. asimpl.
   wp_head. asimpl.
   iApply (wp_bind $ fill [ AppLCtx _ ]).
   wp_head. wp_value.
   simpl.
   wp_head.
   asimpl.
   iApply (wp_bind $ fill [ AppLCtx _ ]).
   wp_head.
   wp_value.
   simpl.
   wp_head.
   asimpl.
 Admitted.



End extract_embed.
