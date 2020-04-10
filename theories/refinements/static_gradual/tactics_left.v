From fae_gtlc_mu.stlc_mu Require Export lang.
(* From iris.heap_lang Require Export lang. *)
(* Set Default Proof Using "Type". *)
(* Import heap_lang. *)

(* Ltac reshape_expr e tac := *)
(*   let rec go K e := *)
(*       match e with *)
(*       | _ => tac K e *)
(*       (* | Var x => *) *)
(*       (* | Lam e =>  *) *)
(*       | App (of_val ?v1) ?e2 => go (AppRCtx v1 :: K) e2 *)
(*       | App ?e1 ?e2 => match (to_val e1) with *)
(*       (* | App ?e1 ?e2 => match (to_val e1) with *) *)
(*                       (* | Some v1 => go (AppRCtx (LamV e1) :: K) e2 *) *)
(*                       (* | None => go (AppLCtx e1 :: K) e2 *) *)
(*                       (* end *) *)
(*       (* | Unit => *) *)
(*       | Pair (of_val ?v1) ?e2 => go (PairRCtx v1 :: K) e2 *)
(*       (* | Pair ?e1 ?e2 => match (to_val e1) with *) *)
(*                        (* | Some ?v1 => go (PairRCtx v1 :: K) e2 *) *)
(*                        (* | None => go (PairLCtx e1 :: K) e2 *) *)
(*                        (* end *) *)
(*       | Fst ?e => go (FstCtx :: K) e *)
(*       | Snd ?e => go (SndCtx :: K) e *)
(*       | InjL ?e => go (InjLCtx :: K) e *)
(*       | InjR ?e => go (InjRCtx :: K) e *)
(*       | Case ?e0 ?e1 ?e2 => go (CaseCtx e1 e2 :: K) e0 *)
(*       | Fold ?f => go (FoldCtx :: K) f *)
(*       | Unfold ?f => go (UnfoldCtx :: K) f *)
(*       end *)
(*   in *)
(*   go (@nil ectx_item) e. *)

From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Import atomic.
Set Default Proof Using "Type".
Import uPred.

(* From fae_gtlc_mu.cast_calculus Require Export types typing. *)
(* From fae_gtlc_mu.cast_calculus Require Export lang. *)
(* From fae_gtlc_mu.cast_calculus Require Export lang. *)
(* From iris.algebra Require Import list. *)
(* From iris.proofmode Require Import tactics. *)
From iris.program_logic Require Import lifting.
From fae_gtlc_mu.refinements.static_gradual Require Export resources_left.
From fae_gtlc_mu.backtranslation.cast_help Require Export extract embed.


Ltac fetch_eval e tac :=
  let rec go K e :=
      match e with
      (* | Var x => *)
      (* | Lam e =>  *)
      | App (of_val ?v1) ?e2 => go (AppRCtx v1 :: K) e2
      | App ?e1 ?e2 => go (AppLCtx e1 :: K) e2
      (* | Unit => *)
      | Pair (of_val ?v1) ?e2 => go (PairRCtx v1 :: K) e2
      | Pair ?e1 ?e2 => go (PairLCtx e1 :: K) e2
      | Fst ?e => go (FstCtx :: K) e
      | Snd ?e => go (SndCtx :: K) e
      | InjL ?e => go (InjLCtx :: K) e
      | InjR ?e => go (InjRCtx :: K) e
      | Case ?e0 ?e1 ?e2 => fail "testing"
      (* | Case ?e0 ?e1 ?e2 => go (CaseCtx e1 e2 :: K) e0 *)
      | Fold e => go (FoldCtx :: K) e
      | Unfold e => go (UnfoldCtx :: K) e
      | _ => tac K e
      end
  in
  go (@nil ectx_item) e.




Ltac wp_step :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    let e := eval simpl in e in
        fetch_eval e ltac:(fun K e' =>
                              iApply (wp_bind (fill K))
                          (* [iSolveTC                       (* PureExec *) *)
                          (* |iSolveTC                       (* IntoLaters *) *)
                          )
        || fail "wp_pure: cannot finot a redex"
  | _ => fail "wp_pure: not a 'wp'"
  end.





Ltac wp_head := iApply wp_pure_step_later; auto; iNext.
Ltac wp_value := iApply wp_value.

(** We are working with deterministic programs; we should have a tactic wp_step *)




Lemma tac_wp_expr_eval `{!implG Σ} Δ s E Φ e e' :
  (∀ (e'':=e'), e = e'') →
  envs_entails Δ (WP e' @ s; E {{ Φ }}) → envs_entails Δ (WP e @ s; E {{ Φ }}).
Proof. by intros ->. Qed.
(* Lemma tac_twp_expr_eval `{!implG Σ} Δ s E Φ e e' : *)
(*   (∀ (e'':=e'), e = e'') → *)
(*   envs_entails Δ (WP e' @ s; E [{ Φ }]) → envs_entails Δ (WP e @ s; E [{ Φ }]). *)
(* Proof. by intros ->. Qed. *)

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
  envs_entails Δ (Φ v) → envs_entails Δ (WP (of_val v) @ s; E {{ Φ }}).
Proof. rewrite envs_entails_eq=> ->. by apply wp_value. Qed.
(* Lemma tac_twp_value `{!implG Σ} Δ s E Φ v : *)
(*   envs_entails Δ (Φ v) → envs_entails Δ (WP (Val v) @ s; E [{ Φ }]). *)
(* Proof. rewrite envs_entails_eq=> ->. by apply twp_value. Qed. *)

Ltac wp_expr_simpl := wp_expr_eval simpl.

Ltac wp_value_head :=
  first [apply tac_wp_value].

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

(* Tactic Notation "wp_pure" open_constr(efoc) := *)
(*   iStartProof; *)
(*   lazymatch goal with *)
(*   | |- envs_entails _ (wp ?s ?E ?e ?Q) => *)
(*     let e := eval simpl in e in *)
(*         reshape_expr e ltac:(fun K e' => *)
(*                                unify e' efoc; *)
(*                                eapply (tac_wp_pure _ _ _ _ (fill K e')); *)
(*                                [iSolveTC                       (* PureExec *) *)
(*                                |try solve_vals_compare_safe    (* The pure condition for PureExec -- handles trivial goals, including [vals_compare_safe] *) *)
(*                                |iSolveTC                       (* IntoLaters *) *)
(*                                |wp_finish                      (* new goal *) *)
(*                             ]) *)
(*         || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex" *)
(*   | _ => fail "wp_pure: not a 'wp'" *)
(*   end. *)

(* TODO: do this in one go, without [repeat]. *)
(* Ltac wp_pures := *)
(*   iStartProof; *)
(*   repeat (wp_pure _; []). (* The `;[]` makes sure that no side-condition *)
(*                              magically spawns. *) *)

(** Unlike [wp_pures], the tactics [wp_rec] and [wp_lam] should also reduce
lambdas/recs that are hidden behind a definition, i.e. they should use
[AsRecV_recv] as a proper instance instead of a [Hint Extern].

We achieve this by putting [AsRecV_recv] in the current environment so that it
can be used as an instance by the typeclass resolution system. We then perform
the reduction, and finally we clear this new hypothesis. *)
(* Tactic Notation "wp_rec" := *)
(*   let H := fresh in *)
(*   assert (H := AsRecV_recv); *)
(*   wp_pure (App _ _); *)
(*   clear H. *)

(* Tactic Notation "wp_if" := wp_pure (If _ _ _). *)
(* Tactic Notation "wp_if_true" := wp_pure (If (LitV (LitBool true)) _ _). *)
(* Tactic Notation "wp_if_false" := wp_pure (If (LitV (LitBool false)) _ _). *)
(* Tactic Notation "wp_unop" := wp_pure (UnOp _ _). *)
(* Tactic Notation "wp_binop" := wp_pure (BinOp _ _ _). *)
(* Tactic Notation "wp_op" := wp_unop || wp_binop. *)
(* Tactic Notation "wp_lam" := wp_rec. *)
(* Tactic Notation "wp_let" := wp_pure (Rec BAnon (BNamed _) _); wp_lam. *)
(* Tactic Notation "wp_seq" := wp_pure (Rec BAnon BAnon _); wp_lam. *)
(* Tactic Notation "wp_proj" := wp_pure (Fst _) || wp_pure (Snd _). *)
(* Tactic Notation "wp_case" := wp_pure (Case _ _ _). *)
(* Tactic Notation "wp_match" := wp_case; wp_pure (Rec _ _ _); wp_lam. *)
(* Tactic Notation "wp_inj" := wp_pure (InjL _) || wp_pure (InjR _). *)
(* Tactic Notation "wp_pair" := wp_pure (Pair _ _). *)
(* Tactic Notation "wp_closure" := wp_pure (Rec _ _ _). *)

(* Lemma tac_wp_bind `{!implG Σ} K Δ s E Φ e f : *)
(*   f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *) *)
(*   envs_entails Δ (WP e @ s; E {{ v, WP f (Val v) @ s; E {{ Φ }} }})%I → *)
(*   envs_entails Δ (WP fill K e @ s; E {{ Φ }}). *)
(* Proof. rewrite envs_entails_eq=> -> ->. by apply: wp_bind. Qed. *)
(* Lemma tac_twp_bind `{!implG Σ} K Δ s E Φ e f : *)
(*   f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *) *)
(*   envs_entails Δ (WP e @ s; E [{ v, WP f (Val v) @ s; E [{ Φ }] }])%I → *)
(*   envs_entails Δ (WP fill K e @ s; E [{ Φ }]). *)
(* Proof. rewrite envs_entails_eq=> -> ->. by apply: twp_bind. Qed. *)

(* Ltac wp_bind_core K := *)
(*   lazymatch eval hnf in K with *)
(*   | [] => idtac *)
(*   | _ => eapply (tac_wp_bind K); [simpl; reflexivity|reduction.pm_prettify] *)
(*   end. *)
(* Ltac twp_bind_core K := *)
(*   lazymatch eval hnf in K with *)
(*   | [] => idtac *)
(*   | _ => eapply (tac_twp_bind K); [simpl; reflexivity|reduction.pm_prettify] *)
(*   end. *)

(* Tactic Notation "wp_bind" open_constr(efoc) := *)
(*   iStartProof; *)
(*   lazymatch goal with *)
(*   | |- envs_entails _ (wp ?s ?E ?e ?Q) => *)
(*     reshape_expr e ltac:(fun K e' => unify e' efoc; wp_bind_core K) *)
(*     || fail "wp_bind: cannot find" efoc "in" e *)
(*   | |- envs_entails _ (twp ?s ?E ?e ?Q) => *)
(*     reshape_expr e ltac:(fun K e' => unify e' efoc; twp_bind_core K) *)
(*     || fail "wp_bind: cannot find" efoc "in" e *)
(*   | _ => fail "wp_bind: not a 'wp'" *)
(*   end. *)

(* Section compat_cast_all. *)
(*   Context `{!implG Σ}. *)



(*   Lemma wp_extract_TUnit_embed_TProd v1 v2 Φ : *)
(*     (True -∗ WP (extract_TUnit (embedV_Ground_TProd (stlc_mu.lang.PairV v1 v2))) {{ Φ }})%I. *)
(*   Proof. *)
(*     iIntros (_). *)
(*     rewrite /extract_TUnit /embedV_Ground_TProd. *)
(*     wp_pure _. *)
(*     wp_pure _. *)
(*     wp_pure _. *)
(*     wp_pure _. *)
(*     wp_pure _. *)
(*     wp_pure _. *)
(*     wp_pure (Unfold (Fold _)). *)
(*     wp_pure (Case _ _ _). *)
(*     wp_pure (Case _ _ _). *)
(*     wp_pure (Case _ _ _). *)

(*     wp_step. wp_value. simpl. *)
(*     wp_step. wp_value. simpl. *)
(*     wp_step. wp_value. simpl. *)



(*  Lemma wp_fix'' (f : stlc_mu.lang.expr) Φ : *)



(*    (▷ ▷ WP f (stlc_mu.lang.Lam (rename (+1) (Fix'' f) (stlc_mu.lang.Var 0)))   {{ Φ }} -∗ (WP (Fix'' f) {{ Φ }}))%I. *)





