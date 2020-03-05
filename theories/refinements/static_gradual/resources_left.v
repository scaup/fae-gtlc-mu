From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From iris.base_logic Require Export invariants.
From iris.algebra Require Import auth frac agree gmap.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export gen_heap.
From fae_gtlc_mu.stlc_mu Require Export lang.
Import uPred.

Class heapG Σ := HeapG {
  heapG_invG : invG Σ;
  heapG_gen_heapG :> gen_heapG unit unit Σ
}.

Instance heapG_irisG `{heapG Σ} : irisG lang Σ := {
  iris_invG := heapG_invG;
  state_interp σ κs _ := True%I;
  fork_post _ := True%I;
}.
Global Opaque iris_invG.

(** Override the notations so that scopes and coercions work out *)
(* Notation "l ↦{ q } v" := (mapsto (L:=loc) (V:=val) l q v%V) *)
(*   (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope. *)
(* Notation "l ↦ v" := *)
(*   (mapsto (L:=loc) (V:=val) l 1 v%V) (at level 20) : bi_scope. *)
(* Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I *)
(*   (at level 20, q at level 50, format "l  ↦{ q }  -") : bi_scope. *)
(* Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : bi_scope. *)

Section lang_rules.
  Context `{heapG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  (* Implicit Types σ : state. *)
  Implicit Types e : expr.

  (** The tactic [inv_head_step] performs inversion on hypotheses of the shape
      [head_step]. The tactic will discharge head-reductions starting from values, and
      simplifies hypothesis related to conversions from and to values, and finite map
      operations. This tactic is slightly ad-hoc and tuned for proving our lifting
      lemmas. *)
  Ltac inv_head_step :=
    repeat match goal with
    | _ => progress simplify_map_eq/= (* simplify memory stuff *)
    | H : to_val _ = Some _ |- _ => apply of_to_val in H
    | H : head_step ?e _ _ _ _ _ |- _ =>
       try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
       and can thus better be avoided. *)
       inversion H; subst; clear H
    end.

  Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _, _; simpl : core.

  Local Hint Constructors head_step : core.
  (* Local Hint Resolve alloc_fresh : core. *)
  Local Hint Resolve to_of_val : core.

  (** Base axioms for core primitives of the language: Stateful reductions. *)
  (* Lemma wp_alloc E e v: *)
  (*   IntoVal e v → *)
  (*   {{{ True }}} Alloc e @ E {{{ l, RET (LocV l); l ↦ v }}}. *)
  (* Proof. *)
  (*   iIntros (<- Φ) "_ HΦ". *)
  (*   iApply wp_lift_atomic_head_step_no_fork; auto. *)
  (*   iIntros (σ1 ???) "Hσ !>"; iSplit; first by auto. *)
  (*   iNext; iIntros (v2 σ2 efs Hstep); inv_head_step. *)
  (*   iMod (@gen_heap_alloc with "Hσ") as "(Hσ & Hl & _)"; first done. *)
  (*   iModIntro; iSplit=> //. iFrame. by iApply "HΦ". *)
  (* Qed. *)

  (* Lemma wp_load E l q v : *)
  (* {{{ ▷ l ↦{q} v }}} Load (Loc l) @ E {{{ RET v; l ↦{q} v }}}. *)
  (* Proof. *)
  (*   iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto. *)
  (*   iIntros (σ1 ???) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?. *)
  (*   iSplit; first by eauto. *)
  (*   iNext; iIntros (v2 σ2 efs Hstep); inv_head_step. *)
  (*   iModIntro; iSplit=> //. iFrame. by iApply "HΦ". *)
  (* Qed. *)

  (* Lemma wp_store E l v' e v : *)
  (*   to_val e = Some v → *)
  (*   {{{ ▷ l ↦ v' }}} Store (Loc l) e @ E *)
  (*   {{{ RET UnitV; l ↦ v }}}. *)
  (* Proof. *)
  (*   iIntros (<-%of_to_val Φ) ">Hl HΦ". *)
  (*   iApply wp_lift_atomic_head_step_no_fork; auto. *)
  (*   iIntros (σ1 ???) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?. *)
  (*   iSplit; first by eauto. iNext; iIntros (v2 σ2 efs Hstep); inv_head_step. *)
  (*   iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]". *)
  (*   iModIntro. iSplit=>//. by iApply "HΦ". *)
  (* Qed. *)

  Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
  Local Ltac solve_exec_puredet := simpl; intros; by inv_head_step.
  Local Ltac solve_pure_exec :=
    unfold IntoVal in *;
    repeat match goal with H : AsVal _ |- _ => destruct H as [??] end; subst;
    intros ?; apply nsteps_once, pure_head_step_pure_step;
      constructor; [solve_exec_safe | solve_exec_puredet].

  Global Instance pure_lam e1 e2 `{!AsVal e2} :
    PureExec True 1 (App (Lam e1) e2) e1.[e2 /].
  Proof. solve_pure_exec. Qed.

  (* Global Instance pure_tlam e : PureExec True 1 (TApp (TLam e)) e. *)
  (* Proof. solve_pure_exec. Qed. *)

  Global Instance pure_fold e `{!AsVal e}:
    PureExec True 1 (Unfold (Fold e)) e.
  Proof. solve_pure_exec. Qed.

  Global Instance pure_fst e1 e2 `{!AsVal e1, !AsVal e2} :
    PureExec True 1 (Fst (Pair e1 e2)) e1.
  Proof. solve_pure_exec. Qed.

  Global Instance pure_snd e1 e2 `{!AsVal e1, !AsVal e2} :
    PureExec True 1 (Snd (Pair e1 e2)) e2.
  Proof. solve_pure_exec. Qed.

  Global Instance pure_case_inl e0 e1 e2 `{!AsVal e0}:
    PureExec True 1 (Case (InjL e0) e1 e2) e1.[e0/].
  Proof. solve_pure_exec. Qed.

  Global Instance pure_case_inr e0 e1 e2 `{!AsVal e0}:
    PureExec True 1 (Case (InjR e0) e1 e2) e2.[e0/].
  Proof. solve_pure_exec. Qed.



End lang_rules.
