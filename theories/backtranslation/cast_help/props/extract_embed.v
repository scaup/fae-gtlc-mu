From fae_gtlc_mu.stlc_mu Require Export lang.
From fae_gtlc_mu.backtranslation.cast_help Require Export extract embed.

(* from resourcers_left {{{ *)

(* From fae_gtlc_mu.refinements.static_gradual Require Export resources_left. *)

Ltac inv_head_step :=
  repeat match goal with
  (* | _ => progress simplify_map_eq/= (* simplify memory stuff *) *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : head_step ?e _ _ _ _ _ |- _ =>
      try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
      and can thus better be avoided. *)
      inversion H; subst; clear H
  end.

Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
Local Ltac solve_exec_puredet := simpl; intros; by inv_head_step.
Local Ltac solve_pure_exec :=
  unfold IntoVal in *;
  repeat match goal with H : AsVal _ |- _ => destruct H as [??] end; subst;
  intros ?; apply nsteps_once, pure_head_step_pure_step;
    constructor; [solve_exec_safe | solve_exec_puredet].

(* }}} *)

Ltac ps_head_step := apply pure_head_step_pure_step;
    constructor; [solve_exec_safe | solve_exec_puredet]; try (by rewrite /= to_of_val /=).

Ltac new_step := eapply nsteps_l.

Lemma extract_TUnit_embed_TUnit v : nsteps pure_step 6 (extract_TUnit (embedV_TUnit v)) v.
Proof.
  new_step. ps_head_step.
  new_step. apply (pure_step_ctx (fill_item (CaseCtx _ _))). ps_head_step. simpl.
  new_step. ps_head_step.
  new_step. ps_head_step.
  new_step. ps_head_step.
  new_step. ps_head_step.
  constructor.
Qed.

Lemma extract_TProd_embed_TProd v : nsteps pure_step 5 (extract_Ground_TProd (embedV_Ground_TProd v)) v.
Proof.
  new_step. ps_head_step.
  new_step. apply (pure_step_ctx (fill_item (CaseCtx _ _))). ps_head_step. simpl.
  new_step. ps_head_step.
  new_step. ps_head_step.
  new_step. ps_head_step.
  constructor.
Qed.

Lemma extract_TArrow_embed_TArrow v : nsteps pure_step 4 (extract_Ground_TArrow (embedV_Ground_TArrow v)) v.
Proof.
  new_step. ps_head_step.
  new_step. apply (pure_step_ctx (fill_item (CaseCtx _ _))). ps_head_step. simpl.
  new_step. ps_head_step.
  new_step. ps_head_step.
  constructor.
Qed.

Lemma extract_TSum_embed_TSum v : nsteps pure_step 6 (extract_Ground_TSum (embedV_Ground_TSum v)) v.
Proof.
  new_step. ps_head_step.
  new_step. apply (pure_step_ctx (fill_item (CaseCtx _ _))). ps_head_step. simpl.
  new_step. ps_head_step.
  new_step. ps_head_step.
  new_step. ps_head_step.
  new_step. ps_head_step.
  constructor.
Qed.


Lemma extract_TRec_embed_TUnknown v : nsteps pure_step 3 (extract_Ground_TRec (# embedV_TUnknown v)) (Fold (# v)).
Proof.
  new_step. ps_head_step.
  new_step. apply (pure_step_ctx (fill_item (CaseCtx _ _))). ps_head_step. simpl.
  new_step. ps_head_step.
  constructor.
Qed.
