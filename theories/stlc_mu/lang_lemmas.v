From Autosubst Require Export Autosubst.
From iris.program_logic Require Export language ectx_language ectxi_language.
From fae_gtlc_mu.stlc_mu Require Export lang.

Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_eq/=
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : head_step ?e _ _ _ _ _ |- _ =>
      try (is_var e; fail 1);
      inversion H; subst; clear H
  end.

Local Hint Resolve to_of_val : core.

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
