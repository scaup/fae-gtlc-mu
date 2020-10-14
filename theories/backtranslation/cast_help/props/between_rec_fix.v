From fae_gtlc_mu.stlc_mu Require Export lang typing_lemmas.
From fae_gtlc_mu.backtranslation.cast_help Require Export between general_def general_def_lemmas.

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

Lemma Fix_steps e : nsteps pure_step 2
                          (Fix (LamV e))
                          ((LamV e) (Lam ((Fix (Lam e).[ren (+1)]) (Var 0)))).
Proof.
  new_step. apply (pure_step_ctx (fill_item (AppLCtx _))). ps_head_step. simpl.
  new_step. ps_head_step. rewrite /Fix. asimpl.
  constructor.
Qed.

Lemma Fix_steps2 e v : nsteps pure_step 4
                             (Fix (LamV (LamV e)) (of_val v))
                             (e.[of_val v, Lam ((Fix (LamV (LamV e))).[ren (+1)] (Var 0))/]).
Proof.
  new_step. apply (pure_step_ctx (fill [AppLCtx _ ; AppLCtx _])). ps_head_step. asimpl.
  new_step. apply (pure_step_ctx (fill [AppLCtx _])). ps_head_step. asimpl.
  new_step. apply (pure_step_ctx (fill [AppLCtx _])). ps_head_step. asimpl.
  new_step. ps_head_step. asimpl.
  constructor.
Qed.

Lemma rewrite_subs_app (e1 e2 : expr) σ :
  (App e1 e2).[σ] = App e1.[σ] e2.[σ].
Proof.
  by simpl.
Qed.

Lemma between_TRec_steps_help f v : nsteps pure_step 1 (between_TRec f (of_val v))
  (Fix (Lam (Lam (Fold (f.[(ren (+ 1))] (Unfold (Var 0)))))) (of_val v)).
Proof.
  new_step. rewrite /between_TRec. ps_head_step.
  rewrite rewrite_subs_app Fix_subs_rewrite.
  asimpl. constructor.
Qed.

From fae_gtlc_mu.cast_calculus Require Export types consistency.

Lemma between_TRec_steps {A} {τl τr} (pC : alternative_consistency ((TRec τl, TRec τr) :: A) τl.[TRec τl/] τr.[TRec τr/]) fs (H : length A = length fs) (pμτlμτrnotA : (TRec τl, TRec τr) ∉ A) v :
  nsteps pure_step 6
    ((between_TRec (𝓕 pC)).[env_subst fs] (of_val (FoldV v)))
    (Fold ((𝓕c pC (𝓕cV (exposeRecursiveCAll A τl τr pμτlμτrnotA pC) fs H :: fs)) v)).
Proof.
  new_step. apply nsteps_once_inv. rewrite between_TRec_subst_rewrite. apply between_TRec_steps_help.
  cut (nsteps pure_step 5 (Fix (LamV (LamV (Fold ((𝓕 pC).[up (env_subst fs)].[ren (+1)] (Unfold (Var 0)))))) (of_val (FoldV v)))
    (Fold ((𝓕 pC).[env_subst (𝓕cV (exposeRecursiveCAll A τl τr pμτlμτrnotA pC) fs H :: fs)] (of_val v)))). by simpl.
  eapply (nsteps_trans 4 1).
  apply Fix_steps2. simpl. asimpl.
  assert (triv : (𝓕 pC).[Lam
                           (Unfold
                              (Fold
                                 (Lam
                                    (Lam (Lam (Fold ((𝓕 pC).[ids 1 .: env_subst fs >> ren (+4)] (Unfold (ids 0)))))
                                         (Lam (Unfold (ids 1) (ids 1) (ids 0))))))
                              (Fold
                                 (Lam
                                    (Lam (Lam (Fold ((𝓕 pC).[ids 1 .: env_subst fs >> ren (+4)] (Unfold (ids 0)))))
                                         (Lam (Unfold (ids 1) (ids 1) (ids 0)))))) (Var 0)) .: env_subst fs] =
                 (𝓕 pC).[env_subst (((between_TRecV (𝓕 pC).[up (stlc_mu.typing_lemmas.env_subst fs)])) :: fs)]).
  rewrite /between_TRecV /between_TRec /Fix. by asimpl. rewrite triv. clear triv.
  fold (𝓕c pC (between_TRecV (𝓕 pC).[up (stlc_mu.typing_lemmas.env_subst fs)] :: fs)).
  rewrite (𝓕c_rewrite pC). simpl. auto. intros H'.
  new_step. apply (pure_step_ctx (fill [AppRCtx _ ; FoldCtx])). ps_head_step. simpl.
  constructor.
Qed.
