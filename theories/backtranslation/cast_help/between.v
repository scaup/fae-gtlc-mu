From fae_gtlc_mu.stlc_mu Require Export typing lang lib.fix.
From fae_gtlc_mu Require Export prelude.
From Coq Require Export List.

(** Between sums, products, recursive types, arrow types *)

Lemma subst_lam e σ : (Lam e).[σ] = Lam e.[up σ].
Proof.
  by simpl.
Qed.

Lemma subst_app e1 e2 σ : (App e1 e2).[σ] = (App e1.[σ] e2.[σ]).
Proof.
  by simpl.
Qed.

Definition between_TSum (c1 c2 : expr) : val :=
  LamV (Case (Var 0) (InjL ((c1.[ren (+2)]) (Var 0))) (InjR ((c2.[ren (+2)]) (Var 0)))).

Lemma between_TSum_subst_rewrite σ f1 f2 :
  (# (between_TSum f1 f2)).[σ] =
  between_TSum f1.[σ] f2.[σ].
Proof.
  rewrite /between_TSum.
  by asimpl.
Qed.

Lemma between_TSum_typed Γ (τ1 τ2 τ1' τ2' : type) (f1 f2 : expr)
      (d1 : Γ ⊢ₛ f1 : (TArrow τ1 τ1'))
      (d2 : Γ ⊢ₛ f2 : (TArrow τ2 τ2')) :
  Γ ⊢ₛ between_TSum f1 f2 : (TArrow (τ1 + τ2) (τ1' + τ2'))%type.
Proof.
  assert (pτ1 : TClosed τ1). by apply (TArrow_closed1 (typed_closed d1)).
  assert (pτ2 : TClosed τ2). by apply (TArrow_closed1 (typed_closed d2)).
  assert (pτ1' : TClosed τ1'). by apply (TArrow_closed2 (typed_closed d1)).
  assert (pτ2' : TClosed τ2'). by apply (TArrow_closed2 (typed_closed d2)).
  apply Lam_typed. by apply TSum_closed.
  eapply Case_typed.
  apply Var_typed; auto. by apply TSum_closed.
  apply InjL_typed; auto. eapply App_typed.
  apply up_type_two. apply d1.
  by eapply (Var_typed _ _ _ _).
  eapply (InjR_typed _ _ _ _ _).
  eapply App_typed. apply up_type_two. apply d2.
  by eapply (Var_typed _ _ _ _).
  Unshelve. all: done.
Qed.

Definition between_TProd (f1 f2 : expr) : val :=
  LamV (Pair (f1.[ren (+1)] (Fst (Var 0))) (f2.[ren (+1)] (Snd (Var 0)))).

Lemma between_TProd_subst_rewrite σ f1 f2 :
  (# (between_TProd f1 f2)).[σ] =
  between_TProd f1.[σ] f2.[σ].
Proof.
  rewrite /between_TProd.
  by asimpl.
Qed.

Lemma between_TProd_typed Γ (τ1 τ2 τ1' τ2' : type) (f1 f2 : expr) (d1 : Γ ⊢ₛ f1 : (TArrow τ1 τ1')) (d2 : Γ ⊢ₛ f2 : (TArrow τ2 τ2')) :
  Γ ⊢ₛ between_TProd f1 f2 : (TArrow (τ1 × τ2) (τ1' × τ2'))%type.
Proof.
  assert (pτ1 : TClosed τ1). by apply (TArrow_closed1 (typed_closed d1)).
  assert (pτ2 : TClosed τ2). by apply (TArrow_closed1 (typed_closed d2)).
  assert (pτ1' : TClosed τ1'). by apply (TArrow_closed2 (typed_closed d1)).
  assert (pτ2' : TClosed τ2'). by apply (TArrow_closed2 (typed_closed d2)).
  apply Lam_typed. by apply TProd_closed.
  apply Pair_typed.
  eapply App_typed.
  apply up_type_one. apply d1. econstructor. apply Var_typed; auto. by apply TProd_closed.
  eapply (App_typed _ _ _ _).
  apply up_type_one. apply d2. econstructor. apply Var_typed; auto.
  Unshelve. by apply TProd_closed.
Qed.

Definition between_TArrow (ca cr : expr) : val :=
  LamV (*f*)
    (Lam (*a*) (
         cr.[ren (+2)] (((Var 1)(*f*)) (ca.[ren (+2)] (Var 0(*a*))))
       )
    ).

Lemma between_TArrow_subst_rewrite σ ca cr :
  (# (between_TArrow ca cr)).[σ] =
  between_TArrow ca.[σ] cr.[σ].
Proof.
  rewrite /between_TArrow.
  by asimpl.
Qed.

Lemma between_TArrow_typed Γ (τ1 τ2 τ3 τ4 : type) (ca cr : expr)
      (da : Γ ⊢ₛ ca : (TArrow τ3 τ1))
      (dr : Γ ⊢ₛ cr : (TArrow τ2 τ4)) :
  Γ ⊢ₛ between_TArrow ca cr : (TArrow (TArrow τ1 τ2) (TArrow τ3 τ4))%type.
Proof.
  assert (pτ1 : TClosed τ1). by apply (TArrow_closed2 (typed_closed da)).
  assert (pτ2 : TClosed τ2). by apply (TArrow_closed1 (typed_closed dr)).
  assert (pτ3 : TClosed τ3). by apply (TArrow_closed1 (typed_closed da)).
  repeat apply Lam_typed; try done; try by apply TArrow_closed.
  apply App_typed with (τ1 := τ2).
  auto. apply up_type_two. apply dr. apply App_typed with (τ1 := τ1).
    apply Var_typed; auto. by apply TArrow_closed.
    eapply App_typed. by apply up_type_two.
    by apply Var_typed.
Qed.

Definition between_TRec (f : expr) : val :=
  LamV (* x : μ. τi *) (
      Fix (
          Lam (* g : μ.τi → μ.τf *) (
              Lam (* r : μ.τi *) (
                  Fold (f.[upn 1 (ren (+ 1))].[ren (+1)](* : τi.[μ.τi/] → τf.[μ.τf]*) (Unfold (Var 0)))
                )
            )
        ) (Var 0)
    ).

Lemma between_TRec_subst_rewrite σ f :
  (# (between_TRec f)).[σ] =
  between_TRec f.[up σ].
Proof.
  rewrite /between_TRec.
  rewrite subst_lam.
  rewrite subst_app.
  rewrite Fix_subs_rewrite.
  by asimpl.
Qed.

Definition between_TRecV (f : expr) : val := between_TRec f.

Lemma between_TRec_to_value f : stlc_mu.lang.of_val (between_TRec f) = stlc_mu.lang.of_val (between_TRecV f).
Proof.
  by simpl.
Qed.

Lemma between_TRec_typed Γ (τi τf : type) (f : expr)
      (d : (TArrow (TRec τi) (TRec τf):: Γ) ⊢ₛ f : TArrow τi.[TRec τi/] τf.[TRec τf/]) :
  Γ ⊢ₛ between_TRec f : TArrow (TRec τi) (TRec τf)%type.
Proof.
  assert (Hi : TClosed (TRec τi)). apply (closed_Fold_typed_help _ (TArrow_closed1 (typed_closed d))).
  assert (Hf : TClosed (TRec τf)). apply (closed_Fold_typed_help _ (TArrow_closed2 (typed_closed d))).
  apply Lam_typed; auto.
  apply App_typed with (τ1 := TRec τi).
  apply Fix_typed; auto.
  apply Lam_typed. by apply TArrow_closed.
  apply Lam_typed; auto.
  apply Fold_typed.
  apply App_typed with (τ1 := τi.[(TRec τi)/]).
  apply up_type_one.
  rewrite rewrite_for_context_weakening in d.
  rewrite (rewrite_for_context_weakening Γ).
  rewrite rewrite_for_context_weakening.
  apply context_gen_weakening.
  apply d.
  apply Unfold_typed.
  apply Var_typed; auto.
  apply Var_typed; auto.
Qed.

