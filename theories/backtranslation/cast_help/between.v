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

Lemma between_TSum_typed Γ pΓ τ1 pτ1 τ2 pτ2 τ1' pτ1' τ2' pτ2' (f1 f2 : expr)
      (d1 : Γ & pΓ ⊢ₛ f1 : (TArrow τ1 τ1') & (TArrow_closed pτ1 pτ1'))
      (d2 : Γ & pΓ ⊢ₛ f2 : (TArrow τ2 τ2') & (TArrow_closed pτ2 pτ2')) :
  Γ & pΓ ⊢ₛ between_TSum f1 f2 : (TArrow (τ1 + τ2) (τ1' + τ2'))%type & (TArrow_closed (TSum_closed pτ1 pτ2) (TSum_closed pτ1' pτ2')).
Proof.
  eapply Lam_typed.
  eapply Case_typed.
  by apply Var_typed.
  eapply InjL_typed. eapply App_typed.
  eapply up_type_two. apply d1.
  by apply Var_typed.
  eapply InjR_typed. eapply App_typed.
  eapply up_type_two. apply d2. by apply Var_typed.
  Unshelve. all:intro σ; asimpl; repeat rewrite pτ1; repeat rewrite pτ1'; repeat rewrite pτ2; repeat rewrite pτ2'; done.
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

Lemma between_TProd_typed Γ pΓ τ1 pτ1 τ2 pτ2 τ1' pτ1' τ2' pτ2' (f1 f2 : expr)
      (d1 : Γ & pΓ ⊢ₛ f1 : (TArrow τ1 τ1') & (TArrow_closed pτ1 pτ1'))
      (d2 : Γ & pΓ ⊢ₛ f2 : (TArrow τ2 τ2') & (TArrow_closed pτ2 pτ2')) :
  Γ & pΓ ⊢ₛ between_TProd f1 f2 : (TArrow (τ1 × τ2) (τ1' × τ2'))%type & (TArrow_closed (TProd_closed pτ1 pτ2) (TProd_closed pτ1' pτ2')).
Proof.
  eapply Lam_typed.
  eapply Pair_typed.
  eapply App_typed.
  eapply up_type_one. apply d1. econstructor. by apply Var_typed.
  eapply App_typed.
  apply up_type_one. apply d2. econstructor. by apply Var_typed.
  Unshelve. all:intro σ; asimpl; repeat rewrite pτ1; repeat rewrite pτ1'; repeat rewrite pτ2; repeat rewrite pτ2'; done.
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

Lemma between_TArrow_typed Γ pΓ τ1 pτ1 τ2 pτ2 τ3 pτ3 τ4 pτ4 (ca cr : expr)
      (da : Γ & pΓ ⊢ₛ ca : (TArrow τ3 τ1) & (TArrow_closed pτ3 pτ1))
      (dr : Γ & pΓ ⊢ₛ cr : (TArrow τ2 τ4) & (TArrow_closed pτ2 pτ4)) :
  Γ & pΓ ⊢ₛ between_TArrow ca cr : (TArrow (TArrow τ1 τ2) (TArrow τ3 τ4))%type &
                                   (TArrow_closed (TArrow_closed pτ1 pτ2) (TArrow_closed pτ3 pτ4)).
Proof.
  repeat eapply Lam_typed.
  eapply App_typed with (τ1 := τ2).
  eapply up_type_two. apply dr. eapply App_typed with (τ1 := τ1).
    by auto; apply Var_typed.
    eapply App_typed. by eapply up_type_two.
    by apply Var_typed.
  Unshelve. all:intro σ; asimpl; repeat rewrite pτ1; repeat rewrite pτ2; repeat rewrite pτ3; repeat rewrite pτ4; done.
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

Lemma between_TRec_typed Γ pΓ τi pμτi τf pμτf (f : expr)
      (d : ((TArrow (TRec τi) (TRec τf)):: Γ) & (Forall_cons _ _ _ (TArrow_closed pμτi pμτf) pΓ) ⊢ₛ f : (TArrow (τi.[TRec τi/]) τf.[TRec τf/]) &
      TArrow_closed (TRec_closed_unfold pμτi) (TRec_closed_unfold pμτf)) :
  Γ & pΓ ⊢ₛ between_TRec f : (TArrow (TRec τi) (TRec τf))%type &
      TArrow_closed pμτi pμτf.
Proof.
  eapply Lam_typed.
  eapply App_typed with (τ1 := TRec τi).
  apply Fix_typed; auto.
  eapply Lam_typed.
  eapply Lam_typed.
  eapply Fold_typed.
  eapply App_typed with (τ1 := τi.[(TRec τi)/]).
  eapply up_type_one.
  revert d.
  generalize (Forall_cons TClosed (TArrow (TRec τi) (TRec τf)) Γ (TArrow_closed pμτi pμτf) pΓ).
  rewrite rewrite_for_context_weakening. intros pp d.
  Unshelve. 4-15: auto. 4-5: by apply TArrow_closed.
  generalize (Forall_cons TClosed (TArrow (TRec τi) (TRec τf)) (TRec τi :: Γ) (TArrow_closed pμτi pμτf)
    (Forall_cons TClosed (TRec τi) Γ pμτi pΓ)).
  rewrite (rewrite_for_context_weakening Γ).
  rewrite rewrite_for_context_weakening.
  intro ppp.
  eapply context_gen_weakening.
  apply d.
  eapply Unfold_typed.
  by apply Var_typed.
  by apply Var_typed.
  Unshelve. all: try done; by apply TRec_closed_unfold.
Qed.
