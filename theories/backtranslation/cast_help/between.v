From fae_gtlc_mu.stlc_mu Require Export typing lang lib.fix.
From fae_gtlc_mu Require Export prelude.

(** Between sums, products, recursive types, arrow types *)

Lemma subst_lam e σ : (Lam e).[σ] = Lam e.[up σ].
Proof.
  by simpl.
Qed.

Lemma subst_app e1 e2 σ : (App e1 e2).[σ] = (App e1.[σ] e2.[σ]).
Proof.
  by simpl.
Qed.

Definition between_TSum (c1 c2 : expr) : expr :=
  Lam (Case (Var 0) (InjL ((rename (+2) c1) (Var 0))) (InjR ((rename (+2) c2) (Var 0)))).

Lemma between_TSum_subst_rewrite σ f1 f2 :
  (between_TSum f1 f2).[σ] =
  between_TSum f1.[σ] f2.[σ].
Proof.
  rewrite /between_TSum.
  by asimpl.
Qed.

Lemma between_TSum_typed Γ (τ1 τ2 τ1' τ2' : type) (f1 f2 : expr) (d1 : Γ ⊢ₛ f1 : (TArrow τ1 τ1')) (d2 : Γ ⊢ₛ f2 : (TArrow τ2 τ2')) :
  Γ ⊢ₛ between_TSum f1 f2 : (TArrow (τ1 + τ2) (τ1' + τ2'))%type.
Proof.
  apply Lam_typed.
  eapply Case_typed.
  by apply Var_typed.
  constructor. eapply App_typed.
  apply up_type_two. apply d1.
  by apply Var_typed.
  constructor. eapply App_typed.
  apply up_type_two. apply d2. by apply Var_typed.
Qed.

Definition between_TProd (f1 f2 : expr) : expr :=
  Lam (Pair (rename (+1) f1 (Fst (Var 0))) (rename (+1) f2 (Snd (Var 0)))).

Lemma between_TProd_subst_rewrite σ f1 f2 :
  (between_TProd f1 f2).[σ] =
  between_TProd f1.[σ] f2.[σ].
Proof.
  rewrite /between_TProd.
  by asimpl.
Qed.

Lemma between_TProd_typed Γ (τ1 τ2 τ1' τ2' : type) (f1 f2 : expr) (d1 : Γ ⊢ₛ f1 : (TArrow τ1 τ1')) (d2 : Γ ⊢ₛ f2 : (TArrow τ2 τ2')) :
  Γ ⊢ₛ between_TProd f1 f2 : (TArrow (τ1 × τ2) (τ1' × τ2'))%type.
Proof.
  apply Lam_typed.
  apply Pair_typed.
  eapply App_typed.
  apply up_type_one. apply d1. econstructor. by apply Var_typed.
  eapply App_typed.
  apply up_type_one. apply d2. econstructor. by apply Var_typed.
Qed.

Definition between_TArrow (ca cr : expr) : expr :=
  Lam (*f*)
    (Lam (*a*) (
         rename (+2) cr (((Var 1)(*f*)) (rename (+2) ca (Var 0(*a*))))
       )
    ).

Lemma between_TArrow_subst_rewrite σ ca cr :
  (between_TArrow ca cr).[σ] =
  between_TArrow ca.[σ] cr.[σ].
Proof.
  rewrite /between_TArrow.
  by asimpl.
Qed.

Lemma between_TArrow_typed Γ (τ1 τ2 τ3 τ4 : type) (ca cr : expr) (da : Γ ⊢ₛ ca : (TArrow τ3 τ1)) (dr : Γ ⊢ₛ cr : (TArrow τ2 τ4)) :
  Γ ⊢ₛ between_TArrow ca cr : (TArrow (TArrow τ1 τ2) (TArrow τ3 τ4))%type.
Proof.
  repeat apply Lam_typed.
  apply App_typed with (τ1 := τ2).
  auto. apply up_type_two. apply dr. apply App_typed with (τ1 := τ1).
    by auto; apply Var_typed.
    eapply App_typed. by apply up_type_two.
    by apply Var_typed.
Qed.

Definition between_TRec (f : expr) : expr :=
  Lam (* x : μ. τi *) (
      Fix (
          Lam (* g : μ.τi → μ.τf *) (
              Lam (* r : μ.τi *) (
                  Fold (rename (+1) (f.[upn 1 (ren (+ 1))])(* : τi.[μ.τi/] → τf.[μ.τf]*) (Unfold (Var 0)))
                )
            )
        ) (Var 0)
    ).

Lemma between_TRec_typed Γ (τi τf : type) (Pi : Is_Closed (TRec τi)) (Pf : Is_Closed (TRec τf)) (f : expr)
      (d : ((TArrow (TRec τi) (TRec τf)):: Γ) ⊢ₛ f : (TArrow (τi.[TRec τi/]) τf.[TRec τf/])) :
  Γ ⊢ₛ between_TRec f : (TArrow (stlc_mu.typing.TRec τi) (stlc_mu.typing.TRec τf))%type.
Proof.
  apply Lam_typed.
  apply App_typed with (τ1 := TRec τi).
  (* apply App_typed with (τ1 := ((TRec τi → TRec τf) → (TRec τi → TRec τf))). *)
  eapply App_typed.
  apply Fix_typed; auto.
    (* by intro τ; simpl; rewrite -(Pi τ); rewrite -(Pf τ); by simpl. *)
  apply Lam_typed.
  apply Lam_typed.
  apply Fold_typed.
  apply App_typed with (τ1 := τi.[(TRec τi)/]).
  apply up_type_one.
  rewrite rewrite_for_context_weakening in d.
  rewrite (rewrite_for_context_weakening Γ).
  rewrite rewrite_for_context_weakening.
  apply context_gen_weakening.
  apply d.
  apply Unfold_typed.
  by apply Var_typed.
  by apply Var_typed.
Qed.

Definition between_TRec' (f : expr) : expr :=
  Lam (* x : μ. τi *) (
      Fix'' (
          Lam (* g : μ.τi → μ.τf *) (
              Lam (* r : μ.τi *) (
                  Fold (rename (+1) (f.[upn 1 (ren (+ 1))])(* : τi.[μ.τi/] → τf.[μ.τf]*) (Unfold (Var 0)))
                )
            )
        ) (Var 0)
    ).

Lemma between_TRec'_subst_rewrite σ f :
  (between_TRec' f).[σ] =
  between_TRec' f.[up σ].
Proof.
  rewrite /between_TRec'.
  rewrite subst_lam.
  rewrite subst_app.
  rewrite Fix''_subs_rewrite.
  by asimpl.
Qed.

Definition between_TRecV' (f : expr) : val :=
  LamV (* x : μ. τi *) (
      Fix'' (
          Lam (* g : μ.τi → μ.τf *) (
              Lam (* r : μ.τi *) (
                  Fold (rename (+1) (f.[upn 1 (ren (+ 1))])(* : τi.[μ.τi/] → τf.[μ.τf]*) (Unfold (Var 0)))
                )
            )
        ) (Var 0)
    ).

Lemma between_TRec'_to_value f : between_TRec' f = stlc_mu.lang.of_val (between_TRecV' f).
Proof.
  by simpl.
Qed.

Lemma between_TRec'_typed Γ (τi τf : type) (Pi : Is_Closed (TRec τi)) (Pf : Is_Closed (TRec τf)) (f : expr)
      (d : ((TArrow (TRec τi) (TRec τf)):: Γ) ⊢ₛ f : (TArrow (τi.[TRec τi/]) τf.[TRec τf/])) :
  Γ ⊢ₛ between_TRec' f : (TArrow (stlc_mu.typing.TRec τi) (stlc_mu.typing.TRec τf))%type.
Proof.
  apply Lam_typed.
  apply App_typed with (τ1 := TRec τi).
  apply Fix''_typed; auto.
    (* by intro τ; simpl; rewrite -(Pi τ); rewrite -(Pf τ); by simpl. *)
  apply Lam_typed.
  apply Lam_typed.
  apply Fold_typed.
  apply App_typed with (τ1 := τi.[(TRec τi)/]).
  apply up_type_one.
  rewrite rewrite_for_context_weakening in d.
  rewrite (rewrite_for_context_weakening Γ).
  rewrite rewrite_for_context_weakening.
  apply context_gen_weakening.
  apply d.
  apply Unfold_typed.
  by apply Var_typed.
  by apply Var_typed.
Qed.

Definition between_TRec_stepped (f : expr) : expr :=
  Lam (* x : μ. τi *) (
      Fix_stepped.[(
          Lam (* g : μ.τi → μ.τf *) (
              Lam (* r : μ.τi *) (
                  Fold (rename (+1) (f.[upn 1 (ren (+ 1))])(* : τi.[μ.τi/] → τf.[μ.τf]*) (Unfold (Var 0)))
                )
            )
        )/] (Var 0)
    ).

Lemma between_TRec_stepped_typed Γ (τi τf : type) (Pi : Is_Closed (TRec τi)) (Pf : Is_Closed (TRec τf)) (f : expr)
      (d : ((TArrow (TRec τi) (TRec τf)):: Γ) ⊢ₛ f : (TArrow (τi.[TRec τi/]) τf.[TRec τf/])) :
  Γ ⊢ₛ between_TRec_stepped f : (TArrow (stlc_mu.typing.TRec τi) (stlc_mu.typing.TRec τf))%type.
Proof.
  apply Lam_typed.
  apply App_typed with (τ1 := TRec τi).
  apply Fix_stepped_subs_typed; auto.
    (* by intro τ; simpl; rewrite -(Pi τ); rewrite -(Pf τ); by simpl. *)
  apply Lam_typed.
  apply Lam_typed.
  apply Fold_typed.
  apply App_typed with (τ1 := τi.[(TRec τi)/]).
  apply up_type_one.
  rewrite rewrite_for_context_weakening in d.
  rewrite (rewrite_for_context_weakening Γ).
  rewrite rewrite_for_context_weakening.
  apply context_gen_weakening.
  apply d.
  apply Unfold_typed.
  by apply Var_typed.
  by apply Var_typed.
Qed.

(* Lemma between_TRec_subs (f : expr) σ : (between_TRec_stepped f).[σ] = between_TRec_stepped (f.[ids 0 .: σ]). *)
(* Proof. *)
(*   rewrite /between_TRec_stepped /Fix_stepped. *)
(*   asimpl. *)
(*   auto. *)
(*   repeat rewrite rename_ren. *)
(*   simpl. *)
(*   f_equal. *)
(*   f_equal. *)
(*   f_equal. *)
(*   f_equal. *)
(*   f_equal. *)
(*   f_equal. *)
(*   f_equal. *)
(*   repeat rewrite subst_comp. repeat rewrite up_lift1. asimpl. *)
(*   rewrite -fold_ren_cons *)


(*   admit. *)
(*   asimpl. *)
(*   asimpl. *)
(*   asimpl. *)
(*   repeat f_equal. *)
(*   asimpl.  *)
(*   rewrite /up. *)
(*   rewrite -up_comp. *)
(*   asimpl. *)
