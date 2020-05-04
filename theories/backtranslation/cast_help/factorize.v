From fae_gtlc_mu.cast_calculus Require Export types.
From fae_gtlc_mu.stlc_mu Require Export typing lang lib.fix.
From fae_gtlc_mu.backtranslation.cast_help Require Export universe embed extract.

(** Trivial stuff *)

Definition identity : val :=
  LamV (Var 0).

Lemma identity_typed Γ pΓ τ pτ : Γ & pΓ ⊢ₛ identity : (TArrow τ τ) & (TArrow_closed pτ pτ).
Proof.
  intros.
  eapply Lam_typed. by apply Var_typed.
  Unshelve. all:auto.
Qed.

(** Factorisations *)

Definition factorization (f g : expr) : val :=
  LamV (
      g.[ren (+1)] (f.[ren (+1)] (Var 0))
    ).

Lemma factorization_subst_rewrite (f g : expr) σ : (# (factorization f g)).[σ] = factorization f.[σ] g.[σ].
Proof. by asimpl. Qed.

Lemma factorization_typed Γ pΓ {f g : expr} (τ1 : type) pτ1 τ2 pτ2 τ3 pτ3
      (df : Γ & pΓ ⊢ₛ f : (TArrow τ1 τ2) & TArrow_closed pτ1 pτ2)
      (dg : Γ & pΓ ⊢ₛ g : (TArrow τ2 τ3) & TArrow_closed pτ2 pτ3) :
  Γ & pΓ ⊢ₛ factorization f g : (TArrow τ1 τ3) & TArrow_closed pτ1 pτ3.
Proof.
  eapply Lam_typed.
  eapply App_typed with (τ1 := τ2).
  eapply up_type_one. apply dg.
  eapply App_typed with (τ1 := τ1).
  eapply up_type_one. apply df.
  by apply Var_typed.
  Unshelve. all:auto.
Qed.

(* Definition factorization_up (f : expr) (τG : cast_calculus.types.type) (G : Ground τG) : val := *)
(*   LamV ( *)
(*       embed τG G (f.[ren (+1)] (Var 0)) *)
(*     ). *)

(* Lemma factorization_up_subst_rewrite (f : expr) (τG : cast_calculus.types.type) (G : Ground τG) σ : (# (factorization_up f τG G)).[σ] = factorization_up f.[σ] τG G. *)
(* Proof. *)
(*   rewrite /factorization_up. *)
(*   asimpl. by rewrite embed_no_subs. *)
(* Qed. *)

(* Lemma factorization_up_typed Γ pΓ {f : expr} (τ : type) pτ (τG : cast_calculus.types.type) (G : Ground τG) *)
(*       (d : Γ & pΓ ⊢ₛ f : (TArrow τ <<τG>>) & TArrow_closed pτ (back_Ground_closed G)) : *)
(*   Γ & pΓ ⊢ₛ factorization_up f τG G : (TArrow τ Universe) & TArrow_closed pτ Universe_closed. *)
(* Proof. *)
(*   eapply Lam_typed. *)
(*   eapply App_typed with (τ1 := << τG >>). *)
(*   apply embed_typed. *)
(*   eapply App_typed with (τ1 := τ ). *)
(*   eapply up_type_one. apply d. *)
(*   by apply Var_typed. *)
(*   Unshelve. all:(auto||apply Universe_closed||by apply back_Ground_closed). *)
(* Qed. *)

(* Definition factorization_down (f : expr) (τG : cast_calculus.types.type) (G : Ground τG) : val := *)
(*   LamV ( *)
(*       (f.[ren (+1)]) (extract τG G (Var 0)) *)
(*     ). *)

(* Lemma factorization_down_subst_rewrite (f : expr) (τG : cast_calculus.types.type) (G : Ground τG) σ : (# (factorization_down f τG G)).[σ] = factorization_down f.[σ] τG G. *)
(* Proof. *)
(*   rewrite /factorization_down. *)
(*   asimpl. by rewrite extract_no_subs. *)
(* Qed. *)

(* Lemma factorization_down_typed Γ pΓ {f : expr} (τ : type) pτ (τG : cast_calculus.types.type) (G : Ground τG) *)
(*       (d : Γ & pΓ ⊢ₛ f : (TArrow <<τG>> τ) & (TArrow_closed (back_Ground_closed G) pτ)) : *)
(*   Γ & pΓ ⊢ₛ factorization_down f τG G : (TArrow Universe τ) & (TArrow_closed Universe_closed pτ). *)
(* Proof. *)
(*   eapply Lam_typed. *)
(*   eapply App_typed with (τ1 := << τG >>). *)
(*   eapply up_type_one. apply d. *)
(*   eapply App_typed with (τ1 := Universe). *)
(*   apply extract_typed. *)
(*   by apply Var_typed. *)
(*   Unshelve. all:(auto||apply Universe_closed||by apply back_Ground_closed). *)
(* Qed. *)
