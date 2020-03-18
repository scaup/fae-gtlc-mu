From fae_gtlc_mu Require Export stlc_mu.lang.
From fae_gtlc_mu Require Export stlc_mu.typing.

Definition Fix : expr :=
  Lam (
      (Lam (Var 1 (Lam ((Unfold (Var 1)) (Var 1) (Var 0)))))
        (Fold (Lam (Var 1 (Lam ((Unfold (Var 1)) (Var 1) (Var 0))))))
  ).

Definition Fix_typed Γ τa τr (pa : Is_Closed τa) (pr : Is_Closed τr) :
  (Γ ⊢ₛ Fix : (TArrow (TArrow (TArrow τa τr) (TArrow τa τr)) (TArrow τa τr))).
Proof.
  apply Lam_typed.
  apply App_typed with (τ1 := (TRec (TArrow (TVar 0) (TArrow τa τr)))).
  - apply Lam_typed.
    apply App_typed with (τ1 := TArrow τa τr); first by apply Var_typed.
    apply Lam_typed.
    apply App_typed with (τ1 := τa).
    + apply App_typed with (τ1 := TRec (TArrow (TVar 0) (TArrow τa τr))).
      apply Unfold_typed_help_2 with (τ := TArrow (TVar 0) (TArrow τa τr)).
      asimpl. by rewrite pa pr. by apply Var_typed. by apply Var_typed.
    + by apply Var_typed.
  - apply Fold_typed. asimpl. rewrite pa pr.
    apply Lam_typed.
    apply App_typed with (τ1 := (TArrow τa τr)); first by apply Var_typed.
    apply Lam_typed.
    apply App_typed with (τ1 := τa).
    apply App_typed with (τ1 := TRec (TArrow (TVar 0) (TArrow τa τr))).
    apply Unfold_typed_help_2 with (τ := TArrow (TVar 0) (TArrow τa τr)).
    asimpl. by rewrite pa pr. by apply Var_typed. by apply Var_typed.
    by apply Var_typed.
Qed.

(* avoid to much substitutions since autosubst is as slow as a snail *)

Definition Fix' (f : expr) : expr :=
  (Lam ((rename (+1) f) (Lam ((Unfold (Var 1)) (Var 1) (Var 0)))))
    (Fold (Lam (rename (+1) f (Lam ((Unfold (Var 1)) (Var 1) (Var 0)))))).

Lemma Fix'_typed Γ τa τr f (pa : Is_Closed τa) (pr : Is_Closed τr) :
  (Γ ⊢ₛ f : (TArrow (TArrow τa τr) (TArrow τa τr))) -> (Γ ⊢ₛ Fix' f : (TArrow τa τr)).
Proof.
  intros H.
  apply App_typed with (τ1 := (TRec (TArrow (TVar 0) (TArrow τa τr)))).
  - apply Lam_typed.
    apply App_typed with (τ1 := TArrow τa τr). asimpl. rewrite -rename_ren. apply up_type_one. apply H.
    apply Lam_typed.
    apply App_typed with (τ1 := τa).
    + apply App_typed with (τ1 := TRec (TArrow (TVar 0) (TArrow τa τr))).
      asimpl. apply Unfold_typed_help_2 with (τ := TArrow (TVar 0) (TArrow τa τr)).
      asimpl. by rewrite pa pr. by apply Var_typed. by apply Var_typed.
    + by apply Var_typed.
  - apply Fold_typed. asimpl. rewrite pa pr.
    apply Lam_typed.
    apply App_typed with (τ1 := (TArrow τa τr)). rewrite -rename_ren. apply up_type_one. apply H.
    apply Lam_typed.
    apply App_typed with (τ1 := τa).
    apply App_typed with (τ1 := TRec (TArrow (TVar 0) (TArrow τa τr))).
    + apply Unfold_typed_help_2 with (τ := (TArrow (TVar 0) (TArrow τa τr))).
      asimpl. by rewrite pa pr. by apply Var_typed.
    + by apply Var_typed.
    + by apply Var_typed.
Qed.

Lemma Fix'_subs_rewrite f σ : (Fix' f).[σ] = Fix' (f.[σ]).
Proof.
  rewrite /Fix'.
  by asimpl.
Qed.

Definition Fix'' (f : expr) : expr :=
  (Unfold (Fold (Lam ((rename (+1) f) (Lam ((Unfold (Var 1)) (Var 1) (Var 0)))))))
    (Fold (Lam (rename (+1) f (Lam ((Unfold (Var 1)) (Var 1) (Var 0)))))).

Lemma Fix''_typed Γ τa τr f (pa : Is_Closed τa) (pr : Is_Closed τr) :
  (Γ ⊢ₛ f : (TArrow (TArrow τa τr) (TArrow τa τr))) -> (Γ ⊢ₛ Fix'' f : (TArrow τa τr)).
Proof.
  intros H.
  apply App_typed with (τ1 := (TRec (TArrow (TVar 0) (TArrow τa τr)))).
  - apply Unfold_typed_help_2 with (τ := TArrow (TVar 0) (TArrow τa τr)). by asimpl; by rewrite pa pr.
    apply Fold_typed.
    apply Lam_typed.
    apply App_typed with (τ1 := TArrow τa τr). asimpl. rewrite -rename_ren. apply up_type_one.
    rewrite pa pr.
    apply H.
    apply Lam_typed.
    apply App_typed with (τ1 := τa).
    + apply App_typed with (τ1 := TRec (TArrow (TVar 0) (TArrow τa τr))).
      asimpl. apply Unfold_typed_help_2 with (τ := TArrow (TVar 0) (TArrow τa τr)).
      asimpl. by rewrite pa pr. by apply Var_typed. by apply Var_typed.
    + by apply Var_typed.
  - apply Fold_typed. asimpl. rewrite pa pr.
    apply Lam_typed.
    apply App_typed with (τ1 := (TArrow τa τr)). rewrite -rename_ren. apply up_type_one. apply H.
    apply Lam_typed.
    apply App_typed with (τ1 := τa).
    apply App_typed with (τ1 := TRec (TArrow (TVar 0) (TArrow τa τr))).
    + apply Unfold_typed_help_2 with (τ := (TArrow (TVar 0) (TArrow τa τr))).
      asimpl. by rewrite pa pr. by apply Var_typed.
    + by apply Var_typed.
    + by apply Var_typed.
Qed.

Lemma Fix''_subs_rewrite f σ : (Fix'' f).[σ] = Fix'' (f.[σ]).
Proof.
  rewrite /Fix''.
  by asimpl.
Qed.

(* Definition Fix'' (f : expr) : expr := *)
(*   (Lam (f (Lam ((Unfold (Var 1)) (Var 1) (Var 0))))) *)
(*     (Fold (Lam (f (Lam ((Unfold (Var 1)) (Var 1) (Var 0)))))). *)

(* (* Lemma Fix''_typed Γ τa τr f (pa : Is_Closed τa) (pr : Is_Closed τr) : *) *)
(* (*   (Γ ⊢ₛ f : (TArrow (TArrow τa τr) (TArrow τa τr))) -> (Γ ⊢ₛ Fix'' f : (TArrow τa τr)). *) *)
(* (* Proof. *) *)
(* (*   intros H. *) *)
(* (*   apply App_typed with (τ1 := (TRec (TArrow (TVar 0) (TArrow τa τr)))). *) *)
(* (*   - apply Lam_typed. *) *)
(* (*     apply App_typed with (τ1 := TArrow τa τr). asimpl. rewrite -rename_ren. apply up_type_one. apply H. *) *)
(* (*     apply Lam_typed. *) *)
(* (*     apply App_typed with (τ1 := τa). *) *)
(* (*     + apply App_typed with (τ1 := TRec (TArrow (TVar 0) (TArrow τa τr))). *) *)
(* (*       asimpl. apply Unfold_typed_help_2 with (τ := TArrow (TVar 0) (TArrow τa τr)). *) *)
(* (*       asimpl. by rewrite pa pr. by apply Var_typed. by apply Var_typed. *) *)
(* (*     + by apply Var_typed. *) *)
(* (*   - apply Fold_typed. asimpl. rewrite pa pr. *) *)
(* (*     apply Lam_typed. *) *)
(* (*     apply App_typed with (τ1 := (TArrow τa τr)). rewrite -rename_ren. apply up_type_one. apply H. *) *)
(* (*     apply Lam_typed. *) *)
(* (*     apply App_typed with (τ1 := τa). *) *)
(* (*     apply App_typed with (τ1 := TRec (TArrow (TVar 0) (TArrow τa τr))). *) *)
(* (*     + apply Unfold_typed_help_2 with (τ := (TArrow (TVar 0) (TArrow τa τr))). *) *)
(* (*       asimpl. by rewrite pa pr. by apply Var_typed. *) *)
(* (*     + by apply Var_typed. *) *)
(* (*     + by apply Var_typed. *) *)
(* (* Qed. *) *)

(* Lemma test0 σ : (Var 0).[ids 0 .: σ] = Var 0. *)
(* Proof. *)
(*   by simpl. *)
(* Qed. *)

(* Lemma test1 σ : (Var 0).[ids 0 .: σ] = (Var 0). *)
(* Proof. *)
(*   asimpl. done. *)
(* Qed. *)

(* Lemma test2 e σ : (rename (+1) e).[ids 0 .: σ] = e.[σ]. *)
(* Proof. *)
(*   asimpl. done. *)
(* Qed. *)

Definition Fix_stepped : expr :=
  (Lam (Var 1 (Lam ((Unfold (Var 1)) (Var 1) (Var 0)))))
    (Fold (Lam (Var 1 (Lam ((Unfold (Var 1)) (Var 1) (Var 0)))))).


Definition Fix_stepped_subs_typed Γ τa τr f (pa : Is_Closed τa) (pr : Is_Closed τr) :
  (Γ ⊢ₛ f : (TArrow (TArrow τa τr) (TArrow τa τr))) -> (Γ ⊢ₛ Fix_stepped.[f/] : (TArrow τa τr)).
Proof.
  intros H.
  apply App_typed with (τ1 := (TRec (TArrow (TVar 0) (TArrow τa τr)))).
  - apply Lam_typed.
    apply App_typed with (τ1 := TArrow τa τr). asimpl. rewrite -rename_ren. apply up_type_one. apply H.
    apply Lam_typed.
    apply App_typed with (τ1 := τa).
    + apply App_typed with (τ1 := TRec (TArrow (TVar 0) (TArrow τa τr))).
      asimpl. apply Unfold_typed_help_2 with (τ := TArrow (TVar 0) (TArrow τa τr)).
      asimpl. by rewrite pa pr. by apply Var_typed. by apply Var_typed.
    + by apply Var_typed.
  - apply Fold_typed. asimpl. rewrite pa pr.
    apply Lam_typed.
    apply App_typed with (τ1 := (TArrow τa τr)). rewrite -rename_ren. apply up_type_one. apply H.
    apply Lam_typed.
    apply App_typed with (τ1 := τa).
    apply App_typed with (τ1 := TRec (TArrow (TVar 0) (TArrow τa τr))).
    + apply Unfold_typed_help_2 with (τ := (TArrow (TVar 0) (TArrow τa τr))).
      asimpl. by rewrite pa pr. by apply Var_typed.
    + by apply Var_typed.
    + by apply Var_typed.
Qed.

(* Definition Fix_stepped_typed Γ τ : (Is_Closed τ) -> (((TArrow τ τ) :: Γ) ⊢ₛ Fix_stepped : τ). *)
(* Proof. *)
(*   intro P. *)
(*   apply App_typed with (τ1 := (TRec (TArrow (TVar 0) τ))). *)
(*   - apply Lam_typed. *)
(*     apply App_typed with (τ1 := τ); first by apply Var_typed. *)
(*     apply App_typed with (τ1 := TRec (TArrow (TVar 0) τ)). *)
(*     + apply Unfold_typed_help_2 with (τ := TArrow (TVar 0) τ). *)
(*       asimpl. by rewrite P. by apply Var_typed. *)
(*     + by apply Var_typed. *)
(*   - apply Fold_typed. asimpl. rewrite P. *)
(*     apply Lam_typed. *)
(*     apply App_typed with (τ1 := τ); first by apply Var_typed. *)
(*     apply App_typed with (τ1 := TRec (TArrow (TVar 0) τ)). *)
(*     + apply Unfold_typed_help_2 with (τ := (TArrow (TVar 0) τ)). *)
(*       asimpl. by rewrite P. by apply Var_typed. *)
(*     + by apply Var_typed. *)
(* Qed. *)
