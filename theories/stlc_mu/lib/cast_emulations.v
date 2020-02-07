From fae_gtlc_mu.cast_calculus Require Export types.
From fae_gtlc_mu.stlc_mu Require Export typing lang lib.fix lib.universe.
From fae_gtlc_mu.backtranslation Require Export types.

(** Trivial stuff *)

Definition identity : expr :=
  Lam (Var 0).

(** Embeddings *)

Definition embed_TUnit : expr :=
  Lam (Fold (InjL (InjL (InjL (InjL (Var 0)))))).

Lemma embed_TUnit_typed Γ τ (G : Ground τ) :
  Γ ⊢ₛ embed_TUnit : (TUnit → Universe).
Proof.
  apply Lam_typed, Fold_typed.
  repeat apply InjL_typed.
  by apply Var_typed.
Qed.

Definition embed_Gound_TSum : expr :=
  Lam (Fold ((InjL (InjL (InjL (InjR (Var 0))))))).

Definition embed_Gound_TSum_typed :
  [] ⊢ₛ embed_Gound_TSum : ((Universe + Universe) → Universe)%type.
Proof.
  apply Lam_typed.
  apply Fold_typed.
  repeat apply InjL_typed. apply InjR_typed.
  by apply Var_typed.
Qed.

Definition embed_Gound_TProd : expr :=
  Lam (Fold (InjL (InjL (InjR (Var 0))))).

Definition embed_Gound_TProd_typed :
  [] ⊢ₛ embed_Gound_TProd : ((Universe × Universe) → Universe).
Proof.
  apply Lam_typed, Fold_typed.
  repeat apply InjL_typed. asimpl. repeat apply InjR_typed.
  by apply Var_typed.
Qed.

Definition embed_Gound_TArrow : expr :=
  Lam (Fold (InjL (InjR (Var 0)))).

Definition embed_Gound_TArrow_typed :
  [] ⊢ₛ embed_Gound_TArrow : ((Universe → Universe) → Universe).
Proof.
  apply Lam_typed, Fold_typed.
  repeat apply InjL_typed. asimpl. repeat apply InjR_typed.
  by apply Var_typed.
Qed.

Definition embed_Gound_TRec  : expr :=
  Lam (Fold (InjR (Unfold (Var 0)))).

Definition embed_Gound_TRec_typed :
  [] ⊢ₛ embed_Gound_TRec : (TRec Universe → Universe).
Proof.
  apply Lam_typed. apply Fold_typed.
  apply InjR_typed.
  asimpl.
  apply Unfold_typed_help; first by trivial.
  by apply Var_typed.
Qed.

(** Extractions *)

Definition Ω : expr :=
  (
    (Lam ((Unfold (Var 0)) (Var 0)))
      (Fold (Lam ((Unfold (Var 0)) (Var 0))))
  ).

Definition Ω_typed Γ τ : (Is_Closed τ) -> (Γ ⊢ₛ Ω : τ).
Proof.
  intro P.
  apply App_typed with (τ1 := (TRec (TVar 0 → τ))).
  - apply Lam_typed.
    apply App_typed with (τ1 := TRec (TVar 0 → τ)).
    + apply Unfold_typed_help_2 with (τ := (TVar 0 → τ)).
      asimpl. by rewrite P. by apply Var_typed.
    + by apply Var_typed.
  - apply Fold_typed. asimpl. rewrite P.
    apply Lam_typed.
    apply App_typed with (τ1 := TRec (TVar 0 → τ)).
    + apply Unfold_typed_help_2 with (τ := (TVar 0 → τ)).
      asimpl. by rewrite P. by apply Var_typed.
    + by apply Var_typed.
Qed.

Definition extract_TUnit : expr :=
  Lam (Case (Unfold (Var 0))
            (Case (Var 0)
                  (Case (Var 0)
                        (Case (Var 0)
                              (Var 0)
                              (Ω)
                        )
                        (Ω)
                  )
                  (Ω)
            )
            (Ω)
      ).

Definition extract_TUnit_typed : [] ⊢ₛ extract_TUnit : (Universe → TUnit).
Proof.
  apply Lam_typed.
  apply Case_typed with (τ1 := (TUnit + (TVar 0 + TVar 0) + (TVar 0 × TVar 0) + (TVar 0 → TVar 0)).[Universe/]%type)
                         (τ2 := Universe).
  - eapply Unfold_typed_help_2 with (τ := Universe_body). by asimpl.
    by apply Var_typed.
  - apply Case_typed with (τ1 := (TUnit + (TVar 0 + TVar 0) + (TVar 0 × TVar 0)).[Universe/]%type)
                          (τ2 := (TVar 0 → TVar 0).[Universe/]%type).
    + by apply Var_typed.
    + eapply Case_typed.
      * by apply Var_typed.
      * eapply Case_typed.
        -- by apply Var_typed.
        -- by apply Var_typed.
        -- by apply Ω_typed.
      * by apply Ω_typed.
    + by apply Ω_typed.
  - by apply Ω_typed.
Qed.

Definition extract_Ground_TSum : expr :=
  Lam (Case (Unfold (Var 0))
            (Case (Var 0)
                  (Case (Var 0)
                        (Case (Var 0)
                              (Ω)
                              (Var 0)
                        )
                        (Ω)
                  )
                  (Ω)
            )
            (Ω)
      ).

Definition extract_Ground_TSum_typed : [] ⊢ₛ extract_Ground_TSum : (Universe → (Universe + Universe))%type.
Proof.
  apply Lam_typed.
  apply Case_typed with (τ1 := (TUnit + (TVar 0 + TVar 0) + (TVar 0 × TVar 0) + (TVar 0 → TVar 0)).[Universe/]%type)
                         (τ2 := Universe).
  - eapply Unfold_typed_help_2 with (τ := Universe_body). by asimpl. by apply Var_typed.
  - eapply Case_typed. by apply Var_typed.
    + eapply Case_typed.
      * by apply Var_typed.
      * eapply Case_typed.
        -- by apply Var_typed.
        -- by apply Ω_typed.
        -- by apply Var_typed.
      * by apply Ω_typed.
    + by apply Ω_typed.
  - by apply Ω_typed.
Qed.

Definition extract_Ground_TProd : expr :=
  Lam (Case (Unfold (Var 0))
            (Case (Var 0)
                  (Case (Var 0)
                        (Ω)
                        (Var 0)
                  )
                  (Ω)
            )
            (Ω)
      ).

Definition extract_Ground_TProd_typed : [] ⊢ₛ extract_Ground_TProd : (Universe → (Universe × Universe)).
Proof.
  apply Lam_typed.
  apply Case_typed with (τ1 := (TUnit + (TVar 0 + TVar 0) + (TVar 0 × TVar 0) + (TVar 0 → TVar 0)).[Universe/]%type)
                         (τ2 := Universe).
  - eapply Unfold_typed_help_2 with (τ := Universe_body). by asimpl. by apply Var_typed.
  - eapply Case_typed. by apply Var_typed.
    + eapply Case_typed.
      * by apply Var_typed.
      * by apply Ω_typed.
      * by apply Var_typed.
    + by apply Ω_typed.
  - by apply Ω_typed.
Qed.

Definition extract_Ground_TArrow : expr :=
  Lam (Case (Unfold (Var 0))
            (Case (Var 0)
                  (Ω)
                  (Var 0)
            )
            (Ω)
      ).

Definition extract_Ground_TArrow_typed : [] ⊢ₛ extract_Ground_TArrow : (Universe → (Universe → Universe)).
Proof.
  apply Lam_typed.
  apply Case_typed with (τ1 := (TUnit + (TVar 0 + TVar 0) + (TVar 0 × TVar 0) + (TVar 0 → TVar 0)).[Universe/]%type)
                         (τ2 := Universe).
  - eapply Unfold_typed_help_2 with (τ := Universe_body). by asimpl. by apply Var_typed.
  - eapply Case_typed. by apply Var_typed.
    + by apply Ω_typed.
    + by apply Var_typed.
  - by apply Ω_typed.
Qed.

Definition extract_Ground_TRec : expr :=
  Lam (Case (Unfold (Var 0))
            (Ω)
            (Fold (Var 0))
      ).

Definition extract_Ground_TRec_typed : [] ⊢ₛ extract_Ground_TRec : (Universe → TRec Universe).
Proof.
  apply Lam_typed.
  apply Case_typed with (τ1 := (TUnit + (TVar 0 + TVar 0) + (TVar 0 × TVar 0) + (TVar 0 → TVar 0)).[Universe/]%type)
                         (τ2 := Universe).
  - eapply Unfold_typed_help_2 with (τ := Universe_body). by asimpl. by apply Var_typed.
  - by apply Ω_typed.
  - apply Fold_typed. by apply Var_typed.
Qed.

(** Factorisations *)

Definition factorization (f1 f2 : expr) : expr :=
  Lam (f2 (f1 (Var 0))).

Lemma factorization_up_typed {f1 f2 : expr} {τ τG : cast_calculus.types.type} {G : Ground τG} {p1 : notT (Ground τ)} {p2 : not (τ = ⋆)} (d1 : forall Γ, Γ ⊢ₛ f1 : (<<τ>> → <<τG>>)) (d2 : forall Γ, Γ ⊢ₛ f2 : (<<τG>> → Universe)) :
  [] ⊢ₛ factorization f1 f2 : (<<τ>> → Universe).
Proof.
  apply Lam_typed.
  apply App_typed with (τ1 := << τG >>).
  apply d2.
  apply App_typed with (τ1 := << τ >>).
  apply d1.
  by apply Var_typed.
Qed.

Lemma factorization_down_typed {f1 f2 : expr} {τ τG : cast_calculus.types.type} {G : Ground τG} {p1 : notT (Ground τ)} {p2 : not (τ = ⋆)} (d1 : forall Γ, Γ ⊢ₛ f1 : (Universe → <<τG>>)) (d2 : forall Γ, Γ ⊢ₛ f2 : (<<τG>> → <<τ>>)) :
  [] ⊢ₛ factorization f1 f2 : (Universe → <<τ>>).
Proof.
  apply Lam_typed.
  apply App_typed with (τ1 := << τG >>).
  apply d2.
  apply App_typed with (τ1 := Universe).
  apply d1.
  by apply Var_typed.
Qed.

(** Between sums, products, recursive types, arrow types *)

Definition between_TSum (c1 c2 : expr) : expr :=
  Lam (Case (Var 0) (InjL (c1 (Var 0))) (InjR (c2 (Var 0)))).

Lemma between_TSum_typed (τ1 τ2 τ1' τ2' : cast_calculus.types.type) (f1 f2 : expr) (d1 : ∀ Γ, Γ ⊢ₛ f1 : (<<τ1>> → <<τ1'>>)) (d2 : ∀ Γ, Γ ⊢ₛ f2 : (<<τ2>> → <<τ2'>>)) :
  [] ⊢ₛ between_TSum f1 f2 : (<<τ1>> + <<τ2>> → <<τ1'>> + <<τ2'>>)%type.
Proof.
  apply Lam_typed.
  apply Case_typed with (τ1 := <<τ1>>) (τ2 := <<τ2>>).
  by apply Var_typed.
  constructor. eapply App_typed. apply d1. by apply Var_typed.
  constructor. eapply App_typed. apply d2. by apply Var_typed.
Qed.

Definition between_TProd (f1 f2 : expr) : expr :=
  Lam (Pair (f1 (Fst (Var 0))) (f2 (Snd (Var 0)))).

Lemma between_TProd_typed (τ1 τ2 τ1' τ2' : cast_calculus.types.type) (f1 f2 : expr) (d1 : ∀ Γ, Γ ⊢ₛ f1 : (<<τ1>> → <<τ1'>>)) (d2 : ∀ Γ, Γ ⊢ₛ f2 : (<<τ2>> → <<τ2'>>)) :
  [] ⊢ₛ between_TProd f1 f2 : ((<<τ1>> × <<τ2>>) → (<<τ1'>> × <<τ2'>>))%type.
Proof.
  apply Lam_typed.
  apply Pair_typed.
  eapply App_typed. apply d1. econstructor. by apply Var_typed.
  eapply App_typed. apply d2. econstructor. by apply Var_typed.
Qed.

Definition between_TArrow (ca cr : expr) : expr :=
  Lam (*f*)
    (Lam (*a*) (
         cr
           (((Var 1)(*f*)) (ca (Var 0(*a*))))
       )
    ).

Lemma between_TArrow_typed (τ1 τ2 τ3 τ4 : cast_calculus.types.type) (ca cr : expr) (da : ∀ Γ, Γ ⊢ₛ ca : (<<τ3>> → <<τ1>>)) (dr : ∀ Γ, Γ ⊢ₛ cr : (<<τ2>> → <<τ4>>)) :
  [] ⊢ₛ between_TArrow ca cr : ((<<τ1>> → <<τ2>>) → (<<τ3>> → <<τ4>>))%type.
Proof.
  repeat apply Lam_typed.
  apply App_typed with (τ1 := <<τ2>>).
  auto. apply App_typed with (τ1 := <<τ1>>); auto.
    by auto; apply Var_typed.
    eapply App_typed. auto.
    by apply Var_typed.
Qed.


(* Definition between_recs (τb τb' : cast_calculus.types.type) (f1 f2 : expr) : expr := *)
(*   Lam ( *)
(*       Fix ( *)
(*           Lam ( *)
(*               Lam (Fold (f (Unfold (Var 0)))) *)
(*             ) *)
(*           ) (Var 0) *)
(*     ). *)


(* Definition between_recs_typed (τb τb' : cast_calculus.types.type) (f1 f2 : expr) : expr := *)
(*   [] ⊢ₛ  *)

(* From fae_gtlc_mu Require Export stlc_mu.typing. *)

(** Complete definition *)

(* recursively defined on the alternative consistency relation *)

Definition add_head (i : nat) (ls : list nat) : list nat :=
  match ls with
  | nil => nil
  | cons x x0 => cons (i + x) x0
  end.

Fixpoint 𝓕 (τi τf : cast_calculus.types.type) (P : open_sym_alt τi τf) (Σ : list nat) : expr :=
  match P with
  (** ATOMIC cases *)
  | GenSymAltGroundGround τ G => identity
  | GenSymAltGroundStar τ G => match G with
                              | Ground_TUnit => embed_TUnit
                              | Ground_TProd => embed_Gound_TProd
                              | Ground_TSum => embed_Gound_TSum
                              | Ground_TArrow => embed_Gound_TArrow
                              | Ground_TRec => embed_Gound_TRec
                              end
  | GenSymAltStarGround τ G => match G with
                              | Ground_TUnit => extract_TUnit
                              | Ground_TProd => extract_Ground_TProd
                              | Ground_TSum => extract_Ground_TSum
                              | Ground_TArrow => extract_Ground_TArrow
                              | Ground_TRec => extract_Ground_TRec
                              end
  | GenSymAltStarStar => identity
  (** RECURSIVE cases *)
  | GenSymAltProds τ1 τ1' τ2 τ2' P1 P2 =>
    between_TProd (𝓕 τ1 τ1' P1 (add_head 1 Σ) (Fst (Var 0)))
                  (𝓕 τ2 τ2' P2 (add_head 1 Σ) (Snd (Var 0)))
  | GenSymAltSums τ1 τ1' τ2 τ2' P1 P2 =>
    between_TSum (𝓕 τ1 τ1' P1 (add_head 2 Σ) (Var 0))
                 (InjR (𝓕 τ2 τ2' P2 (add_head 2 Σ) (Var 0)))
  | GenSymAltArrows τ1 τ2 τ3 τ4 P31 P24 =>
    between_TArrow (𝓕 τ3 τ1 P31 (add_head 2 Σ))
                   (𝓕 τ2 τ4 P24 (add_head 2 Σ))
  | GenSymAltRec τ τ' x => Unit
  (* recursive calls from earlier *)
  | GenSymAltVars i =>
    Var (sum_list_with id (take (S i) Σ))
  | GenSymAltVarStar i => Unit
    (* Lam (𝓕 _ _ (GenSymAltGroundStar Ground_TRec) (add_head 1 Σ) *)
           (* (Var (sum_list_with id (take (S i) Σ))) *)
        (* ) *)
        (* wrrooooong *)

  (* compare μ. () + (nat × #0) ~ μ. () + (nat × ⋆) *)
          (* vs *)
          (* μ. () + (nat × #0) ~ μ. ⋆ *)
  (* recursive call will be different in both cases... *)

  | GenSymAltStarVar i => Unit
  | GenSymAltStarTau τ τG G x => Unit
  | GenSymAltTauStar τ τG G x => Unit
  end.

(* Fixpoint free_variables (τ : cast_calculus.types.type) : nat := *)
(*   match τ with *)
(*   | types.TUnit => 0 *)
(*   | types.TProd τ1 τ2 => max (free_variables τ1) (free_variables τ2) *)
(*   | types.TSum τ1 τ2 => max (free_variables τ1) (free_variables τ2) *)
(*   | types.TArrow τ1 τ2 => max (free_variables τ1) (free_variables τ2) *)
(*   | types.TRec τ => (free_variables τ) - 1 *)
(*   | types.TVar k => k *)
(*   | types.TUnknown => 0 *)
(*   end. *)

(* Definition upperbound (τ τ' : cast_calculus.types.type) : nat := max (free_variables τ) (free_variables τ'). *)



(* Definition 𝓕 (τi τf : cast_calculus.types.type) (P : open_sym τi τf) (Σ : vec expr (upperbound τi τf)) : expr. *)
(* Proof. *)
(*   induction P. *)
(*   - admit. *)
(*   - admit. *)
(*   - admit. *)
(*   - admit. *)
(*   - admit. *)
(*   - admit. *)
(*   - admit. *)
(*   - admit. *)


(* Fixpoint 𝓕 (τi τf : cast_calculus.types.type) (P : sym τi τf) : expr := *)


(* Lemma 𝓕_typed (τi τf : cast_calculus.types.type) : *)
(*   [] ⊢ₛ 𝓕 τi τf : TArrow <<τi>> <<τf>>. *)
(* Admitted. *)

