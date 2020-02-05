From fae_gtlc_mu.cast_calculus Require Export types.
From fae_gtlc_mu.stlc_mu Require Export typing lang lib.fix lib.universe.
From fae_gtlc_mu.backtranslation Require Export types.

(** Embeddings *)

Definition ce_unit_to_unknown : expr :=
  Lam (Fold (InjL (InjL (InjL (InjL (Var 0)))))).

Lemma ce_unit_to_unknown_typed Γ τ (G : Ground τ) :
  Γ ⊢ₛ ce_unit_to_unknown : (TUnit → Universe).
Proof.
  apply Lam_typed, Fold_typed.
  repeat apply InjL_typed.
  by apply Var_typed.
Qed.

Definition ce_ground_sum_to_unknown : expr :=
  Lam (Fold ((InjL (InjL (InjL (InjR (Var 0))))))).

Definition ce_ground_sum_to_unknown_typed :
  [] ⊢ₛ ce_ground_sum_to_unknown : ((Universe + Universe) → Universe)%type.
Proof.
  apply Lam_typed.
  apply Fold_typed.
  repeat apply InjL_typed. apply InjR_typed.
  by apply Var_typed.
Qed.

Definition ce_ground_prod_to_unknown : expr :=
  Lam (Fold (InjL (InjL (InjR (Var 0))))).

Definition ce_ground_prod_to_unknown_typed :
  [] ⊢ₛ ce_ground_prod_to_unknown : ((Universe × Universe) → Universe).
Proof.
  apply Lam_typed, Fold_typed.
  repeat apply InjL_typed. asimpl. repeat apply InjR_typed.
  by apply Var_typed.
Qed.

Definition ce_ground_rec_to_unknown  : expr :=
  Lam (Fold (InjR (Unfold (Var 0)))).

Definition ce_ground_rec_to_unknown_typed :
  [] ⊢ₛ ce_ground_rec_to_unknown : (TRec Universe → Universe).
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

Definition Match_TUnit : expr :=
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

Definition Match_TUnit_typed : [] ⊢ₛ Match_TUnit : (Universe → TUnit).
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

Definition Match_TSum : expr :=
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

Definition Match_TSum_typed : [] ⊢ₛ Match_TSum : (Universe → (Universe + Universe))%type.
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

Definition Match_TProd : expr :=
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

Definition Match_TProd_typed : [] ⊢ₛ Match_TProd : (Universe → (Universe × Universe)).
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

Definition Match_TArrow : expr :=
  Lam (Case (Unfold (Var 0))
            (Case (Var 0)
                  (Ω)
                  (Var 0)
            )
            (Ω)
      ).

Definition Match_TArrow_typed : [] ⊢ₛ Match_TArrow : (Universe → (Universe → Universe)).
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

Definition Match_TRec : expr :=
  Lam (Case (Unfold (Var 0))
            (Ω)
            (Fold (Var 0))
      ).

Definition Match_TRec_typed : [] ⊢ₛ Match_TRec : (Universe → TRec Universe).
Proof.
  apply Lam_typed.
  apply Case_typed with (τ1 := (TUnit + (TVar 0 + TVar 0) + (TVar 0 × TVar 0) + (TVar 0 → TVar 0)).[Universe/]%type)
                         (τ2 := Universe).
  - eapply Unfold_typed_help_2 with (τ := Universe_body). by asimpl. by apply Var_typed.
  - by apply Ω_typed.
  - apply Fold_typed. by apply Var_typed.
Qed.

(** Factorisations *)

Definition up_factorization (f1 f2 : expr) (τ τG : cast_calculus.types.type) (G : Ground τG) (_ : not (Ground τ)) (_ : not (τ = ⋆)) (_ : sym τ τG) : expr :=
  Lam (f2 (f1 (Var 0))).

Lemma up_factorization_typed {f1 f2 : expr} {τ τG : cast_calculus.types.type} {G : Ground τG} {p1 : not (Ground τ)} {p2 : not (τ = ⋆)} {p3 : sym τ τG} (d1 : forall Γ, Γ ⊢ₛ f1 : (<<τ>> → <<τG>>)) (d2 : forall Γ, Γ ⊢ₛ f2 : (<<τG>> → Universe)) :
  [] ⊢ₛ up_factorization f1 f2 τ τG G p1 p2 p3 : (<<τ>> → Universe).
Proof.
  apply Lam_typed.
  apply App_typed with (τ1 := << τG >>).
  apply d2.
  apply App_typed with (τ1 := << τ >>).
  apply d1.
  by apply Var_typed.
Qed.

Definition down_factorization (f1 f2 : expr) (τ τG : cast_calculus.types.type) (G : Ground τG) (_ : not (Ground τ)) (_ : not (τ = ⋆)) (_ : sym τ τG) : expr :=
  Lam (f2 (f1 (Var 0))).

Lemma down_factorization_typed {f1 f2 : expr} {τ τG : cast_calculus.types.type} {G : Ground τG} {p1 : not (Ground τ)} {p2 : not (τ = ⋆)} {p3 : sym τ τG} (d1 : forall Γ, Γ ⊢ₛ f1 : (Universe → <<τG>>)) (d2 : forall Γ, Γ ⊢ₛ f2 : (<<τG>> → <<τ>>)) :
  [] ⊢ₛ up_factorization f1 f2 τ τG G p1 p2 p3 : (Universe → <<τ>>).
Proof.
  apply Lam_typed.
  apply App_typed with (τ1 := << τG >>).
  apply d2.
  apply App_typed with (τ1 := Universe).
  apply d1.
  by apply Var_typed.
Qed.

(** Between sums, products, recursive types, arrow types *)

Definition between_sums (τ1 τ2 τ1' τ2' : cast_calculus.types.type) (f1 f2 : expr) : expr :=
  Lam (Case (Var 0) (InjL (f1 (Var 0))) (InjR (f2 (Var 0)))).

Lemma between_sums_typed (τ1 τ2 τ1' τ2' : cast_calculus.types.type) (f1 f2 : expr) (d1 : ∀ Γ, Γ ⊢ₛ f1 : (<<τ1>> → <<τ1'>>)) (d2 : ∀ Γ, Γ ⊢ₛ f2 : (<<τ2>> → <<τ2'>>)) :
  [] ⊢ₛ between_sums τ1 τ2 τ1' τ2' f1 f2 : (<<τ1>> + <<τ2>> → <<τ1'>> + <<τ2'>>)%type.
Proof.
  apply Lam_typed.
  apply Case_typed with (τ1 := <<τ1>>) (τ2 := <<τ2>>).
  by apply Var_typed.
  constructor. eapply App_typed. apply d1. by apply Var_typed.
  constructor. eapply App_typed. apply d2. by apply Var_typed.
Qed.

Definition between_prods (τ1 τ2 τ1' τ2' : cast_calculus.types.type) (f1 f2 : expr) : expr :=
  Lam (Pair (f1 (Fst (Var 0))) (f2 (Snd (Var 0)))).

Lemma between_prods_typed (τ1 τ2 τ1' τ2' : cast_calculus.types.type) (f1 f2 : expr) (d1 : ∀ Γ, Γ ⊢ₛ f1 : (<<τ1>> → <<τ1'>>)) (d2 : ∀ Γ, Γ ⊢ₛ f2 : (<<τ2>> → <<τ2'>>)) :
  [] ⊢ₛ between_prods τ1 τ2 τ1' τ2' f1 f2 : ((<<τ1>> × <<τ2>>) → (<<τ1'>> × <<τ2'>>))%type.
Proof.
  apply Lam_typed.
  apply Pair_typed.
  eapply App_typed. apply d1. econstructor. by apply Var_typed.
  eapply App_typed. apply d2. econstructor. by apply Var_typed.
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

Fixpoint 𝓕 (τi τf : cast_calculus.types.type) (P : sym τi τf) : expr :=
  match P with
  | SymUnit => (Lam (Var 0))
  | SymUnknownL τ (* ⋆ ~ τ *) => 
  | SymUnknwonR τ => Unit
  | SymSum τ1 τ1' τ2 τ2' s1 s2 => Unit
  | SymProd τ1 τ1' τ2 τ2' s1 s2 => Unit
  | SymArrow τ1 τ1' τ2 τ2' s1 s2 => Unit
  end.



Admitted.

Lemma 𝓕_typed (τi τf : cast_calculus.types.type) :
  [] ⊢ₛ 𝓕 τi τf : TArrow <<τi>> <<τf>>.
Admitted.

