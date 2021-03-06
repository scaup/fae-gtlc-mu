From fae_gtlc_mu.cast_calculus Require Export lang types typing_lemmas.

(** Defines a context of depth 1 *)
Inductive ctx_item :=
  | CTX_Lam
  | CTX_AppL (e2 : expr)
  | CTX_AppR (e1 : expr)
  (* Products *)
  | CTX_PairL (e2 : expr)
  | CTX_PairR (e1 : expr)
  | CTX_Fst
  | CTX_Snd
  (* Sums *)
  | CTX_InjL
  | CTX_InjR
  | CTX_CaseL (e1 : expr) (e2 : expr)
  | CTX_CaseM (e0 : expr) (e2 : expr)
  | CTX_CaseR (e0 : expr) (e1 : expr)
  (* Recursive Types *)
  | CTX_Fold
  | CTX_Unfold
  (* Casts *)
  | CTX_Cast (τi τf : type).

(** Filling in a term in such a context of depth 1 *)
Fixpoint fill_ctx_item (ctx : ctx_item) (e : expr) : expr :=
  match ctx with
  | CTX_Lam => Lam e
  | CTX_AppL e2 => App e e2
  | CTX_AppR e1 => App e1 e
  | CTX_PairL e2 => Pair e e2
  | CTX_PairR e1 => Pair e1 e
  | CTX_Fst => Fst e
  | CTX_Snd => Snd e
  | CTX_InjL => InjL e
  | CTX_InjR => InjR e
  | CTX_CaseL e1 e2 => Case e e1 e2
  | CTX_CaseM e0 e2 => Case e0 e e2
  | CTX_CaseR e0 e1 => Case e0 e1 e
  | CTX_Fold => Fold e
  | CTX_Unfold => Unfold e
  | CTX_Cast τi τf => Cast e τi τf
  end.

(** A general context is now represented by a list of these superficial contexts *)
Definition ctx := list ctx_item.

(** Filling in a term in these general contexts *)
Definition fill_ctx (K : ctx) (e : expr) : expr := foldr fill_ctx_item e K.

(** Typing derivation for contexts of depth 1 *)
Inductive typed_ctx_item : ctx_item → list type → type → list type → type → Prop :=
  | TP_CTX_Lam Γ τ (pτ : Closed τ) τ' :
     typed_ctx_item CTX_Lam (τ :: Γ) τ' Γ (TArrow τ τ')
  | TP_CTX_AppL Γ e2 τ τ' :
     typed Γ e2 τ →
     typed_ctx_item (CTX_AppL e2) Γ (TArrow τ τ') Γ τ'
  | TP_CTX_AppR Γ e1 τ τ' :
     typed Γ e1 (TArrow τ τ') →
     typed_ctx_item (CTX_AppR e1) Γ τ Γ τ'
  | TP_CTX_PairL Γ e2 τ τ' :
     typed Γ e2 τ' →
     typed_ctx_item (CTX_PairL e2) Γ τ Γ (TProd τ τ')
  | TP_CTX_PairR Γ e1 τ τ' :
     typed Γ e1 τ →
     typed_ctx_item (CTX_PairR e1) Γ τ' Γ (TProd τ τ')
  | TP_CTX_Fst Γ τ τ' :
     typed_ctx_item CTX_Fst Γ (TProd τ τ') Γ τ
  | TP_CTX_Snd Γ τ τ' :
     typed_ctx_item CTX_Snd Γ (TProd τ τ') Γ τ'
  | TP_CTX_InjL Γ τ τ' (pτ' : Closed τ') :
     typed_ctx_item CTX_InjL Γ τ Γ (TSum τ τ')
  | TP_CTX_InjR Γ τ (pτ : Closed τ) τ' :
     typed_ctx_item CTX_InjR Γ τ' Γ (TSum τ τ')
  | TP_CTX_CaseL Γ e1 e2 τ1 τ2 τ' :
     typed (τ1 :: Γ) e1 τ' → typed (τ2 :: Γ) e2 τ' →
     typed_ctx_item (CTX_CaseL e1 e2) Γ (TSum τ1 τ2) Γ τ'
  | TP_CTX_CaseM Γ e0 e2 τ1 τ2 τ' :
     typed Γ e0 (TSum τ1 τ2) → typed (τ2 :: Γ) e2 τ' →
     typed_ctx_item (CTX_CaseM e0 e2) (τ1 :: Γ) τ' Γ τ'
  | TP_CTX_CaseR Γ e0 e1 τ1 τ2 τ' :
     typed Γ e0 (TSum τ1 τ2) → typed (τ1 :: Γ) e1 τ' →
     typed_ctx_item (CTX_CaseR e0 e1) (τ2 :: Γ) τ' Γ τ'
  | TP_CTX_Fold Γ τ :
     typed_ctx_item CTX_Fold Γ τ.[(TRec τ)/] Γ (TRec τ)
  | TP_CTX_Unfold Γ τ :
     typed_ctx_item CTX_Unfold Γ (TRec τ) Γ τ.[(TRec τ)/]
  | TP_CTX_Cast Γ τi τf (pτf : Closed τf):
      consistency_open τi τf ->
      typed_ctx_item (CTX_Cast τi τf) Γ τi Γ τf.

(* We don't enforce the hole-type or output-type to be closed *)
(* But we do have that closeness of the hole-type implies closeness of the output type *)
(* We'll only fill in contexts with well-typed terms, so this is sufficient *)

Lemma typed_ctx_item_closedness k Γ τ Γ' τ' :
  Closed τ → typed_ctx_item k Γ τ Γ' τ' → Closed τ'.
Proof.
  intro pτ. destruct 1; try done.
  by apply TArrow_closed.
  by eapply TArrow_closed2.
  eapply TArrow_closed2. by eapply typed_closed.
  apply TProd_closed; auto. by eapply typed_closed.
  apply TProd_closed; auto.
    by eapply typed_closed.
  by eapply TProd_closed1.
  by eapply TProd_closed2.
  by eapply TSum_closed.
  by eapply TSum_closed.
    by eapply typed_closed.
  by apply closed_Fold_typed_help.
  by apply TRec_closed_unfold.
Qed.

Lemma typed_ctx_item_typed k Γ τ Γ' τ' e :
  typed Γ e τ → typed_ctx_item k Γ τ Γ' τ' →
  typed Γ' (fill_ctx_item k e) τ'.
Proof. induction 2; simpl; eauto using typed. Qed.

(** Typing derivation of general contexts *)
Inductive typed_ctx: ctx → list type → type → list type → type → Prop :=
  | TPCTX_nil Γ τ :
     typed_ctx nil Γ τ Γ τ
  | TPCTX_cons Γ1 τ1 Γ2 τ2 Γ3 τ3 k K :
     typed_ctx_item k Γ2 τ2 Γ3 τ3 →
     typed_ctx K Γ1 τ1 Γ2 τ2 →
     typed_ctx (k :: K) Γ1 τ1 Γ3 τ3.

Lemma typed_ctx_closedness K Γ τ Γ' τ' :
  Closed τ → typed_ctx K Γ τ Γ' τ' → Closed τ'.
Proof. induction 2. auto. eauto using typed_ctx_item_closedness. Qed.

Lemma typed_ctx_typed K Γ τ Γ' τ' e :
  typed Γ e τ → typed_ctx K Γ τ Γ' τ' → typed Γ' (fill_ctx K e) τ'.
Proof. induction 2; simpl; eauto using typed_ctx_item_typed. Qed.
