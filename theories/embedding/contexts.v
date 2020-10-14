From fae_gtlc_mu.stlc_mu Require lang contexts.
From fae_gtlc_mu.cast_calculus Require Import lang contexts.
From fae_gtlc_mu.embedding Require Import expressions.

Reserved Notation "[{ C }]" (at level 4, C at next level).
Fixpoint embed_ctx_item (C : stlc_mu.contexts.ctx_item) : ctx_item :=
  match C with
  | stlc_mu.contexts.CTX_Lam => CTX_Lam
  | stlc_mu.contexts.CTX_AppL e2 => CTX_AppL [[e2]]
  | stlc_mu.contexts.CTX_AppR e1 => CTX_AppR [[e1]]
  | stlc_mu.contexts.CTX_PairL e2 => CTX_PairL [[e2]]
  | stlc_mu.contexts.CTX_PairR e1 => CTX_PairR [[e1]]
  | stlc_mu.contexts.CTX_Fst => CTX_Fst
  | stlc_mu.contexts.CTX_Snd => CTX_Snd
  | stlc_mu.contexts.CTX_InjL => CTX_InjL
  | stlc_mu.contexts.CTX_InjR => CTX_InjR
  | stlc_mu.contexts.CTX_CaseL e1 e2 => CTX_CaseL [[e1]] [[e2]]
  | stlc_mu.contexts.CTX_CaseM e0 e2 => CTX_CaseM [[e0]] [[e2]]
  | stlc_mu.contexts.CTX_CaseR e0 e1 => CTX_CaseR [[e0]] [[e1]]
  | stlc_mu.contexts.CTX_Fold => CTX_Fold
  | stlc_mu.contexts.CTX_Unfold => CTX_Unfold
  end where "[{ C }]" := (embed_ctx_item C).

Definition embed_ctx (C : stlc_mu.contexts.ctx) : ctx := map embed_ctx_item C.
