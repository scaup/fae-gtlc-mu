From fae_gtlc_mu.cast_calculus Require Import lang contexts.
From fae_gtlc_mu.stlc_mu Require Import lang contexts.
From fae_gtlc_mu.backtranslation Require Import cast_help.general expressions.

Reserved Notation "<{ C }>" (at level 4, C at next level).
Fixpoint backtranslate_ctx_item (C : cast_calculus.contexts.ctx_item) : ctx_item :=
  match C with
  | cast_calculus.contexts.CTX_Lam => CTX_Lam
  | cast_calculus.contexts.CTX_AppL e2 => CTX_AppL <<e2>>
  | cast_calculus.contexts.CTX_AppR e1 => CTX_AppR <<e1>>
  | cast_calculus.contexts.CTX_PairL e2 => CTX_PairL <<e2>>
  | cast_calculus.contexts.CTX_PairR e1 => CTX_PairR <<e1>>
  | cast_calculus.contexts.CTX_Fst => CTX_Fst
  | cast_calculus.contexts.CTX_Snd => CTX_Snd
  | cast_calculus.contexts.CTX_InjL => CTX_InjL
  | cast_calculus.contexts.CTX_InjR => CTX_InjR
  | cast_calculus.contexts.CTX_CaseL e1 e2 => CTX_CaseL <<e1>> <<e2>>
  | cast_calculus.contexts.CTX_CaseM e0 e2 => CTX_CaseM <<e0>> <<e2>>
  | cast_calculus.contexts.CTX_CaseR e0 e1 => CTX_CaseR <<e0>> <<e1>>
  | cast_calculus.contexts.CTX_Fold => CTX_Fold
  | cast_calculus.contexts.CTX_Unfold => CTX_Unfold
  | CTX_Cast τi τf => match (cons_stand_dec τi τf, decide (TClosed τi) , decide (TClosed τf)) with
                     | (inl pC , left pi, left pf) => CTX_AppR (𝓕c (cons_co τi pi τf pf pC) [])
                     | _ => CTX_Lam
                     end
  end where "<{ C }>" := (backtranslate_ctx_item C).

Definition backtranslate_ctx (C : cast_calculus.contexts.ctx) : ctx := map backtranslate_ctx_item C.
