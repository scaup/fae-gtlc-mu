From fae_gtlc_mu.cast_calculus Require Import lang contexts consistency consistency_lemmas.
From fae_gtlc_mu.backtranslation Require Import cast_help.general_def implication_consistencies.proof expressions.
From fae_gtlc_mu.stlc_mu Require Import lang contexts.
From fae_gtlc_mu.cast_calculus Require Import types.

(* This file naturally extends the backtranslation on expressions to one on contexts *)

(* To contexts of depth 1 *)
Reserved Notation "<{ C }>" (at level 4, C at next level).
Fixpoint backtranslate_ctx_item (C : cast_calculus.contexts.ctx_item) : ctx_item :=
  match C with
  (* uninteresting cases *)
  | cast_calculus.contexts.CTX_Lam => CTX_Lam
  | cast_calculus.contexts.CTX_AppL e2 => CTX_AppL <<<e2>>>
  | cast_calculus.contexts.CTX_AppR e1 => CTX_AppR <<<e1>>>
  | cast_calculus.contexts.CTX_PairL e2 => CTX_PairL <<<e2>>>
  | cast_calculus.contexts.CTX_PairR e1 => CTX_PairR <<<e1>>>
  | cast_calculus.contexts.CTX_Fst => CTX_Fst
  | cast_calculus.contexts.CTX_Snd => CTX_Snd
  | cast_calculus.contexts.CTX_InjL => CTX_InjL
  | cast_calculus.contexts.CTX_InjR => CTX_InjR
  | cast_calculus.contexts.CTX_CaseL e1 e2 => CTX_CaseL <<<e1>>> <<<e2>>>
  | cast_calculus.contexts.CTX_CaseM e0 e2 => CTX_CaseM <<<e0>>> <<<e2>>>
  | cast_calculus.contexts.CTX_CaseR e0 e1 => CTX_CaseR <<<e0>>> <<<e1>>>
  | cast_calculus.contexts.CTX_Fold => CTX_Fold
  | cast_calculus.contexts.CTX_Unfold => CTX_Unfold
  (* interesting case of cast *)
  (* We assume τi and τf to be consistent here (see typing rule for casts). *)
  (* We assume τi and τf are meaningful; i.e. they do not contain open variables. *)
  | CTX_Cast τi τf => match (consistency_open_dec τi τf, decide (Closed τi) , decide (Closed τf)) with
                     | (inleft pC , left pi, left pf) => CTX_AppR (𝓕c (proof.cons_co τi pi τf pf pC) [])
                     (* Here, we need to convert our proof of conventional consistency (pC) into a proof of alternative consistency (proof.cons_co τi pi τf pf pC). *)
                     | _ => CTX_Lam
                     (* Just some random value; we only care about the backtranslation of well-typed contexts. *)
                     end
  end where "<{ C }>" := (backtranslate_ctx_item C).

(* To general contexts *)
Definition backtranslate_ctx (C : cast_calculus.contexts.ctx) : ctx := map backtranslate_ctx_item C.
