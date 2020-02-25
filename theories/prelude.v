Require Export Utf8_core.
From iris.algebra Require Export base.

(* Definition iff := λ A B : Type, (A -> B)  (B -> A). *)
Definition TDecision : Type -> Type := λ P : Type, sum P (P -> False).

(* Definition TNeg : Type -> Type := λ P : Type, P → False. *)

From Autosubst Require Export Autosubst.

Section Autosubst_Lemmas.
  Context {term : Type} {Ids_term : Ids term}
          {Rename_term : Rename term} {Subst_term : Subst term}
          {SubstLemmas_term : SubstLemmas term}.

  Lemma iter_up (m x : nat) (f : var → term) :
    upn m f x = if lt_dec x m then ids x else rename (+m) (f (x - m)).
  Proof.
    revert x; induction m as [|m IH]=> -[|x];
      repeat (destruct (lt_dec _ _) || asimpl || rewrite IH); auto with lia.
  Qed.
End Autosubst_Lemmas.

Inductive ForallT {A : Type} (P : A → Type) : list A → Type :=
    ForallT_nil : ForallT P []
  | ForallT_cons : ∀ (x : A) (l : list A), P x → ForallT P l → ForallT P (x :: l).

Lemma rewrite_for_context_weakening {A} (Γ : list A) τ : τ :: Γ = [τ] ++ Γ.
by simpl.
Qed.

Definition update {A : Type} (l : list A) (i : nat) (a : A) : list A :=
  alter (fun _ => a) i l.
