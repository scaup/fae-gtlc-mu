Require Export Utf8_core.
From iris.algebra Require Export base.

(* Definition iff := λ A B : Type, (A -> B)  (B -> A). *)
Definition TDecision : Type -> Type := λ P : Type, sum P (P -> False).

(* Definition TNeg : Type -> Type := λ P : Type, P → False. *)
