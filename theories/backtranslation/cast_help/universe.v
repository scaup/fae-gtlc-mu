From fae_gtlc_mu Require Export stlc_mu.lang.
From fae_gtlc_mu Require Export stlc_mu.typing.

Infix "→" := TArrow : type_scope.

Definition Universe_body : type :=
  (
    TUnit +
    (TVar 0 + TVar 0) +
    (TVar 0 × TVar 0) +
    (TVar 0 → TVar 0) +
    (TVar 0)
  )%type.

(* + is left associative; (a + b + c) = ((a + b) + c) *)

Definition Universe : type :=
  TRec Universe_body.

Definition Universe_unfolded : type :=
  Universe_body.[Universe/]%type.

(* Coercion App : expr >-> Funclass. *)
