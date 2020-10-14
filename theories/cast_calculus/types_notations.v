From fae_gtlc_mu.cast_calculus Require Export types.

Declare Scope types_scope.

Notation "⋆" := TUnknown.
Infix "×" := TProd (at level 150) : types_scope.
Infix "+" := TSum : types_scope.

Delimit Scope types_scope with types.
