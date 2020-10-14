From fae_gtlc_mu.stlc_mu Require Export types.

Declare Scope types_scope.

Infix "×" := TProd (at level 150) : types_scope.
Infix "+" := TSum : types_scope.

Delimit Scope types_scope with types.
