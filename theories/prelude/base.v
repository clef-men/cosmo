From Coq.ssr Require Export
  ssreflect.

From stdpp Require Export
  prelude.

#[export] Set Default Proof Using "Type*".
#[export] Set Suggest Proof Using.

Open Scope general_if_scope.

Infix "⊓@{ A }" := (@meet A _)
( at level 40,
  only parsing
) : stdpp_scope.
Notation "(⊓@{ A } )" := (@meet A _)
( only parsing
) : stdpp_scope.

Infix "⊔@{ A }" := (@join A _)
( at level 50,
  only parsing
) : stdpp_scope.
Notation "(⊔@{ A } )" := (@join A _)
( only parsing
) : stdpp_scope.
