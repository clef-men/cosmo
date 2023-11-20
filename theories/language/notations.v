From cosmo Require Import
  prelude.
From cosmo.language Require Export
  lang.

Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Notation "e 'at' V" := (
  mkExpr e V
)(at level 180
) : expr_scope.
Notation "v 'at' V" := (
  mkVal v V
)(at level 180
) : val_scope.

Coercion LitLoc : location >-> lit.
Coercion LitInt : Z >-> lit.
Coercion LitBool : bool >-> lit.

Coercion App : expr >-> Funclass.

Coercion Val : val >-> expr.
Coercion Var : string >-> expr.

Notation Lam x e := (
  Rec BAnon x e
)(only parsing
).
Notation Let x e1 e2 := (
  App (Lam x e2) e1
)(only parsing
).
Notation Seq e1 e2 := (
  Let BAnon e1 e2
)(only parsing
).
Notation LamV x e := (
  RecV BAnon x e
)(only parsing
).
Notation LetCtx x e2 := (
  AppRCtx (LamV x e2)
)(only parsing
).
Notation SeqCtx e2 := (
  LetCtx BAnon e2
)(only parsing
).
Notation Match e0 x1 e1 x2 e2 := (
  Case e0 (Lam x1 e1) (Lam x2 e2)
)(only parsing
).

Notation Skip := (
  App (Val $ LamV BAnon (Val $ LitV LitUnit)) (Val $ LitV LitUnit)
).

Notation "# l" := (
  LitV l%Z%V%stdpp
)(at level 8,
  format "# l"
).

Notation "( e1 , e2 , .. , en )" := (
  Pair .. (Pair e1 e2) .. en
) : expr_scope.
Notation "( e1 , e2 , .. , en )" := (
  PairV .. (PairV e1 e2) .. en
) : val_scope.

Notation "'match:' e0 'with' 'InjL' x1 => e1 | 'InjR' x2 => e2 'end'" := (
  Match e0 x1%binder e1 x2%binder e2
)(e0, x1, e1, x2, e2 at level 200,
  format "'[hv' 'match:'  e0  'with'  '/  ' '[' 'InjL'  x1  =>  '/  ' e1 ']'  '/' '[' |  'InjR'  x2  =>  '/  ' e2 ']'  '/' 'end' ']'"
) : expr_scope.
Notation "'match:' e0 'with' | 'InjL' x1 => e1 | 'InjR' x2 => e2 'end'" := (
  Match e0 x1%binder e1 x2%binder e2
)(only parsing,
  e0, x1, e1, x2, e2 at level 200
) : expr_scope.
Notation "'match:' e0 'with' 'InjR' x1 => e1 | 'InjL' x2 => e2 'end'" := (
  Match e0 x2%binder e2 x1%binder e1
)(only parsing,
  e0, x1, e1, x2, e2 at level 200
) : expr_scope.
Notation "'match:' e0 'with' | 'InjR' x1 => e1 | 'InjL' x2 => e2 'end'" := (
  Match e0 x2%binder e2 x1%binder e1
)(only parsing,
  e0, x1, e1, x2, e2 at level 200
) : expr_scope.

Notation "()" :=
  LitUnit
: val_scope.

Notation "'ref' e" := (
  Alloc NonAtomic (Val $ LitV $ LitInt 1) e%E
)(at level 10
) : expr_scope.
Notation "! e" := (
  Read NonAtomic e%E (Val $ LitV $ LitInt 0)
)(at level 9,
  right associativity
) : expr_scope.
Notation "e1 <- e2" := (
  Write NonAtomic e1%E (Val $ LitV $ LitInt 0) e2%E
)(at level 80
) : expr_scope.

Notation "'ref_at' e" := (
  Alloc Atomic (Val $ LitV $ LitInt 1) e%E
)(at level 10
) : expr_scope.
Notation "!at e" := (
  Read Atomic e%E (Val $ LitV $ LitInt 0)
)(at level 9,
  right associativity
) : expr_scope.
Notation "e1 <-at e2" := (
  Write Atomic e1%E (Val $ LitV $ LitInt 0) e2%E
)(at level 80
) : expr_scope.

Notation CAS_ref e1 e2 e3 := (
  CAS e1 (Val $ LitV $ LitInt 0) e2 e3
).

Notation "- e" := (
  UnOp MinusUnOp e%E
) : expr_scope.
Notation "¬ e" := (
  UnOp NotOp e%E
)%E : expr_scope.

Notation "e1 + e2" := (
  BinOp PlusOp e1%E e2%E
) : expr_scope.
Notation "e1 - e2" := (
  BinOp MinusOp e1%E e2%E
) : expr_scope.
Notation "e1 * e2" := (
  BinOp MultOp e1%E e2%E
) : expr_scope.
Notation "e1 / e2" := (
  BinOp DivOp e1%E e2%E
) : expr_scope.
Notation "e1 `mod` e2" := (
  BinOp ModOp e1%E e2%E
) : expr_scope.
Notation "e1 ≤ e2" := (
  BinOp LeOp e1%E e2%E
) : expr_scope.
Notation "e1 = e2" := (
  BinOp EqOp e1%E e2%E
) : expr_scope.
Notation "e1 ≠ e2" := (
  ¬ (e1%E = e2%E)
)%E : expr_scope.
Notation "e1 ∧ e2" := (
  BinOp AndOp e1%E e2%E
) : expr_scope.
Notation "e1 ∨ e2" := (
  BinOp OrOp e1%E e2%E
) : expr_scope.

Notation "e1 && e2" := (
  If e1%E e2%E (LitV (LitBool false))
)(only parsing
) : expr_scope.
Notation "e1 || e2" := (
  If e1%E (LitV (LitBool true)) e2%E
)(only parsing
) : expr_scope.

Notation "'rec:' f x := e" := (
  Rec f%binder x%binder e%E
)(at level 200,
  f at level 1,
  x at level 1,
  e at level 200,
  format "'[' 'rec:'  f  x  :=  '/  ' e ']'"
) : expr_scope.
Notation "'rec:' f x := e" := (
  RecV f%binder x%binder e%E
)(at level 200,
  f at level 1,
  x at level 1, e
  at level 200,
  format "'[' 'rec:'  f  x  :=  '/  ' e ']'"
) : val_scope.
Notation "'if:' e1 'then' e2 'else' e3" := (
  If e1%E e2%E e3%E
)(at level 200,
  e1, e2, e3 at level 200
) : expr_scope.

Notation "'rec:' f x y .. z := e" := (
  Rec f%binder x%binder (Lam y%binder .. (Lam z%binder e%E) ..)
)(at level 200,
  f, x, y, z at level 1,
  e at level 200,
  format "'[' 'rec:'  f  x  y  ..  z  :=  '/  ' e ']'"
) : expr_scope.
Notation "'rec:' f x y .. z := e" := (
  RecV f%binder x%binder (Lam y%binder .. (Lam z%binder e%E) ..)
)(at level 200, f, x, y, z at level 1,
  e at level 200,
  format "'[' 'rec:'  f  x  y  ..  z  :=  '/  ' e ']'"
) : val_scope.

Notation "λ: x , e" := (
  Lam x%binder e%E
)(at level 200,
  x at level 1,
  e at level 200,
  format "'[' 'λ:'  x ,  '/  ' e ']'"
) : expr_scope.
Notation "λ: x y .. z , e" := (
  Lam x%binder (Lam y%binder .. (Lam z%binder e%E) ..)
)(at level 200,
  x, y, z at level 1,
  e at level 200,
  format "'[' 'λ:'  x  y  ..  z ,  '/  ' e ']'"
) : expr_scope.

Notation "λ: x , e" := (
  LamV x%binder e%E
)(at level 200,
  x at level 1,
  e at level 200,
  format "'[' 'λ:'  x ,  '/  ' e ']'"
) : val_scope.
Notation "λ: x y .. z , e" := (
  LamV x%binder (Lam y%binder .. (Lam z%binder e%E) .. )
)(at level 200,
  x, y, z at level 1,
  e at level 200,
  format "'[' 'λ:'  x  y  ..  z ,  '/  ' e ']'"
) : val_scope.

Notation "'let:' x := e1 'in' e2" := (
  Lam x%binder e2%E e1%E
)(at level 200,
  x at level 1,
  e1, e2 at level 200,
  format "'[' 'let:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'"
) : expr_scope.
Notation "e1 ;; e2" := (
  Lam BAnon e2%E e1%E
)(at level 100,
  e2 at level 200,
  format "'[' '[hv' '[' e1 ']'  ;;  ']' '/' e2 ']'"
) : expr_scope.

Notation NONE := (
  InjL (LitV LitUnit)
)(only parsing
).
Notation NONEV := (
  InjLV (LitV LitUnit)
)(only parsing
).
Notation SOME x := (
  InjR x
)(only parsing
).
Notation SOMEV x := (
  InjRV x
)(only parsing
).

Notation "'match:' e0 'with' 'NONE' => e1 | 'SOME' x => e2 'end'" := (
  Match e0 BAnon e1 x%binder e2
)(only parsing,
  e0, e1, x, e2 at level 200
) : expr_scope.
Notation "'match:' e0 'with' | 'NONE' => e1 | 'SOME' x => e2 'end'" := (
  Match e0 BAnon e1 x%binder e2
)(only parsing,
  e0, e1, x, e2 at level 200
) : expr_scope.
Notation "'match:' e0 'with' 'SOME' x => e2 | 'NONE' => e1 'end'" := (
  Match e0 BAnon e1 x%binder e2
)(only parsing,
  e0, e1, x, e2 at level 200
) : expr_scope.
Notation "'match:' e0 'with' | 'SOME' x => e2 | 'NONE' => e1 'end'" := (
  Match e0 BAnon e1 x%binder e2
)(only parsing,
  e0, e1, x, e2 at level 200
) : expr_scope.
