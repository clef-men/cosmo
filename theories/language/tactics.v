From cosmo Require Import
  prelude.
From cosmo.language Require Export
  lang.

Ltac reshape_expr e tac :=
  let rec go K e :=
    match e with
    | _ =>
        tac K e
    | App ?e (Val ?v) =>
        go (AppLCtx v :: K) e
    | App ?e1 ?e2 =>
        go (AppRCtx e1 :: K) e2
    | UnOp ?op ?e =>
        go (UnOpCtx op :: K) e
    | BinOp ?op ?e (Val ?v) =>
        go (BinOpLCtx op v :: K) e
    | BinOp ?op ?e1 ?e2 =>
        go (BinOpRCtx op e1 :: K) e2
    | If ?e0 ?e1 ?e2 =>
        go (IfCtx e1 e2 :: K) e0
    | Pair ?e (Val ?v) =>
        go (PairLCtx v :: K) e
    | Pair ?e1 ?e2 =>
        go (PairRCtx e1 :: K) e2
    | Fst ?e =>
        go (FstCtx :: K) e
    | Snd ?e =>
        go (SndCtx :: K) e
    | InjL ?e =>
        go (InjLCtx :: K) e
    | InjR ?e =>
        go (InjRCtx :: K) e
    | Case ?e0 ?e1 ?e2 =>
        go (CaseCtx e1 e2 :: K) e0
    | Read ?a ?eℓ (Val ?vi) =>
        go (ReadLCtx a vi :: K) eℓ
    | Read ?a ?eℓ ?ei =>
        go (ReadRCtx a eℓ :: K) ei
    | Write ?a ?eℓ (Val ?vi) (Val ?v) =>
        go (WriteLCtx a vi v :: K) eℓ
    | Write ?a ?eℓ ?ei (Val ?v) =>
        go (WriteMCtx a eℓ v :: K) ei
    | Write ?a ?eℓ ?ei ?e =>
        go (WriteRCtx a eℓ ei :: K) e
    | CAS ?eℓ (Val ?vi) (Val ?v1) (Val ?v2) =>
        go (CASLCtx vi v1 v2 :: K) eℓ
    | CAS ?eℓ ?ei (Val ?v1) (Val ?v2) =>
        go (CASICtx eℓ v1 v2 :: K) ei
    | CAS ?eℓ ?ei ?e1 (Val ?v2) =>
        go (CASMCtx eℓ ei v2 :: K) e1
    | CAS ?eℓ ?ei ?e1 ?e2 =>
        go (CASRCtx eℓ ei e1 :: K) e2
    | Length ?eℓ =>
        go (LengthCtx :: K) eℓ
    | Alloc ?a ?ei (Val ?v) =>
        go (AllocLCtx a v :: K) ei
    | Alloc ?a ?ei ?e =>
        go (AllocRCtx a ei :: K) e
    end
  in
  go (@nil ectx_item) e.
