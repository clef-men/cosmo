From stdpp Require Export
  strings
  gmap
  binders.

From iris.algebra Require Import
  ofe.
From iris.algebra Require Export
  gmap
  frac.
From iris.program_logic Require Export
  language
  ectx_language
  ectxi_language.

From cosmo Require Import
  prelude.
From cosmo.language Require Export
  memory.

Implicit Types ℓ : location.

Open Scope Z_scope.

Inductive lit :=
  | LitLoc ℓ
  | LitInt (n : Z)
  | LitBool (b : bool)
  | LitUnit.
Implicit Types l : lit.

Inductive un_op :=
  | MinusUnOp
  | NotOp.

Inductive bin_op :=
  | PlusOp | MinusOp | MultOp | DivOp | ModOp
  | LeOp | EqOp
  | AndOp | OrOp.

Module base.
  Inductive expr :=
    | Val (v : val)
    | Var (x : string)
    | Rec (f x : binder) (e : expr)
    | App (e1 e2 : expr)
    | UnOp (op : un_op) (e: expr)
    | BinOp (op : bin_op) (e1 e2 : expr)
    | If (e0 e1 e2 : expr)
    | Pair (e1 e2 : expr)
    | Fst (e : expr)
    | Snd (e : expr)
    | InjL (e : expr)
    | InjR (e : expr)
    | Case (e0 : expr) (e1 : expr) (e2 : expr)
    | Read (α : atomicity) (eℓ ei : expr)
    | Write (α : atomicity) (eℓ ei e : expr)
    | CAS (eℓ ei e1 e2 : expr)
    | Length (eℓ : expr)
    | Alloc (α : atomicity) (ei e : expr)
    | Fork (e : expr)

  with val :=
    | LitV l
    | RecV (f x : binder) (e : expr)
    | PairV (v1 v2 : val)
    | InjLV (v : val)
    | InjRV (v : val).

  Bind Scope expr_scope with expr.
  Bind Scope val_scope with val.

  Implicit Types e eℓ ei : expr.
  Implicit Types v vℓ vi : val.
  Implicit Types α : atomicity.

  Notation of_val :=
    Val
  ( only parsing
  ).

  Definition to_val e : option val :=
    match e with
    | Val v => Some v
    | _ => None
    end.

  Lemma to_of_val v :
    to_val (of_val v) = Some v.
  Proof.
    by destruct v.
  Qed.

  Lemma of_to_val e v :
    to_val e = Some v →
    of_val v = e.
  Proof.
    destruct e=>//=. by intros [= <-].
  Qed.

  #[local] Instance of_val_inj :
    Inj (=) (=) of_val.
  Proof.
    intros ??. congruence.
  Qed.

  Inductive ectx_item :=
    | AppLCtx v2
    | AppRCtx e1
    | UnOpCtx (op : un_op)
    | BinOpLCtx (op : bin_op) v2
    | BinOpRCtx (op : bin_op) e1
    | IfCtx e1 e2
    | PairLCtx v2
    | PairRCtx e1
    | FstCtx
    | SndCtx
    | InjLCtx
    | InjRCtx
    | CaseCtx e1 e2
    | ReadLCtx α vi
    | ReadRCtx α eℓ
    | WriteLCtx α vi v
    | WriteMCtx α eℓ v
    | WriteRCtx α eℓ ei
    | CASLCtx vi v1 v2
    | CASICtx eℓ v1 v2
    | CASMCtx eℓ ei v2
    | CASRCtx eℓ ei e1
    | LengthCtx
    | AllocLCtx α v
    | AllocRCtx α ei.

  Implicit Types Ki : ectx_item.
  Implicit Types K : list ectx_item.

  Definition fill_item Ki e :=
    match Ki with
    | AppLCtx v2 =>
        App e (Val v2)
    | AppRCtx e1 =>
        App e1 e
    | UnOpCtx op =>
        UnOp op e
    | BinOpLCtx op v2 =>
        BinOp op e (Val v2)
    | BinOpRCtx op e1 =>
        BinOp op e1 e
    | IfCtx e1 e2 =>
        If e e1 e2
    | PairLCtx v2 =>
        Pair e (Val v2)
    | PairRCtx e1 =>
        Pair e1 e
    | FstCtx =>
        Fst e
    | SndCtx =>
        Snd e
    | InjLCtx =>
        InjL e
    | InjRCtx =>
        InjR e
    | CaseCtx e1 e2 =>
        Case e e1 e2
    | ReadLCtx α vi =>
        Read α e (Val vi)
    | ReadRCtx α eℓ =>
        Read α eℓ e
    | WriteLCtx α vi v =>
        Write α e (Val vi) (Val v)
    | WriteMCtx α eℓ v =>
        Write α eℓ e (Val v)
    | WriteRCtx α eℓ ei =>
        Write α eℓ ei e
    | CASLCtx vi v1 v2 =>
        CAS e (Val vi) (Val v1) (Val v2)
    | CASICtx eℓ v1 v2 =>
        CAS eℓ e (Val v1) (Val v2)
    | CASMCtx eℓ ei v2 =>
        CAS eℓ ei e (Val v2)
    | CASRCtx eℓ ei e1 =>
        CAS eℓ ei e1 e
    | LengthCtx =>
        Length e
    | AllocLCtx α v1 =>
        Alloc α e (Val v1)
    | AllocRCtx α en =>
        Alloc α en e
    end.

  Definition fill K e :=
    foldl (flip fill_item) e K.

  Fixpoint subst x v e :=
    match e with
    | Val _ =>
        e
    | Var y =>
        if bool_decide (x = y) then Val v else Var y
    | Rec f y e =>
        Rec f y $
        if bool_decide (BNamed x ≠ f ∧ BNamed x ≠ y) then subst x v e else e
    | App e1 e2 =>
        App (subst x v e1) (subst x v e2)
    | UnOp op e =>
        UnOp op (subst x v e)
    | BinOp op e1 e2 =>
        BinOp op (subst x v e1) (subst x v e2)
    | If e0 e1 e2 =>
        If (subst x v e0) (subst x v e1) (subst x v e2)
    | Pair e1 e2 =>
        Pair (subst x v e1) (subst x v e2)
    | Fst e =>
        Fst (subst x v e)
    | Snd e =>
        Snd (subst x v e)
    | InjL e =>
        InjL (subst x v e)
    | InjR e =>
        InjR (subst x v e)
    | Case e0 e1 e2 =>
        Case (subst x v e0) (subst x v e1) (subst x v e2)
    | Read α eℓ ei =>
        Read α (subst x v eℓ) (subst x v ei)
    | Write α eℓ ei e =>
        Write α (subst x v eℓ) (subst x v ei) (subst x v e)
    | CAS eℓ ei e1 e2 =>
        CAS (subst x v eℓ) (subst x v ei) (subst x v e1) (subst x v e2)
    | Length eℓ =>
        Length (subst x v eℓ)
    | Alloc α ei e =>
        Alloc α (subst x v ei) (subst x v e)
    | Fork e =>
        Fork (subst x v e)
    end.

  Definition subst' mx v :=
    match mx with BNamed x => subst x v | BAnon => id end.

  Notation store := (
    store (val := val)
  ).
  Notation mem_event := (
    mem_event (val := val)
  ).

  Implicit Types V : view.
  Implicit Types σ : store.

  Definition un_op_eval op l :=
    match op, l with
    | MinusUnOp, (LitInt z) =>
        Some $ LitInt (-z)
    | NotOp, (LitBool b) =>
        Some $ LitBool (negb b)
    | _, _ =>
        None
    end.

  Definition lit_eq l1 l2 :=
    match l1, l2 with
    | LitLoc ℓ1, LitLoc ℓ2 =>
        bool_decide (ℓ1 = ℓ2)
    | LitInt z1, LitInt z2 =>
        bool_decide (z1 = z2)
    | LitBool b1, LitBool b2 =>
        bool_decide (b1 = b2)
    | LitUnit, LitUnit =>
        true
    | _, _ =>
        false
    end.

  Definition lit_neq l1 l2 :=
    match l1, l2 with
    | LitLoc ℓ1, LitLoc ℓ2 =>
        bool_decide (ℓ1 ≠ ℓ2)
    | LitInt z1, LitInt z2 =>
        bool_decide (z1 ≠ z2)
    | LitBool b1, LitBool b2 =>
        bool_decide (b1 ≠ b2)
    | _, _ =>
        false
    end.

  Definition bin_op_eval op l1 l2 :=
    match op, l1, l2 with
    | PlusOp, LitInt z1, LitInt z2 =>
        Some $ LitInt (z1 + z2)
    | MinusOp, LitInt z1, LitInt z2 =>
        Some $ LitInt (z1 - z2)
    | MultOp, LitInt z1, LitInt z2 =>
        Some $ LitInt (z1 * z2)
    | DivOp, LitInt z1, LitInt z2 =>
        Some $ LitInt (z1 / z2)
    | ModOp, LitInt z1, LitInt z2 =>
        Some $ LitInt (z1 `mod` z2)
    | LeOp, LitInt z1, LitInt z2 =>
        Some $ LitBool $ bool_decide (z1 ≤ z2)
    | EqOp, _, _ =>
        match lit_eq l1 l2, lit_neq l1 l2 with
        | true, false => Some $ LitBool true
        | false, true => Some $ LitBool false
        | _, _ => None
        end
    | AndOp, LitBool b1, LitBool b2 =>
        Some $ LitBool (b1 && b2)
    | OrOp, LitBool b1, LitBool b2 =>
        Some $ LitBool (b1 || b2)
    | _, _, _ =>
        None
    end.

  Inductive head_step : expr → option mem_event → expr → list expr → Prop :=
    | RecS f x e :
       head_step (Rec f x e) None (Val $ RecV f x e) []
    | PairS v1 v2 :
       head_step (Pair (Val v1) (Val v2)) None (Val $ PairV v1 v2) []
    | InjLS v :
       head_step (InjL $ Val v) None (Val $ InjLV v) []
    | InjRS v :
       head_step (InjR $ Val v) None (Val $ InjRV v) []
    | BetaS f x e1 v2 e' :
       e' = subst' x v2 (subst' f (RecV f x e1) e1) →
       head_step (App (Val $ RecV f x e1) (Val v2)) None e' []
    | UnOpS op l l' :
        un_op_eval op l = Some l' →
        head_step (UnOp op (Val $ LitV l)) None (Val $ LitV l') []
    | BinOpS op l1 l2 l' :
        bin_op_eval op l1 l2 = Some l' →
        head_step (BinOp op (Val $ LitV l1) (Val $ LitV l2)) None (Val $ LitV l') []
    | IfTrueS e1 e2 :
       head_step (If (Val $ LitV $ LitBool true) e1 e2) None e1 []
    | IfFalseS e1 e2 :
       head_step (If (Val $ LitV $ LitBool false) e1 e2) None e2 []
    | FstS v1 v2 :
       head_step (Fst (Val $ PairV v1 v2)) None (Val v1) []
    | SndS v1 v2 :
       head_step (Snd (Val $ PairV v1 v2)) None (Val v2) []
    | CaseLS v e1 e2 :
       head_step (Case (Val $ InjLV v) e1 e2) None (App e1 (Val v)) []
    | CaseRS v e1 e2 :
       head_step (Case (Val $ InjRV v) e1 e2) None (App e2 (Val v)) []
    | ReadS α ℓ (i : Z) v :
        head_step (Read α (Val $ LitV $ LitLoc ℓ) (Val $ LitV $ LitInt i))
                  (Some $ mem_event_read α (Locoff ℓ i) v)
                  (Val v)
                  []
    | WriteNonAtomicS ℓ (i : Z) v :
        head_step (Write NonAtomic (Val $ LitV $ LitLoc ℓ) (Val $ LitV $ LitInt i) (Val v))
                  (Some $ mem_event_write_na (Locoff ℓ i) v)
                  (Val $ LitV $ LitUnit)
                  []
    | WriteAtomicS ℓ (i : Z) v0 v :
        head_step (Write Atomic (Val $ LitV $ LitLoc ℓ) (Val $ LitV $ LitInt i) (Val v))
                  (Some $ mem_event_update (Locoff ℓ i) v0 v)
                  (Val $ LitV $ LitUnit)
                  []
    | CASFailS ℓ (i : Z) lit0 lit1 v2 :
        lit_neq lit1 lit0 →
        head_step (CAS (Val $ LitV $ LitLoc ℓ) (Val $ LitV $ LitInt i) (Val $ LitV lit1) (Val v2))
                  (Some $ mem_event_read Atomic (Locoff ℓ i) (LitV lit0))
                  (Val $ LitV $ LitBool false)
                  []
    | CASSucS ℓ (i : Z) lit0 lit1 v2 :
        lit_eq lit1 lit0 →
        head_step (CAS (Val $ LitV $ LitLoc ℓ) (Val $ LitV $ LitInt i) (Val $ LitV lit1) (Val v2))
                  (Some $ mem_event_update (Locoff ℓ i) (LitV lit0) v2)
                  (Val $ LitV $ LitBool true)
                  []
    | LengthS ℓ (n : Z) :
        head_step (Length (Val $ LitV $ LitLoc ℓ))
                  (Some $ mem_event_length ℓ n)
                  (Val $ LitV $ LitInt n)
                  []
    | AllocS α (n : Z) v ℓ :
        head_step (Alloc α (Val $ LitV $ LitInt n) (Val v))
                  (Some $ mem_event_alloc α ℓ n v)
                  (Val $ LitV $ LitLoc ℓ)
                  []
    | ForkS e :
        head_step (Fork e)
                  None
                  (Val $ LitV $ LitUnit)
                  [e].

  #[local] Instance fill_item_inj Ki :
    Inj (=) (=) (fill_item Ki).
  Proof.
    destruct Ki; intros ???; simplify_eq/=; auto with f_equal.
  Qed.

  Lemma fill_item_val Ki e :
    is_Some (to_val (fill_item Ki e)) →
    is_Some (to_val e).
  Proof.
    intros [v ?]. destruct Ki; simplify_option_eq; eauto.
  Qed.

  Lemma val_head_stuck e1 evt e2 efs :
    head_step e1 evt e2 efs →
    to_val e1 = None.
  Proof.
    destruct 1; naive_solver.
  Qed.

  Lemma head_ctx_step_val Ki e evt e2 σ2 efs :
    head_step (fill_item Ki e) evt e2 efs →
    is_Some (to_val e).
  Proof.
    destruct Ki; inversion_clear 1; simplify_option_eq; eauto.
  Qed.

  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None →
    to_val e2 = None →
    fill_item Ki1 e1 = fill_item Ki2 e2 →
    Ki1 = Ki2.
  Proof.
    revert Ki1. induction Ki2, Ki1; naive_solver eauto with f_equal.
  Qed.

  #[global] Instance lit_dec_eq : EqDecision lit :=
    ltac:(solve_decision).
  #[global] Instance un_op_dec_eq : EqDecision un_op :=
    ltac:(solve_decision).
  #[global] Instance bin_op_dec_eq : EqDecision bin_op :=
    ltac:(solve_decision).
  #[global] Instance expr_eq_dec : EqDecision expr.
  Proof.
    refine (
     fix go e1 e2 {struct e1} : Decision (e1 = e2) :=
       match e1, e2 with
       | Val v, Val v' =>
           cast_if (decide (v = v'))
       | Var x, Var x' =>
           cast_if (decide (x = x'))
       | Rec f x e, Rec f' x' e' =>
          cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
       | App e1 e2, App e1' e2' =>
           cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
       | UnOp o e, UnOp o' e' =>
           cast_if_and (decide (o = o')) (decide (e = e'))
       | BinOp o e1 e2, BinOp o' e1' e2' =>
          cast_if_and3 (decide (o = o')) (decide (e1 = e1')) (decide (e2 = e2'))
       | If e0 e1 e2, If e0' e1' e2' =>
          cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
       | Pair e1 e2, Pair e1' e2' =>
          cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
       | Fst e, Fst e' =>
           cast_if (decide (e = e'))
       | Snd e, Snd e' =>
           cast_if (decide (e = e'))
       | InjL e, InjL e' =>
           cast_if (decide (e = e'))
       | InjR e, InjR e' =>
           cast_if (decide (e = e'))
       | Case e0 e1 e2, Case e0' e1' e2' =>
          cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
       | Read a eℓ ei, Read a' eℓ' ei' =>
          cast_if_and3 (decide (a = a')) (decide (eℓ = eℓ')) (decide (ei = ei'))
       | Write a eℓ ei e, Write a' eℓ' ei' e' =>
          cast_if_and4 (decide (a = a')) (decide (eℓ = eℓ')) (decide (ei = ei'))
            (decide (e = e'))
       | CAS eℓ ei e1 e2, CAS eℓ' ei' e1' e2' =>
          cast_if_and4 (decide (eℓ = eℓ')) (decide (ei = ei')) (decide (e1 = e1'))
            (decide (e2 = e2'))
       | Length e, Length e' =>
           cast_if (decide (e = e'))
       | Alloc a ei e, Alloc a' ei' e' =>
          cast_if_and3 (decide (a = a')) (decide (ei = ei')) (decide (e = e'))
       | Fork e, Fork e' =>
           cast_if (decide (e = e'))
       | _, _ =>
           right _
       end
     with gov (v1 v2 : val) {struct v1} : Decision (v1 = v2) :=
       match v1, v2 with
       | LitV l, LitV l' =>
           cast_if (decide (l = l'))
       | RecV f x e, RecV f' x' e' =>
          cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
       | PairV v1 v2, PairV v1' v2' =>
          cast_if_and (decide (v1 = v1')) (decide (v2 = v2'))
       | InjLV v, InjLV v' =>
           cast_if (decide (v = v'))
       | InjRV v, InjRV v' =>
           cast_if (decide (v = v'))
       | _, _ =>
           right _
       end
     for go);
     (clear go gov; abstract intuition congruence).
  Defined.
  #[global] Instance val_eq_dec : EqDecision val :=
    ltac:(solve_decision).

  #[global] Instance lit_countable :
    Countable lit.
  Proof.
    refine (inj_countable' (
      λ l,
        match l with
        | LitInt n =>
            inl (inl n)
        | LitBool b =>
            inl (inr b)
        | LitUnit =>
            inr (inl tt)
        | LitLoc l =>
            inr (inr l)
        end
  ) (
    λ x,
      match x with
      | inl (inl n) => LitInt n
      | inl (inr b) => LitBool b
      | inr (inl tt) => LitUnit
      | inr (inr l) => LitLoc l
      end
  ) _);
  by intros [].
  Qed.
  #[global] Instance un_op_countable :
    Countable un_op.
  Proof.
    refine (inj_countable' (
      λ op,
        match op with
        | MinusUnOp => 0
        | NotOp => 1
        end
    ) (
      λ n,
        match n with
        | 0 => MinusUnOp
        | _ => NotOp
    end) _);
    by intros [].
  Qed.
  #[global] Instance bin_op_countable :
    Countable bin_op.
  Proof.
    refine (inj_countable' (
      λ op,
        match op with
        | PlusOp => 0
        | MinusOp => 1
        | MultOp => 2
        | DivOp => 3
        | ModOp => 4
        | LeOp => 5
        | EqOp => 6
        | AndOp => 7
        | OrOp => 8
        end
    ) (
      λ n,
        match n with
        | 0 => PlusOp
        | 1 => MinusOp
        | 2 => MultOp
        | 3 => DivOp
        | 4 => ModOp
        | 5 => LeOp
        | 6 => EqOp
        | 7 => AndOp
        | _ => OrOp
        end
    ) _);
    by intros [].
  Qed.
  #[global] Instance expr_countable :
    Countable expr.
  Proof.
   set (enc :=
     fix go e :=
       match e with
       | Val v =>
           GenNode 0 [gov v]
       | Var x =>
           GenLeaf (inl (inl x))
       | Rec f x e =>
           GenNode 1 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); go e]
       | App e1 e2 =>
           GenNode 2 [go e1; go e2]
       | UnOp op e =>
           GenNode 3 [GenLeaf (inr (inr (inl op))); go e]
       | BinOp op e1 e2 =>
           GenNode 4 [GenLeaf (inr (inr (inr op))); go e1; go e2]
       | If e0 e1 e2 =>
           GenNode 5 [go e0; go e1; go e2]
       | Pair e1 e2 =>
           GenNode 6 [go e1; go e2]
       | Fst e =>
           GenNode 7 [go e]
       | Snd e =>
           GenNode 8 [go e]
       | InjL e =>
           GenNode 9 [go e]
       | InjR e =>
           GenNode 10 [go e]
       | Case e0 e1 e2 =>
           GenNode 11 [go e0; go e1; go e2]
       | Read a eℓ ei =>
           GenNode 12 [GenLeaf (inr (inl (inl a))); go eℓ; go ei]
       | Write a eℓ ei e =>
           GenNode 13 [GenLeaf (inr (inl (inl a))); go eℓ; go ei; go e]
       | CAS eℓ ei e1 e2 =>
           GenNode 14 [go eℓ; go ei; go e1; go e2]
       | Length e =>
           GenNode 15 [go e]
       | Alloc a ei e =>
           GenNode 16 [GenLeaf (inr (inl (inl a))); go ei; go e]
       | Fork e =>
           GenNode 17 [go e]
       end
     with gov v :=
       match v with
       | LitV l =>
           GenLeaf (inr (inl (inr l)))
       | RecV f x e =>
          GenNode 0 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); go e]
       | PairV v1 v2 =>
           GenNode 1 [gov v1; gov v2]
       | InjLV v =>
           GenNode 2 [gov v]
       | InjRV v =>
           GenNode 3 [gov v]
       end
     for go).
   set (dec :=
     fix go x :=
       match x with
       | GenNode 0 [v] =>
           Val (gov v)
       | GenLeaf (inl (inl x)) =>
           Var x
       | GenNode 1 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); e] =>
           Rec f x (go e)
       | GenNode 2 [e1; e2] =>
           App (go e1) (go e2)
       | GenNode 3 [GenLeaf (inr (inr (inl op))); e] =>
           UnOp op (go e)
       | GenNode 4 [GenLeaf (inr (inr (inr op))); e1; e2] =>
           BinOp op (go e1) (go e2)
       | GenNode 5 [e0; e1; e2] =>
           If (go e0) (go e1) (go e2)
       | GenNode 6 [e1; e2] =>
           Pair (go e1) (go e2)
       | GenNode 7 [e] =>
           Fst (go e)
       | GenNode 8 [e] =>
           Snd (go e)
       | GenNode 9 [e] =>
           InjL (go e)
       | GenNode 10 [e] =>
           InjR (go e)
       | GenNode 11 [e0; e1; e2] =>
           Case (go e0) (go e1) (go e2)
       | GenNode 12 [GenLeaf (inr (inl (inl a))); eℓ; ei] =>
           Read a (go eℓ) (go ei)
       | GenNode 13 [GenLeaf (inr (inl (inl a))); eℓ; ei; e] =>
           Write a (go eℓ) (go ei) (go e)
       | GenNode 14 [eℓ; ei; e1; e2] =>
           CAS (go eℓ) (go ei) (go e1) (go e2)
       | GenNode 15 [e] =>
           Length (go e)
       | GenNode 16 [GenLeaf (inr (inl (inl a))); ei; e] =>
           Alloc a (go ei) (go e)
       | GenNode 17 [e] =>
           Fork (go e)
       | _ =>
           Val $ LitV LitUnit
       end
     with gov x :=
       match x with
       | GenLeaf (inr (inl (inr l))) =>
           LitV l
       | GenNode 0 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); e] =>
           RecV f x (go e)
       | GenNode 1 [v1; v2] =>
           PairV (gov v1) (gov v2)
       | GenNode 2 [v] =>
           InjLV (gov v)
       | GenNode 3 [v] =>
           InjRV (gov v)
       | _ =>
           LitV LitUnit
       end
     for go).
   refine (inj_countable' enc dec _).
   refine (fix go (e : expr) {struct e} := _ with gov (v : val) {struct v} := _ for go).
   - destruct e as [v| | | | | | | | | | | | | | | | | |];
       simpl; f_equal; [exact (gov v) | done..].
   - destruct v; by f_equal.
  Qed.
  #[global] Instance val_countable :
    Countable val.
  Proof.
    refine (inj_countable of_val to_val _); auto using to_of_val.
  Qed.

  #[global] Instance val_inhabited : Inhabited val :=
    populate (LitV LitUnit).
  #[global] Instance expr_inhabited : Inhabited expr :=
    populate (Val inhabitant).

  Notation locO :=
    positiveO.
  Canonical exprO :=
    leibnizO expr.
  Canonical valO :=
    leibnizO val.
  Notation viewO := (
    gmapO locoff fracO
  ).
  Notation valViewO := (
    prodO valO viewO
  ).

  Lemma ectxi_lang_mixin :
    EctxiLanguageMixin (state := unit) (observation := Empty_set)
      of_val to_val fill_item
      (fun e _ _ e' _ efs => False).
  Proof.
    split; eauto using to_of_val, of_to_val, fill_item_val,
      fill_item_no_val_inj, head_ctx_step_val with typeclass_instances=>//.
  Qed.

  Definition ectxi_lang :=
    EctxiLanguage ectxi_lang_mixin.
  Definition ectx_lang :=
    EctxLanguageOfEctxi ectxi_lang.
  Canonical lang :=
    LanguageOfEctx ectx_lang.

  Class AtomicExpr e :=
    atomic :
      match e with
      | Read _ (Val _) (Val _)
      | Write _ (Val _) (Val _) (Val _)
      | CAS (Val _) (Val _) (Val _) (Val _)
      | Length (Val _)
      | Alloc _ (Val _) (Val _)
      | Fork _
      | App (Val (RecV BAnon BAnon (Val (LitV LitUnit)))) (Val (LitV LitUnit)) =>
          True
      | _ =>
          False
      end.
  Opaque AtomicExpr.

  #[local] Hint Extern 1 (
    AtomicExpr _
  ) =>
    exact I
  : typeclass_instances.
End base.

Export base.

Module view_lang.
  Record expr : Type := mkExpr {
    expr_expr :> base.expr ;
    expr_view : view ;
  }.
  Record val : Type := mkVal {
    val_val :> base.val ;
    val_view : view ;
  }.
  Definition ectx_item :=
    ectx_item.
  Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
    mkExpr (fill_item Ki e) e.(expr_view).
  Definition of_val (v : val) :=
    mkExpr (of_val v) v.(val_view).
  Definition to_val e :=
    (λ v, mkVal v e.(expr_view)) <$> to_val e.

  Definition subst x es (e : expr) :=
    mkExpr (subst x es e) (expr_view e).

  Inductive head_step : expr → store → list Empty_set → expr → store → list expr → Prop :=
  | pure_step e V σ e' efs :
      base.head_step e None e' (expr_expr <$> efs) →
      Forall (eq V) (expr_view <$> efs) →
      head_step (mkExpr e V) σ [] (mkExpr e' V) σ efs
  | impure_step e V σ evt e' V' σ' :
      base.head_step e (Some evt) e' [] →
      mem_step σ V evt σ' V' →
      head_step (mkExpr e V) σ [] (mkExpr e' V') σ' [].
  Arguments head_step _%E _ _ _%E _ _%E.

  Lemma head_step_view_sqsubseteq e V σ κs e' V' σ' ef (STEP: head_step (mkExpr e V) σ κs (mkExpr e' V') σ' ef) :
    V ⊑ V'.
  Proof.
    inversion STEP; first done. subst.
    match goal with H : mem_step _ _ _ _ _ |- _ => destruct H; try solve_lat end.
    intros ℓi'. case (decide (ℓi = ℓi')) => [ <- | ? ] ;
      [ rewrite lookup_insert | by rewrite lookup_insert_ne ].
    by subst.
  Qed.

  Lemma to_of_val v :
    to_val (of_val v) = Some v.
  Proof.
    by destruct v.
  Qed.

  Lemma of_to_val e v :
    to_val e = Some v →
    of_val v = e.
  Proof.
    by destruct e as [[] ?]=>// [= <-] //.
  Qed.

  #[local] Instance of_val_inj :
    Inj (=) (=) of_val.
  Proof.
    by intros [][][=-> ->].
  Qed.

  #[local] Instance fill_item_inj Ki :
    Inj (=) (=) (fill_item Ki).
  Proof.
    by intros [][][= ->%fill_item_inj ->].
  Qed.

  Lemma fill_item_val Ki e :
    is_Some (to_val (fill_item Ki e)) →
    is_Some (to_val e).
  Proof.
    move/fmap_is_Some/fill_item_val => H. exact/fmap_is_Some.
  Qed.

  Lemma val_stuck σ1 e1 κs σ2 e2 ef :
    head_step e1 σ1 κs e2 σ2 ef →
    to_val e1 = None.
  Proof.
    by inversion 1; subst;
      match goal with H : base.head_step _ _ _ _ |- _ => inversion H end.
  Qed.

  Lemma head_ctx_step_val Ki e σ κs e2 σ2 ef :
    head_step (fill_item Ki e) σ κs e2 σ2 ef →
    is_Some (to_val e).
  Proof.
    inversion 1; subst; apply fmap_is_Some; exact: head_ctx_step_val.
  Qed.

  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None →
    to_val e2 = None →
    fill_item Ki1 e1 = fill_item Ki2 e2 →
    Ki1 = Ki2.
  Proof.
    move => /fmap_None H1 /fmap_None H2 [] H3 ?.
    exact: fill_item_no_val_inj H1 H2 H3.
  Qed.

  Lemma view_ectxi_lang_mixin :
    EctxiLanguageMixin of_val to_val fill_item head_step.
  Proof.
    split; eauto using to_of_val, of_to_val, val_stuck, fill_item_val,
      fill_item_no_val_inj, head_ctx_step_val with typeclass_instances.
  Qed.
End view_lang.

Notation mkExpr :=
  view_lang.mkExpr.
Notation mkVal :=
  view_lang.mkVal.
Coercion view_lang.expr_expr : view_lang.expr >-> expr.
Coercion view_lang.val_val : view_lang.val >-> val.

Canonical view_ectxi_lang :=
  EctxiLanguage view_lang.view_ectxi_lang_mixin.
Canonical view_ectx_lang :=
  EctxLanguageOfEctxi view_ectxi_lang.
Canonical view_lang :=
  LanguageOfEctx view_ectx_lang.

#[global] Instance base_atomic_atomic e V a :
  AtomicExpr e →
  language.Atomic a (view_lang.mkExpr e V).
Proof.
  intros He. apply strongly_atomic_atomic, (@ectx_language_atomic view_ectx_lang).
  - intros σ κs [e' V'] σ' ef. cbn. move => STEP. apply/fmap_is_Some.
    destruct e=>//=; simpl in He; repeat (case_match; try done);
    inversion STEP;
      (match goal with H : base.head_step _ _ _ _ |- _ => inversion H end);
      subst; rewrite ?to_of_val; eauto.
  - apply (@ectxi_language_sub_redexes_are_values view_ectxi_lang)=> /= Ki [e' ?] Hfill.
    apply/fmap_is_Some. revert He. inversion Hfill as [Hfill']; subst; clear Hfill.
    destruct Ki=>//=; repeat case_match=>//; naive_solver.
Qed.

Lemma fill_base_view (K : list view_lang.ectx_item) e V :
  mkExpr (fill K e) V = ectxi_language.fill K (mkExpr e V).
Proof.
  revert e. induction K; intros ?; [done|apply IHK].
Qed.
