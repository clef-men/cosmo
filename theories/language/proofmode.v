From iris.bi Require Export
  weakestpre.
From iris.proofmode Require Import
  coq_tactics
  reduction
  string_ident.
From iris.proofmode Require Export
  tactics.

From cosmo Require Import
  prelude.
From cosmo.common Require Import
  list.
From cosmo.language Require Export
  weakestpre
  lifting
  store
  notations
  tactics.
From cosmo.language Require Import
  atomic.

Open Scope Z.

Section collect_monPred_in.
  Context {Σ : gFunctors}.

  Class CollectMonPredInEnv (Γ : env (vProp Σ)) (V : view) : Prop :=
    collect_monPred_in_env : [∧] Γ ⊢ monPred_in V.

  #[global] Instance collect_monPred_in_cons_here Γ i V1 V2 :
    CollectMonPredInEnv Γ V2  →
    CollectMonPredInEnv (Esnoc Γ i (monPred_in V1)) (V1 ⊔ V2) | 1 .
  Proof. rewrite /CollectMonPredInEnv /= => ->. iIntros "[??]". by iSplit. Qed.
  #[global] Instance collect_monPred_in_env_cons_first Γ i V :
    CollectMonPredInEnv (Esnoc Γ i (monPred_in V)) V | 2.
  Proof. by rewrite /CollectMonPredInEnv /= bi.and_elim_l. Qed.
  #[global] Instance collect_monPred_in_cons Γ i V P :
    CollectMonPredInEnv Γ V  →
    CollectMonPredInEnv (Esnoc Γ i P) V | 100.
  Proof. by rewrite /CollectMonPredInEnv /= bi.and_elim_r. Qed.

  Class CollectMonPredIn (Δ : envs (vPropI Σ)) (V : view) : Prop :=
    collect_monPred_in : of_envs Δ ⊢ monPred_in V.

  #[global] Instance collect_monPred_in_envs Δ V:
    CollectMonPredInEnv Δ.(env_intuitionistic) V →
    CollectMonPredIn Δ V.
  Proof.
    rewrite /CollectMonPredInEnv /CollectMonPredIn of_envs_eq -big_andL_persistently => <-.
    iIntros "[_ [#$ _]]".
  Qed.
  #[global] Instance collect_monPred_in_empty Δ:
    CollectMonPredIn Δ ∅ | 100.
  Proof.
    rewrite /CollectMonPredIn. rewrite -monPred_in_bot. auto.
  Qed.

  Lemma tac_solve_monPred_in Δ V V' :
    CollectMonPredIn Δ V →
    V' ⊑ V →
    envs_entails Δ (monPred_in V').
  Proof.
    rewrite /CollectMonPredIn envs_entails_unseal => -> -> //.
  Qed.
End collect_monPred_in.

Ltac solve_monPred_in :=
  lazymatch goal with
  | |- envs_entails _ (monPred_in _) =>
    eapply tac_solve_monPred_in; [tc_solve|solve_lat]
  | _ =>
      fail "solve_monPred_in: not a 'monPred_in'"
  end.

Lemma tac_wp_expr_eval `{!cosmoG Σ} Δ E (Φ : val → vProp Σ) e e' :
  (∀ (e'':=e'), e = e'') →
  envs_entails Δ (WP e' @ E {{ Φ }}) → envs_entails Δ (WP e @ E {{ Φ }}).
Proof.
  by intros ->.
Qed.

Tactic Notation "wp_expr_eval" tactic(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp _ ?E ?e ?Q) =>
    eapply tac_wp_expr_eval;
      [let x := fresh in intros x; t; unfold x; reflexivity|]
  | _ =>
      fail "wp_expr_eval: not a 'wp'"
  end.

Lemma tac_wp_pure `{!cosmoG Σ} Δ Δ' E e1 e2 φ n (Φ : val → vProp Σ) :
  PureExecBase φ n e1 e2 →
  φ →
  MaybeIntoLaterNEnvs n Δ Δ' →
  envs_entails Δ' (WP e2 @ E {{ Φ }}) →
  envs_entails Δ (WP e1 @ E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ??? HΔ'. rewrite into_laterN_env_sound /=.
  rewrite HΔ' -wp_pure_step_later //.
Qed.

Lemma tac_wp_value `{!cosmoG Σ} Δ E Φ v :
  envs_entails Δ (Φ v) →
  envs_entails Δ (WP (Val v) @ E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ->. by apply wp_value.
Qed.

Ltac wp_expr_simpl :=
  wp_expr_eval simpl.

Ltac wp_value_head :=
  eapply tac_wp_value.

Ltac wp_finish :=
  wp_expr_simpl;      (* simplify occurences of subst/fill *)
  try wp_value_head;  (* in case we have reached a value, get rid of the WP *)
  pm_prettify.        (* prettify ▷s caused by [MaybeIntoLaterNEnvs] and
                         λs caused by wp_value *)

Ltac solve_lit_compare_safe :=
  (* The first branch is for when we have [vals_compare_safe] in the context.
     The other two branches are for when either one of the branches reduces to
     [True] or we have it in the context. *)
  fast_done || (left; fast_done) || (right; fast_done).

(** The argument [efoc] can be used to specify the construct that should be
reduced. For example, you can write [wp_pure (EIf _ _ _)], which will search
for an [EIf _ _ _] in the expression, and reduce it.

The use of [open_constr] in this tactic is essential. It will convert all holes
(i.e. [_]s) into evars, that later get unified when an occurences is found
(see [unify e' efoc] in the code below). *)
Tactic Notation "wp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp _ ?E ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' efoc;
      eapply (tac_wp_pure _ _ _ (fill K e'));
      [tc_solve                       (* PureExec *)
      |try solve_lit_compare_safe     (* The pure condition for PureExec -- handles trivial goals, including [vals_compare_safe] *)
      |tc_solve                       (* IntoLaters *)
      |wp_finish                      (* new goal *)
      ])
    || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | _ => fail "wp_pure: not a 'wp'"
  end.

(* TODO: do this in one go, without [repeat]. *)
Ltac wp_pures :=
  iStartProof;
  repeat (wp_pure _; []). (* The `;[]` makes sure that no side-condition
                             magically spawns. *)

(** Unlike [wp_pures], the tactics [wp_rec] and [wp_lam] should also reduce
lambdas/recs that are hidden behind a definition, i.e. they should use
[AsRecV_recv] as a proper instance instead of a [Hint Extern].

We achieve this by putting [AsRecV_recv] in the current environment so that it
can be used as an instance by the typeclass resolution system. We then perform
the reduction, and finally we clear this new hypothesis. *)
Tactic Notation "wp_rec" :=
  let H := fresh in
  assert (H := AsRecV_recv);
  wp_pure (App _ _);
  clear H.

Tactic Notation "wp_if" :=
  wp_pure (If _ _ _).
Tactic Notation "wp_if_true" :=
  wp_pure (If (LitV (LitBool true)) _ _).
Tactic Notation "wp_if_false" :=
  wp_pure (If (LitV (LitBool false)) _ _).
Tactic Notation "wp_unop" :=
  wp_pure (UnOp _ _).
Tactic Notation "wp_binop" :=
  wp_pure (BinOp _ _ _).
Tactic Notation "wp_op" :=
  wp_unop || wp_binop.
Tactic Notation "wp_lam" :=
  wp_rec.
Tactic Notation "wp_let" :=
  wp_pure (Rec BAnon (BNamed _) _); wp_lam.
Tactic Notation "wp_seq" :=
  wp_pure (Rec BAnon BAnon _); wp_lam.
Tactic Notation "wp_proj" :=
  wp_pure (Fst _) || wp_pure (Snd _).
Tactic Notation "wp_case" :=
  wp_pure (Case _ _ _).
Tactic Notation "wp_match" :=
  wp_case; wp_pure (Rec _ _ _); wp_lam.
Tactic Notation "wp_inj" :=
  wp_pure (InjL _) || wp_pure (InjR _).
Tactic Notation "wp_pair" :=
  wp_pure (Pair _ _).
Tactic Notation "wp_closure" :=
  wp_pure (Rec _ _ _).

Lemma tac_wp_bind `{!cosmoG Σ} K Δ E Φ e f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ (WP e @ E {{ v, WP f (Val v) @ E {{ Φ }} }})%I →
  envs_entails Δ (WP fill K e @ E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> -> ->. by apply: wp_bind.
Qed.

Ltac wp_bind_core K :=
  lazymatch eval hnf in K with
  | [] =>
      idtac
  | _ =>
      eapply (tac_wp_bind K); [simpl; reflexivity|reduction.pm_prettify]
  end.

Tactic Notation "wp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    reshape_expr e ltac:(fun K e' => unify e' efoc; wp_bind_core K)
    || fail "wp_bind: cannot find" efoc "in" e
  | _ => fail "wp_bind: not a 'wp'"
  end.

#[global] Instance from_assumption_mapsto_at_mono `{!cosmoG Σ} ℓ q v V1 V2 :
  V2 ⊑ V1 →
  FromAssumption false (ℓ ↦at{q}(v, V1) : iProp Σ)%I (ℓ ↦at{q}(v, V2) : iProp Σ)%I.
Proof.
  rewrite /FromAssumption. iIntros. by iApply mapsto_at_view_mono.
Qed.
#[global] Instance from_assumption_embed `{!cosmoG Σ} p (P Q : iProp Σ) :
  FromAssumption p P Q →
  FromAssumption p ⎡P⎤%I (⎡Q⎤%I : vProp Σ).
Proof.
  rewrite /FromAssumption -embed_intuitionistically_if.
  iIntros (Hpq) "Hp". by iApply Hpq.
Qed.
#[global] Hint Extern 1 (
  FromAssumption _ _ (_ ↦at{_}(_, _))%I
) => (
  apply from_assumption_mapsto_at_mono ; solve_lat
) : typeclass_instances.

Section heap.
  Context `{!cosmoG Σ}.

  Implicit Types P Q : vProp Σ.
  Implicit Types Φ : val → vProp Σ.
  Implicit Types Δ : envs (vPropI Σ).
  Implicit Types v : val.
  Implicit Types z : Z.
  Implicit Types ℓ : location.

  Lemma ref_of_at_block ℓ v V :
    ℓ *↦at() [ (v, V) ] ⊢
    ℓ ↦at(v, V).
  Proof.
    rewrite mapsto_at_view_block_eq. iIntros "[_ H]"=>/=. by iDestruct "H" as "[$_]".
  Qed.

  Lemma ref_of_na_block ℓ v :
    ℓ *↦ [v] ⊢
    ℓ ↦ v.
  Proof.
    iIntros "(_ & $ & _)".
  Qed.

  Lemma tac_wp_alloc_at Δ Δ' E j K (n : Z) v V Φ :
    (0 ≤ n)%Z →
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_entails Δ (monPred_in V) → (* TODO: this may be relaxed to use Δ' *)
    ( ∀ ℓ, ∃ Δ'',
      envs_app false (Esnoc Enil j ⎡ℓ *↦at() replicate (Z.to_nat n) (v, V)⎤) Δ' = Some Δ'' ∧
      envs_entails Δ'' (WP fill K #ℓ @ E {{ Φ }})
    ) →
    envs_entails Δ (WP fill K (Alloc Atomic #n v) @ E {{ Φ }}).
  Proof.
    intros ?.
    rewrite envs_entails_unseal=> ? HV HΔ. iIntros "HΔ". iApply wp_bind.
    iApply (wp_alloc_at_view with "[#]") ; [done | by iApply HV |].
    rewrite into_laterN_env_sound.
    iIntros "!>" (ℓ) "Hℓ" .
    destruct (HΔ ℓ) as (Δ'' & HΔ' & Hwp). iApply Hwp.
    iApply (envs_app_sound with "HΔ")=>//=. auto.
  Qed.

  Lemma tac_wp_alloc_na Δ Δ' E j K (n : Z) v Φ :
    (0 ≤ n)%Z →
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    ( ∀ ℓ, ∃ Δ'',
      envs_app false (Esnoc Enil j (ℓ *↦ replicate (Z.to_nat n) v)) Δ' = Some Δ'' ∧
      envs_entails Δ'' (WP fill K #ℓ @ E {{ Φ }})
    ) →
    envs_entails Δ (WP fill K (Alloc NonAtomic #n v) @ E {{ Φ }}).
  Proof.
    intros ?.
    rewrite envs_entails_unseal=> ? HΔ. iIntros "HΔ". iApply wp_bind.
    rewrite into_laterN_env_sound.
    iApply wp_alloc_na ; first done. iIntros "!>" (ℓ) "Hℓ".
    destruct (HΔ ℓ) as (Δ'' & HΔ' & Hwp). iApply Hwp.
    iApply (envs_app_sound with "HΔ")=>//=. auto.
  Qed.

  Lemma tac_wp_read_at Δ Δ' Δ'' E i j K ℓ (off : Z) q v V Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup i Δ' = Some (false, ⎡ ℓ.[off] ↦at{q}( v, V) ⎤)%I →
    envs_app true (Esnoc Enil j (monPred_in V)) Δ' = Some Δ'' →
    envs_entails Δ'' (WP fill K v @ E {{ Φ }}) →
    envs_entails Δ (WP fill K (Read Atomic #ℓ #off) @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> ??? HΔ'. iIntros "HΔ". iApply wp_bind.
    rewrite into_laterN_env_sound envs_lookup_split //.
    rewrite envs_app_sound // ; rewrite /=.
    iDestruct "HΔ" as "[Hℓ HΔ]".
    iApply (wp_read_at_view with "Hℓ"). iIntros "!> [#? Hℓ]". iApply HΔ'. by iApply ("HΔ" with "Hℓ [$]").
  Qed.

  Lemma tac_wp_read_at_block Δ Δ' E i j K ℓ (off : Z) q vVs Φ :
    0 ≤ off < length vVs →
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup i Δ' = Some (false, ⎡ ℓ *↦at{q}() vVs ⎤)%I →
    ( ∀ v V, vVs !! off = Some (v, V) →
      ∃ Δ'',
      envs_app true (Esnoc Enil j (monPred_in V)) Δ' = Some Δ'' ∧
      envs_entails Δ'' (WP fill K v @ E {{ Φ }})
    ) →
    envs_entails Δ (WP fill K (Read Atomic #ℓ #off) @ E {{ Φ }}).
  Proof.
    intros [[v V] HvV]%list_lookup_Z_lt_is_Some_2.
    rewrite envs_entails_unseal=> ?? HΔ'. specialize (HΔ' v V HvV) as (Δ'' & ? & HΔ').
    iIntros "HΔ". iApply wp_bind.
    rewrite into_laterN_env_sound envs_lookup_split //.
    rewrite envs_app_sound // ; rewrite /=.
    iDestruct "HΔ" as "[Hℓ HΔ]".
    iApply (wp_read_at_block_view with "[$Hℓ//]"). iIntros "!> [#? Hℓ]".
    iApply HΔ'. by iApply ("HΔ" with "Hℓ [$]").
  Qed.

  Lemma tac_wp_read_na Δ Δ' E i K ℓ (off : Z) q v Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup i Δ' = Some (false, ℓ.[off] ↦{q} v)%I →
    envs_entails Δ' (WP fill K v @ E {{ Φ }}) →
    envs_entails Δ (WP fill K (Read NonAtomic #ℓ #off) @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> ?? HΔ'. iIntros "HΔ". iApply wp_bind.
    rewrite into_laterN_env_sound envs_lookup_split //.
    iDestruct "HΔ" as "[Hℓ HΔ]".
    iApply (wp_read_na with "Hℓ"). iIntros "!> Hℓ". iApply HΔ'. by iApply "HΔ".
  Qed.

  Lemma tac_wp_read_na_block Δ Δ' E i K ℓ (off : Z) q vs Φ :
    0 ≤ off < length vs →
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup i Δ' = Some (false, ℓ *↦{q} vs)%I →
    ( ∀ v, vs !! off = Some v →
      envs_entails Δ' (WP fill K v @ E {{ Φ }})
    ) →
    envs_entails Δ (WP fill K (Read NonAtomic #ℓ #off) @ E {{ Φ }}).
  Proof.
    intros [v Hv]%list_lookup_Z_lt_is_Some_2.
    rewrite envs_entails_unseal=> ?? HΔ'. specialize (HΔ' v Hv). iIntros "HΔ". iApply wp_bind.
    rewrite into_laterN_env_sound envs_lookup_split //.
    iDestruct "HΔ" as "[Hℓ HΔ]".
    iApply (wp_read_na_block with "[$Hℓ//]"). iIntros "!> Hℓ".
    iApply HΔ'. by iApply "HΔ".
  Qed.

  Lemma tac_wp_write_at Δ Δ' Δ'' Δ''' E i j K ℓ (off : Z) v v' V0 V V' Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_entails Δ (monPred_in V0) → (* TODO: this may be relaxed to use Δ' *)
    V' ⊑ V ⊔ V0 →
  (*   envs_entails Δ' (monPred_in V -∗ monPred_in V') → *) (* TODO: sort this out once we have working tools for solving these kinds of goals *)
    envs_lookup i Δ' = Some (false, ⎡ℓ.[off] ↦at(v, V)⎤)%I →
    envs_simple_replace i false (Esnoc Enil i ⎡ℓ.[off] ↦at(v', V')⎤) Δ' = Some Δ'' →
    envs_app true (Esnoc Enil j (monPred_in V)) Δ'' = Some Δ''' → (* TODO: insert V' ? *)
    envs_entails Δ''' (WP fill K #() @ E {{ Φ }}) →
    envs_entails Δ (WP fill K (Write Atomic #ℓ #off v') @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> ? HV0 ???? HΔ'''. iIntros "HΔ". iApply wp_bind.
    iAssert (monPred_in V0) as "#?" ; first by iApply HV0.
    rewrite into_laterN_env_sound envs_simple_replace_sound // ; simpl. iDestruct "HΔ" as "[? HΔ]".
    iApply (wp_write_at_view with "[$]").
    iIntros "!> [ #? ? ]". iApply HΔ'''.
    iApply (envs_app_sound with "[-]") ; [ done | | simpl ; by auto ].
    iApply "HΔ". setoid_rewrite mapsto_at_view_mono at 1; eauto.
  Qed.

  Lemma tac_wp_write_at_block Δ Δ' E i j K ℓ (off : Z) vVs v' V0 Φ :
    0 ≤ off < length vVs →
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_entails Δ (monPred_in V0) → (* TODO: this may be relaxed to use Δ' *)
    envs_lookup i Δ' = Some (false, ⎡ℓ *↦at() vVs⎤)%I →
    ( ∀ v V, vVs !! off = Some (v, V) →
      ∃ V' Δ'' Δ''',
      V' ⊑ V ⊔ V0 ∧
  (*     envs_entails Δ' (monPred_in V -∗ monPred_in V') ∧ (* TODO: sort this out once we have working tools for solving these kinds of goals *) *)
      envs_simple_replace i false (Esnoc Enil i ⎡ℓ *↦at() <[off := (v',V')]> vVs⎤) Δ' = Some Δ'' ∧
      envs_app true (Esnoc Enil j (monPred_in V)) Δ'' = Some Δ''' ∧ (* TODO: insert V' ? *)
      envs_entails Δ''' (WP fill K #() @ E {{ Φ }})
    ) →
    envs_entails Δ (WP fill K (Write Atomic #ℓ #off v') @ E {{ Φ }}).
  Proof.
    intros [[v V] HvV]%list_lookup_Z_lt_is_Some_2.
    rewrite envs_entails_unseal=> ? HV0 ? HΔ'. specialize (HΔ' v V HvV) as (V' & Δ'' & Δ''' & HV' & ? & ? & HΔ''').
    iIntros "HΔ". iApply wp_bind.
    iAssert (monPred_in V0) as "#HV0" ; first by iApply HV0.
    rewrite into_laterN_env_sound envs_simple_replace_sound // ; simpl. iDestruct "HΔ" as "[Hℓ HΔ]".
    iApply (wp_write_at_block_view with "[$HV0 $Hℓ//]").
    iIntros "!> [ #? ? ]". iApply HΔ'''.
    iApply (envs_app_sound with "[-]") ; [ done | | simpl ; by auto ].
    iApply "HΔ". rewrite -HV'. by iFrame.
  Qed.

  Lemma tac_wp_write_na Δ Δ' Δ'' E i K ℓ (off : Z) v v' Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup i Δ' = Some (false, ℓ.[off] ↦ v)%I →
    envs_simple_replace i false (Esnoc Enil i (ℓ.[off] ↦ v')) Δ' = Some Δ'' →
    envs_entails Δ'' (WP fill K #() @ E {{ Φ }}) →
    envs_entails Δ (WP fill K (Write NonAtomic #ℓ #off v') @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> ??? HΔ''. iIntros "HΔ". iApply wp_bind.
    rewrite into_laterN_env_sound envs_simple_replace_sound //. simpl.
    iDestruct "HΔ" as "[Hℓ HΔ]".
    iApply (wp_write_na with "Hℓ"). iIntros "!> Hℓ". iApply HΔ''. iApply "HΔ". auto.
  Qed.

  Lemma tac_wp_write_na_block Δ Δ' Δ'' E i K ℓ (off : Z) vs v' Φ :
    0 ≤ off < length vs →
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup i Δ' = Some (false, ℓ *↦ vs)%I →
    envs_simple_replace i false (Esnoc Enil i (ℓ *↦ <[off := v']> vs)) Δ' = Some Δ'' →
    envs_entails Δ'' (WP fill K #() @ E {{ Φ }}) →
    envs_entails Δ (WP fill K (Write NonAtomic #ℓ #off v') @ E {{ Φ }}).
  Proof.
    intros [v Hv]%list_lookup_Z_lt_is_Some_2.
    rewrite envs_entails_unseal=> ??? HΔ''. iIntros "HΔ". iApply wp_bind.
    rewrite into_laterN_env_sound envs_simple_replace_sound //. simpl.
    iDestruct "HΔ" as "[Hℓ HΔ]".
    iApply (wp_write_na_block with "[$Hℓ//]"). iIntros "!> Hℓ". iApply HΔ''. iApply "HΔ". auto.
  Qed.

  Lemma tac_wp_cas Δ Δ' E i j K V V1 V' ℓ (off : Z) lit lit1 v2 Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    CollectMonPredIn Δ V1 → (* TODO: this may be relaxed to use Δ' *)
    envs_lookup i Δ' = Some (false, ⎡ℓ.[off] ↦at(#lit, V)⎤)%I →
    V' ⊑ V ⊔ V1 →
    lit_compare_safe lit lit1 →
    ( lit = lit1 →
      ∃ Δ'' Δ''',
      envs_simple_replace i false (Esnoc Enil i ⎡ℓ.[off] ↦at(v2, V')⎤) Δ' = Some Δ'' ∧
      envs_app true (Esnoc Enil j (monPred_in V)) Δ'' = Some Δ''' ∧ (* TODO: insert V' ? *)
      envs_entails Δ''' (WP fill K #true @ E {{ Φ }})
    ) →
    ( lit ≠ lit1 →
      ∃ Δ'',
      envs_app true (Esnoc Enil j (monPred_in V)) Δ' = Some Δ'' ∧ (* TODO: insert V' ? *)
      envs_entails Δ'' (WP fill K #false @ E {{ Φ }})
    ) →
    envs_entails Δ (WP fill K (CAS #ℓ #off #lit1 v2) @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> ? ? Hineq ?? Hsuc Hfail. iIntros "HΔ". iApply wp_bind.
    iAssert (monPred_in V1) as "#HV1"; first by rewrite collect_monPred_in.
    destruct (decide (lit = lit1)) as [Heq|Hne].
    - clear Hfail. specialize (Hsuc Heq) as (Δ'' & Δ''' & ? & ? & Hsuc).
      rewrite into_laterN_env_sound; simpl.
      rewrite envs_simple_replace_sound //; simpl.
      rewrite envs_app_sound //; simpl.
      iDestruct "HΔ" as "[Hℓ HΔ]". iApply (wp_cas_suc_view with "[$Hℓ]")=>//.
      iIntros "!> [#? Hℓ]". iApply Hsuc. iApply ("HΔ" with "[Hℓ] [$]"). by auto.
    - clear Hsuc. specialize (Hfail Hne) as (Δ'' & ? & Hfail).
      rewrite into_laterN_env_sound envs_lookup_split //; simpl.
      rewrite envs_app_sound //; simpl.
      iDestruct "HΔ" as "[Hℓ HΔ]". iApply (wp_cas_fail_view with "Hℓ")=>//.
      iIntros "!> [#? Hℓ]". iApply Hfail. by iApply ("HΔ" with "Hℓ [$]").
  Qed.

  Lemma tac_wp_cas_block Δ Δ' E i j K V1 ℓ (off : Z) vVs lit1 v2 Φ :
    0 ≤ off < length vVs →
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    CollectMonPredIn Δ V1 → (* TODO: this may be relaxed to use Δ' *)
    envs_lookup i Δ' = Some (false, ⎡ℓ *↦at() vVs⎤)%I →
    ( ∀ v V,
      vVs !! off = Some (v, V) →
        ∃ lit,
        v = #lit ∧ lit_compare_safe lit lit1
    ) →
    ( ∀ lit V,
      vVs !! off = Some (#lit, V) →
        ∃ V',
        V' ⊑ V ⊔ V1 ∧
        ( lit = lit1 →
            ∃ Δ'' Δ''',
            envs_simple_replace i false (Esnoc Enil i ⎡ℓ *↦at() <[off := (v2, V')]> vVs⎤) Δ' = Some Δ'' ∧
            envs_app true (Esnoc Enil j (monPred_in V)) Δ'' = Some Δ''' ∧ (* TODO: insert V' ? *)
            envs_entails Δ''' (WP fill K #true @ E {{ Φ }})
        ) ∧
        ( lit ≠ lit1 →
            ∃ Δ'',
            envs_app true (Esnoc Enil j (monPred_in V)) Δ' = Some Δ'' ∧ (* TODO: insert V' ? *)
            envs_entails Δ'' (WP fill K #false @ E {{ Φ }})
        )
    ) →
    envs_entails Δ (WP fill K (CAS #ℓ #off #lit1 v2) @ E {{ Φ }}).
  Proof.
    intros [[v V] HvV]%list_lookup_Z_lt_is_Some_2.
    rewrite envs_entails_unseal=> ??? Hlit H. iIntros "HΔ". iApply wp_bind.
    iAssert (monPred_in V1) as "#HV1"; first by rewrite collect_monPred_in.
    specialize (Hlit v V HvV) as (lit & -> & ?).
    specialize (H lit V HvV) as (V' & Hineq & Hsuc & Hfail).
    destruct (decide (lit = lit1)) as [Heq|Hne].
    - clear Hfail. specialize (Hsuc Heq) as (Δ'' & Δ''' & ? & ? & Hsuc).
      rewrite into_laterN_env_sound; simpl.
      rewrite envs_simple_replace_sound //; simpl.
      rewrite envs_app_sound //; simpl.
      iDestruct "HΔ" as "[Hℓ HΔ]". iApply (wp_cas_suc_block_view with "[$Hℓ $HV1//]")=>//.
      iIntros "!> [#? Hℓ]". iApply Hsuc. iApply ("HΔ" with "[Hℓ] [$]"). rewrite Hineq. by auto.
    - clear Hsuc. specialize (Hfail Hne) as (Δ'' & ? & Hfail).
      rewrite into_laterN_env_sound envs_lookup_split //; simpl.
      rewrite envs_app_sound //; simpl.
      iDestruct "HΔ" as "[Hℓ HΔ]". iApply (wp_cas_fail_block_view with "[$Hℓ//]")=>//.
      iIntros "!> [#? Hℓ]". iApply Hfail. by iApply ("HΔ" with "Hℓ [$]").
  Qed.

  Lemma tac_wp_cas_fail Δ Δ' Δ'' E i j K V ℓ (off : Z) q lit lit1 v2 Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup i Δ' = Some (false, ⎡ℓ.[off] ↦at{q}(#lit, V)⎤)%I →
    envs_app true (Esnoc Enil j (monPred_in V)) Δ' = Some Δ'' → (* TODO: insert V' ? *)
    lit ≠ lit1 →
    lit_compare_safe lit lit1 →
    envs_entails Δ'' (WP fill K #false @ E {{ Φ }}) →
    envs_entails Δ (WP fill K (CAS #ℓ #off #lit1 v2) @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> ????? HΔ''. iIntros "HΔ". iApply wp_bind.
    rewrite into_laterN_env_sound envs_lookup_split // envs_app_sound //. simpl.
    iDestruct "HΔ" as "[Hℓ HΔ]". iApply (wp_cas_fail_view with "[Hℓ]")=>//.
    iIntros "!> [#HV Hℓ]". iApply HΔ''. by iApply ("HΔ" with "Hℓ [$HV]").
  Qed.

  Lemma tac_wp_cas_fail_block Δ Δ' E i j K ℓ (off : Z) q vVs lit1 v2 Φ :
    0 ≤ off < length vVs →
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup i Δ' = Some (false, ⎡ℓ *↦at{q}() vVs⎤)%I →
    ( ∀ v V,
      vVs !! off = Some (v, V) →
        ∃ lit,
        v = #lit ∧
        lit ≠ lit1 ∧
        lit_compare_safe lit lit1
    ) →
    ( ∀ lit V,
      vVs !! off = Some (#lit, V) →
        ∃ Δ'',
        envs_app true (Esnoc Enil j (monPred_in V)) Δ' = Some Δ'' ∧ (* TODO: insert V' ? *)
        envs_entails Δ'' (WP fill K #false @ E {{ Φ }})
    ) →
    envs_entails Δ (WP fill K (CAS #ℓ #off #lit1 v2) @ E {{ Φ }}).
  Proof.
    intros [[v V] HvV]%list_lookup_Z_lt_is_Some_2.
    rewrite envs_entails_unseal => ?? Hlit H.
    specialize (Hlit v V HvV) as (lit & -> & ? & ?).
    specialize (H lit V HvV) as (Δ'' & ? & HΔ'').
    iIntros "HΔ". iApply wp_bind.
    rewrite into_laterN_env_sound envs_lookup_split // envs_app_sound //. simpl.
    iDestruct "HΔ" as "[Hℓ HΔ]". iApply (wp_cas_fail_block_view with "[$Hℓ//]")=>//.
    iIntros "!> [#HV Hℓ]". iApply HΔ''. by iApply ("HΔ" with "Hℓ [$HV]").
  Qed.

  Lemma tac_wp_cas_suc Δ Δ' Δ'' Δ''' E i j K V V1 V' ℓ (off : Z) lit lit1 v2 Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    CollectMonPredIn Δ V1 → (* TODO: this may be relaxed to use Δ' *)
    V' ⊑ V ⊔ V1 →
    envs_lookup i Δ' = Some (false, ⎡ℓ.[off] ↦at(#lit, V)⎤)%I →
    envs_simple_replace i false (Esnoc Enil i ⎡ℓ.[off] ↦at(v2, V')⎤) Δ' = Some Δ'' →
    envs_app true (Esnoc Enil j (monPred_in V)) Δ'' = Some Δ''' → (* TODO: insert V' ? *)
    lit = lit1 →
    lit_compare_safe lit lit1 →
    envs_entails Δ''' (WP fill K #true @ E {{ Φ }}) →
    envs_entails Δ (WP fill K (CAS #ℓ #off #lit1 v2) @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> ???????? HΔ''. iIntros "HΔ". iApply wp_bind.
    iAssert (monPred_in V1) as "#HV1"; first by rewrite collect_monPred_in.
    rewrite into_laterN_env_sound //.
    rewrite envs_simple_replace_sound //; simpl.
    rewrite envs_app_sound //; simpl.
    iDestruct "HΔ" as "[Hℓ HΔ]". iApply (wp_cas_suc_view with "[$Hℓ]")=>//.
    iIntros "!> [#HV Hℓ]". iApply HΔ''. iApply ("HΔ" with "[Hℓ] [$HV]"). auto.
  Qed.

  Lemma tac_wp_cas_suc_block Δ Δ' E i j K V1 ℓ (off : Z) vVs lit1 v2 Φ :
    0 ≤ off < length vVs →
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    CollectMonPredIn Δ V1 → (* TODO: this may be relaxed to use Δ' *)
    envs_lookup i Δ' = Some (false, ⎡ℓ *↦at() vVs⎤)%I →
    ( ∀ v V,
      vVs !! off = Some (v, V) →
        ∃ lit,
        v = #lit ∧
        lit = lit1 ∧
        lit_compare_safe lit lit1
    ) →
    ( ∀ (lit : lit) (V : view),
      vVs !! off = Some (#lit, V) →
        ∃ V' Δ'' Δ''',
        V' ⊑ V ⊔ V1 ∧
        envs_simple_replace i false (Esnoc Enil i ⎡ℓ *↦at() <[off := (v2, V')]> vVs⎤) Δ' = Some Δ'' ∧
        envs_app true (Esnoc Enil j (monPred_in V)) Δ'' = Some Δ''' ∧ (* TODO: insert V' ? *)
        envs_entails Δ''' (WP fill K #true @ E {{ Φ }})
    ) →
    envs_entails Δ (WP fill K (CAS #ℓ #off #lit1 v2) @ E {{ Φ }}).
  Proof.
    intros [[v V] HvV]%list_lookup_Z_lt_is_Some_2.
    rewrite envs_entails_unseal=> ??? Hlit H.
    specialize (Hlit v V HvV) as (? & -> & -> & ?).
    specialize (H lit1 V HvV) as (V' & Δ'' & Δ''' & HV' & ? & ? & HΔ''').
    iIntros "HΔ". iApply wp_bind.
    iAssert (monPred_in V1) as "#HV1"; first by rewrite collect_monPred_in.
    rewrite into_laterN_env_sound //.
    rewrite envs_simple_replace_sound //; simpl.
    rewrite envs_app_sound //; simpl.
    iDestruct "HΔ" as "[Hℓ HΔ]". iApply (wp_cas_suc_block_view with "[$Hℓ $HV1 //]")=>//.
    rewrite -HV'.
    iIntros "!> [#HV Hℓ]". iApply HΔ'''. iApply ("HΔ" with "[Hℓ] [$HV]"). auto.
  Qed.
End heap.

(** Evaluate [lem] to a hypothesis [H] that can be applied, and then run
[wp_bind K; tac H] for every possible evaluation context.  [tac] can do
[iApplyHyp H] to actually apply the hypothesis.  TC resolution of [lem] premises
happens *after* [tac H] got executed. *)
Tactic Notation "wp_apply_core" open_constr(lem) tactic(tac) :=
  wp_pures;
  iPoseProofCore lem as false (fun H =>
    lazymatch goal with
    | |- envs_entails _ (wp _ ?E ?e ?Q) =>
      reshape_expr e ltac:(fun K e' =>
        wp_bind_core K; tac H) ||
      lazymatch iTypeOf H with
      | Some (_,?P) => fail "wp_apply: cannot apply" P
      end
    | _ => fail "wp_apply: not a 'wp'"
    end).
Tactic Notation "wp_apply" open_constr(lem) :=
  wp_apply_core lem (fun H => iApplyHyp H; try iNext; try wp_expr_simpl).

(** Tactic tailored for atomic triples: the first, simple one just runs
[iAuIntro] on the goal, as atomic triples always have an atomic update as their
premise.  The second one additionaly does some framing: it gets rid of [Hs] from
the context, which is intended to be the non-laterable assertions that iAuIntro
would choke on.  You get them all back in the continuation of the atomic
operation. *)
Tactic Notation "awp_apply" open_constr(lem) :=
  (wp_apply_core lem ltac:(fun H => iApplyHyp H));
  last iAuIntro.
Tactic Notation "awp_apply" open_constr(lem) "without" constr(Hs) :=
  (wp_apply_core lem
    ltac:(fun H =>
      iApply wp_frame_wand_l; iSplitL Hs; [iAccu|iApplyHyp H]));
  last iAuIntro.

Ltac solve_nonneg :=
  first [ done | lia ].

Ltac solve_indexbounds :=
  first [ done | lia ].

Tactic Notation "wp_alloc" ident(ℓ) "at" open_constr(V) "as" constr(H) :=
  let Htmp := iFresh in
  let finish _ :=
    first [intros ℓ | fail 1 "wp_alloc_at:" ℓ "not fresh"];
      eexists; split;
        [pm_reflexivity || fail "wp_alloc_at:" H "not fresh"
        |iDestructHyp Htmp as H; wp_finish] in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp _ ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_alloc_at _ _ _ Htmp K _ _ V))
      |fail 1 "wp_alloc_at: cannot find 'Alloc Atomic' in" e];
    [solve_nonneg
    |tc_solve
    |try solve_monPred_in
    |finish ()]
  | _ => fail "wp_alloc_at: not a 'wp'"
  end.

Tactic Notation "wp_alloc_na" ident(ℓ) "as" constr(H) :=
  let Htmp := iFresh in
  let finish _ :=
    first [intros ℓ | fail 1 "wp_alloc_na:" ℓ "not fresh"];
      eexists; split;
        [pm_reflexivity || fail "wp_alloc_na:" H "not fresh"
        |iDestructHyp Htmp as H; wp_finish] in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp _ ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_alloc_na _ _ _ Htmp K))
      |fail 1 "wp_alloc_na: cannot find 'Alloc NonAtomic' in" e];
    [solve_nonneg
    |tc_solve
    |finish ()]
  | _ => fail "wp_alloc_na: not a 'wp'"
  end.

Tactic Notation "wp_alloc" ident(ℓ) "at" open_constr(V) :=
  wp_alloc ℓ at V as "?".
Tactic Notation "wp_alloc" ident(ℓ) "as" constr(H) :=
  (* We need to explicitely write [@empty _ gmap_empty] instead of
    [∅], otherwise the [Empty] typeclass parameter gets instantiated by
    garbage by [solve_monPred_in] *)
  first [ wp_alloc ℓ at (@empty _ gmap_empty) as H | wp_alloc_na ℓ as H ].
Tactic Notation "wp_alloc" ident(ℓ) :=
  wp_alloc ℓ as "?".

Tactic Notation "wp_ref" ident(ℓ) "at" open_constr(V) "as" constr(H) :=
  let Htmp := iFresh in
  wp_alloc ℓ at V as Htmp;
  iDestruct (ref_of_at_block with Htmp) as H.

Tactic Notation "wp_ref_na" ident(ℓ) "as" constr(H) :=
  let Htmp := iFresh in
  wp_alloc_na ℓ as Htmp;
  iDestruct (ref_of_at_block with Htmp) as H.

Tactic Notation "wp_ref" ident(ℓ) "at" open_constr(V) :=
  wp_ref ℓ at V as "?".
Tactic Notation "wp_ref" ident(ℓ) "as" constr(H) :=
  (* We need to explicitely write [@empty _ gmap_empty] instead of
    [∅], otherwise the [Empty] typeclass parameter gets instantiated by
    garbage by [solve_monPred_in] *)
  first [ wp_ref ℓ at (@empty _ gmap_empty) as H | wp_ref_na ℓ as H ].
Tactic Notation "wp_ref" ident(ℓ) :=
  wp_ref ℓ as "?".

Tactic Notation "wp_read_block" "as" simple_intropattern(v) simple_intropattern(V) simple_intropattern(Hlookup) constr(HV) :=
  let v_tmp := fresh in
  let V_tmp := fresh in
  let Hlookup_tmp := fresh in
  let HV_tmp := iFresh in
  let solve_mapsto _ :=
    let ℓ :=
        match goal with
        | |- _ = Some (_, (⎡?ℓ *↦at{_}() _⎤)%I) => ℓ
        end
    in
    iAssumptionCore || fail "wp_read_at_block: cannot find" ℓ "↦at ?"
  in
  let finish _ :=
    wp_finish ;
    move : v_tmp V_tmp Hlookup_tmp => v V Hlookup ;
    iDestructHyp HV_tmp as HV
  in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp _ ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_read_at_block _ _ _ _ HV_tmp K))
      |fail 1 "wp_read_at_block: cannot find 'Read Atomic' in" e];
    [
    |tc_solve
    |solve_mapsto ()
    |intros v_tmp V_tmp Hlookup_tmp ; eexists ; split ;
      [pm_reflexivity
      |finish()]
    ] ;
    first try solve_indexbounds
  | _ => fail "wp_read_at_block: not a 'wp'"
  end.

Tactic Notation "wp_read" "as" constr(H) :=
  let Htmp := iFresh in
  let solve_mapsto _ :=
    let ℓi :=
        match goal with
        | |- _ = Some (_, (⎡?ℓi ↦at{_}( _ , _ )⎤)%I) => ℓi
        end
    in
    iAssumptionCore || fail "wp_read_at: cannot find" ℓi "↦at ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp _ ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_read_at _ _ _ _ _ Htmp K))
      |fail 1 "wp_read_at: cannot find 'Read Atomic' in" e];
    [tc_solve
    |solve_mapsto ()
    |pm_reflexivity
    |wp_finish ; iDestructHyp Htmp as H]
  | _ => fail "wp_read_at: not a 'wp'"
  end.

Tactic Notation "wp_read_na_block" "as" simple_intropattern(v) simple_intropattern(Hv) :=
  let v_tmp := fresh in
  let Hv_tmp := fresh in
  let solve_mapsto _ :=
    let ℓ :=
        match goal with
        | |- _ = Some (_, (?ℓ *↦{_} _)%I) => ℓ
        end
    in
    iAssumptionCore || fail "wp_read_na_block: cannot find" ℓ "*↦ ?"
  in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp _ ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_read_na_block _ _ _ _ K))
      |fail 1 "wp_read_na_block: cannot find 'Read NonAtomic' in" e];
    [
    |tc_solve
    |solve_mapsto ()
    |intros v_tmp Hv_tmp ; wp_finish ; move : v_tmp Hv_tmp => v Hv
    ] ;
    first try solve_indexbounds
  | _ => fail "wp_read_na_block: not a 'wp'"
  end.

Tactic Notation "wp_read_na" :=
  let solve_mapsto _ :=
    let ℓi :=
        match goal with
        | |- _ = Some (_, (?ℓi ↦{_} _)%I) => ℓi
        end
    in
    iAssumptionCore || fail "wp_read_na: cannot find" ℓi "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp _ ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_read_na _ _ _ _ K))
      |fail 1 "wp_read_na: cannot find 'Read NonAtomic' in" e];
    [tc_solve
    |solve_mapsto ()
    |wp_finish]
  | _ => fail "wp_read_na: not a 'wp'"
  end.

Tactic Notation "wp_read_block" "as" simple_intropattern(v) simple_intropattern(V) simple_intropattern(Hlookup) :=
  wp_read_block as v V Hlookup "?".
Tactic Notation "wp_read_block" "as" simple_intropattern(v) simple_intropattern(Hv) :=
  first [ wp_read_block as v ? Hv "?" | wp_read_na_block as v Hv ].

Tactic Notation "wp_read" :=
  first [ wp_read as "?" | wp_read_na ].

Tactic Notation "wp_write_block" "at" open_constr(V') "as" simple_intropattern(v) simple_intropattern(V) simple_intropattern(Hlookup) constr(HV) :=
  let v_tmp := fresh in
  let V_tmp := fresh in
  let Hlookup_tmp := fresh in
  let HV_tmp := iFresh in
  let solve_mapsto _ :=
    let ℓ :=
        match goal with
        | |- _ = Some (_, (⎡?ℓ *↦at{_}() _⎤)%I) => ℓ
        end
    in
    iAssumptionCore || fail "wp_write_at_block: cannot find" ℓ "*↦at ?"
  in
  let finish _ :=
    first [wp_seq|wp_finish] ;
    move : v_tmp V_tmp Hlookup_tmp => v V Hlookup ;
    iDestructHyp HV_tmp as HV
  in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp _ ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => once (eapply (tac_wp_write_at_block _ _ _ _ HV_tmp K)))
      |fail 1 "wp_write_at_block: cannot find 'Write Atomic' in" e];
    [
    |tc_solve
    |try solve_monPred_in
    |solve_mapsto ()
    |intros v_tmp V_tmp Hlookup_tmp ; eexists V', _, _ ;
      split ; last split ; last split ;
      [once solve_lat
      |pm_reflexivity
      |pm_reflexivity
      |finish ()
      ]
    ] ;
    first try solve_indexbounds
  | _ => fail "wp_write_at_block: not a 'wp'"
  end.

Tactic Notation "wp_write" "at" open_constr(V') "as" constr(H) :=
  let Htmp := iFresh in
  let solve_mapsto _ :=
    let ℓi :=
        match goal with
        | |- _ = Some (_, (⎡?ℓi ↦at{_}( _ , _ )⎤)%I) => ℓi
        end
    in
    iAssumptionCore || fail "wp_write_at: cannot find" ℓi "↦at ?"
  in
  let finish _ :=
    first [wp_seq|wp_finish] ;
    iDestructHyp Htmp as H
  in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp _ ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => once (eapply (tac_wp_write_at _ _ _ _ _ _ Htmp K _ _ _ _ _ _ V')))
      |fail 1 "wp_write_at: cannot find 'Write Atomic' in" e];
    [tc_solve
    |try solve_monPred_in
    |once solve_lat
    |solve_mapsto ()
    |pm_reflexivity
    |pm_reflexivity
    |finish ()]
  | _ => fail "wp_write_at: not a 'wp'"
  end.

Tactic Notation "wp_write_na_block" :=
  let solve_mapsto _ :=
    let ℓ :=
        match goal with
        | |- _ = Some (_, (?ℓ *↦{_} _)%I) => ℓ
        end
    in
    iAssumptionCore || fail "wp_write_na_block: cannot find" ℓ "*↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp _ ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_write_na_block _ _ _ _ _ K))
      |fail 1 "wp_write_na_block: cannot find 'Write NonAtomic' in" e];
    [
    |tc_solve
    |solve_mapsto ()
    |pm_reflexivity
    |first [wp_seq|wp_finish]
    ] ;
    try solve_indexbounds
  | _ => fail "wp_write_na_block: not a 'wp'"
  end.

Tactic Notation "wp_write_na" :=
  let solve_mapsto _ :=
    let ℓi :=
        match goal with
        | |- _ = Some (_, (?ℓi ↦{_} _)%I) => ℓi
        end
    in
    iAssumptionCore || fail "wp_write_na: cannot find" ℓi "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp _ ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_write_na _ _ _ _ _ K))
      |fail 1 "wp_write_na: cannot find 'Write NonAtomic' in" e];
    [tc_solve
    |solve_mapsto ()
    |pm_reflexivity
    |first [wp_seq|wp_finish]]
  | _ => fail "wp_write_na: not a 'wp'"
  end.

Tactic Notation "wp_write_block" "as" simple_intropattern(v) simple_intropattern(V) simple_intropattern(Hlookup) constr(HV) :=
  wp_write_block at _ as v V Hlookup HV.
Tactic Notation "wp_write_block" "at" open_constr(V) "as" simple_intropattern(v) simple_intropattern(V) simple_intropattern(Hlookup) :=
  wp_write_block at V as v V Hlookup "_".
Tactic Notation "wp_write_block" "as" simple_intropattern(v) simple_intropattern(V) simple_intropattern(Hlookup) :=
  wp_write_block at _ as v V Hlookup "_".
Tactic Notation "wp_write_block" :=
  first [ wp_write_block at _ as ? ? ? "_" | wp_write_na_block ].

Tactic Notation "wp_write" "as" constr(H) :=
  wp_write at _ as H.
Tactic Notation "wp_write" "at" open_constr(V) :=
  wp_write at V as "_".
Tactic Notation "wp_write" :=
  first [ wp_write at _ as "_" | wp_write_na ].

Tactic Notation "wp_cas_block"
  "at" open_constr(V')
  "as" simple_intropattern(lit) simple_intropattern(V) simple_intropattern(Hlookup) constr(HV)
  "," simple_intropattern(Heq) "|" simple_intropattern(Hineq)
:=
  let lit_tmp := fresh in
  let V_tmp := fresh in
  let Hlookup_tmp := fresh in
  let HV_tmp := iFresh in
  let H_tmp := fresh in
  let solve_mapsto _ :=
    let ℓ := match goal with |- _ = Some (_, (⎡?ℓ *↦at{_}() _⎤)%I) => ℓ end in
    iAssumptionCore || fail "wp_cas_block: cannot find" ℓ "*↦at ?"
  in
  let finish _ :=
    wp_finish ;
    (move : lit_tmp V_tmp Hlookup_tmp H_tmp => lit V Hlookup)
  in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp _ ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_cas_block _ _ _ _ HV_tmp K))
      |fail 1 "wp_cas_block: cannot find 'CAS' in" e];
    [
    |tc_solve
    |tc_solve
    |solve_mapsto ()
    |
    |intros lit_tmp V_tmp Hlookup_tmp ; eexists V' ;
      split ; last split ;
      [solve_lat
      |intros H_tmp ; eexists _, _ ; (split ; last split) ;
        [pm_reflexivity
        |pm_reflexivity
        |finish () => Heq   ; iDestructHyp HV_tmp as HV]
      |intros H_tmp ; eexists _ ; split ;
        [pm_reflexivity
        |finish () => Hineq ; iDestructHyp HV_tmp as HV]
      ]
    ] ;
    first try solve_indexbounds
  | _ => fail "wp_cas_block: not a 'wp'"
  end.

Tactic Notation "wp_cas" "at" open_constr(V') "as" constr(HV) "," simple_intropattern(Heq) "|" simple_intropattern(Hineq) :=
  let HV_tmp := iFresh in
  let H_tmp := fresh in
  let solve_mapsto _ :=
    let ℓi := match goal with |- _ = Some (_, (⎡?ℓi ↦at{_}(_, _)⎤)%I) => ℓi end in
    iAssumptionCore || fail "wp_cas: cannot find" ℓi "↦at ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp _ ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_cas _ _ _ _ HV_tmp K _ _ V'))
      |fail 1 "wp_cas: cannot find 'CAS' in" e];
    [tc_solve
    |tc_solve
    |solve_mapsto ()
    |solve_lat
    |try solve_lit_compare_safe
    |intros H_tmp ; eexists _, _ ; (split ; last split) ;
      [pm_reflexivity
      |pm_reflexivity
      |wp_finish ; move : H_tmp => Heq   ; iDestructHyp HV_tmp as HV]
    |intros H_tmp ; eexists _ ; split ;
      [pm_reflexivity
      |wp_finish ; move : H_tmp => Hineq ; iDestructHyp HV_tmp as HV]
    ]
  | _ => fail "wp_cas: not a 'wp'"
  end.

Tactic Notation "wp_cas_block" "as" simple_intropattern(lit) simple_intropattern(V) simple_intropattern(Hlookup) constr(HV) "," simple_intropattern(Heq) "|" simple_intropattern(Hineq) :=
  wp_cas_block at _ as lit V Hlookup HV, Heq | Hineq.
Tactic Notation "wp_cas_block" "at" open_constr(V') "as" simple_intropattern(lit) simple_intropattern(V) simple_intropattern(Hlookup) :=
  wp_cas_block at V' as lit V Hlookup "?", ? | ?.
Tactic Notation "wp_cas_block" "as" simple_intropattern(lit) simple_intropattern(V) simple_intropattern(Hlookup) :=
  wp_cas_block at _ as lit V Hlookup "?", ? | ?.
Tactic Notation "wp_cas_block" :=
  wp_cas_block at _ as ? ? ? "?", ? | ?.

Tactic Notation "wp_cas" "as" constr(HV) "," simple_intropattern(Heq) "|" simple_intropattern(Hineq) :=
  wp_cas at _ as HV, Heq | Hineq.
Tactic Notation "wp_cas" "at" open_constr(V') :=
  wp_cas at V' as "?", ? | ?.
Tactic Notation "wp_cas" :=
  wp_cas at _ as "?", ? | ?.
Tactic Notation "wp_cas" "as" simple_intropattern(Heq) "|" simple_intropattern(Hineq) :=
  wp_cas at _ as "_", H1 | H2.

Tactic Notation "wp_cas_fail_block" "as" simple_intropattern(lit) simple_intropattern(V) simple_intropattern(Hlookup) constr(HV) :=
  let lit_tmp := fresh in
  let V_tmp := fresh in
  let Hlookup_tmp := fresh in
  let HV_tmp := iFresh in
  let solve_mapsto _ :=
    let ℓ := match goal with |- _ = Some (_, (⎡?ℓ *↦at{_}() _⎤)%I) => ℓ end in
    iAssumptionCore || fail "wp_cas_fail_block: cannot find" ℓ "*↦at ?"
  in
  let finish _ :=
    wp_finish ;
    move : lit_tmp V_tmp Hlookup_tmp => lit V Hlookup ;
    iDestructHyp HV_tmp as HV
  in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp _ ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_cas_fail_block _ _ _ _ HV_tmp K))
      |fail 1 "wp_cas_fail_block: cannot find 'CAS' in" e];
    [
    |tc_solve
    |solve_mapsto ()
    |
    |intros lit_tmp V_tmp Hlookup_tmp ; eexists _ ; split ;
      [pm_reflexivity
      |finish ()]
    ] ;
    first try solve_indexbounds
  | _ => fail "wp_cas_fail_block: not a 'wp'"
  end.

Tactic Notation "wp_cas_fail" "as" constr(HV) :=
  let Htmp := iFresh in
  let solve_mapsto _ :=
    let ℓi := match goal with |- _ = Some (_, (⎡?ℓi ↦at{_}(_, _)⎤)%I) => ℓi end in
    iAssumptionCore || fail "wp_cas_fail: cannot find" ℓi "↦at ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp _ ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_cas_fail _ _ _ _ _ Htmp K))
      |fail 1 "wp_cas_fail: cannot find 'CAS' in" e];
    [tc_solve
    |solve_mapsto ()
    |pm_reflexivity
    |try (simpl; congruence) (* value inequality *)
    |try solve_lit_compare_safe
    |iDestructHyp Htmp as HV ; wp_finish]
  | _ => fail "wp_cas_fail: not a 'wp'"
  end.

Tactic Notation "wp_cas_fail_block" "as" simple_intropattern(lit) simple_intropattern(V) simple_intropattern(Hlookup) :=
  wp_cas_fail_block as lit V Hlookup "?".
Tactic Notation "wp_cas_fail_block" :=
  wp_cas_fail_block as ? ? ? "?".

Tactic Notation "wp_cas_fail" :=
  wp_cas_fail as "?".

Tactic Notation "wp_cas_suc_block" "at" open_constr(V') "as" simple_intropattern(lit) simple_intropattern(V) simple_intropattern(Hlookup) constr(HV) :=
  let lit_tmp := fresh in
  let V_tmp := fresh in
  let Hlookup_tmp := fresh in
  let HV_tmp := iFresh in
  let solve_mapsto _ :=
    let ℓ := match goal with |- _ = Some (_, (⎡?ℓ *↦at{_}() _⎤)%I) => ℓ end in
    iAssumptionCore || fail "wp_cas_suc_block: cannot find" ℓ "*↦at ?"
  in
  let finish _ :=
    wp_finish ;
    move : lit_tmp V_tmp Hlookup_tmp => lit V Hlookup ;
    iDestructHyp HV_tmp as HV
  in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp _ ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_cas_suc_block _ _ _ _ HV_tmp K))
      |fail 1 "wp_cas_suc_block: cannot find 'CAS' in" e];
    [
    |tc_solve
    |tc_solve
    |solve_mapsto ()
    |
    |intros lit_tmp V_tmp Hlookup_tmp ; eexists V', _, _ ;
      split ; last split ; last split ;
      [solve_lat
      |pm_reflexivity
      |pm_reflexivity
      |finish ()]
    ] ;
    first try solve_indexbounds
  | _ => fail "wp_cas_suc_block: not a 'wp'"
  end.

Tactic Notation "wp_cas_suc" "at" open_constr(V') "as" constr(HV) :=
  let Htmp := iFresh in
  let solve_mapsto _ :=
    let ℓi := match goal with |- _ = Some (_, (⎡?ℓi ↦at{_}(_, _)⎤)%I) => ℓi end in
    iAssumptionCore || fail "wp_cas_suc: cannot find" ℓi "↦at ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp _ ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_cas_suc _ _ _ _ _ _ Htmp K _ _ V'))
      |fail 1 "wp_cas_suc: cannot find 'CAS' in" e];
    [tc_solve
    |tc_solve
    |solve_lat
    |solve_mapsto ()
    |pm_reflexivity
    |pm_reflexivity
    |try (simpl; congruence) (* value equality *)
    |try solve_lit_compare_safe
    |iDestructHyp Htmp as HV ; wp_finish]
  | _ => fail "wp_cas_suc: not a 'wp'"
  end.

Tactic Notation "wp_cas_suc_block" "as" simple_intropattern(lit) simple_intropattern(V) simple_intropattern(Hlookup) constr(HV) :=
  wp_cas_suc_block at _ as lit V Hlookup HV.
Tactic Notation "wp_cas_suc_block" "at" open_constr(V') "as" simple_intropattern(lit) simple_intropattern(V) simple_intropattern(Hlookup) :=
  wp_cas_suc_block at V' as lit V Hlookup "?".
Tactic Notation "wp_cas_suc_block" "as" simple_intropattern(lit) simple_intropattern(V) simple_intropattern(Hlookup) :=
  wp_cas_suc_block at _ as lit V Hlookup "?".
Tactic Notation "wp_cas_suc_block" :=
  wp_cas_suc_block at _ as ? ? ? "?".

Tactic Notation "wp_cas_suc" "as" constr(HV) :=
  wp_cas_suc at _ as HV.
Tactic Notation "wp_cas_suc" "at" open_constr(V') :=
  wp_cas_suc at V' as "?".
Tactic Notation "wp_cas_suc" :=
  wp_cas_suc at _ as "?".
