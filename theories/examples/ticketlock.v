From iris.algebra Require Import
  excl
  auth
  gset.
From iris.base_logic Require Import
  invariants.
From iris.program_logic Require Export
  weakestpre.
From iris.proofmode Require Import
  tactics.

From cosmo Require Import
  prelude.
From cosmo.language Require Import
  proofmode
  notations.

Set Default Proof Using "Type".

Import uPred.

Definition wait_loop: val :=
  rec: "wait_loop" "x" "lk" :=
    let: "o" := !at (Fst "lk") in
    if: "x" = "o"
      then #() (* my turn *)
      else "wait_loop" "x" "lk".

Definition newlock : val :=
  λ: <>, ((* owner *) ref_at #0, (* next *) ref_at #0).

Definition acquire : val :=
  rec: "acquire" "lk" :=
    let: "n" := !at (Snd "lk") in
    if: CAS_ref (Snd "lk") "n" ("n" + #1)
      then wait_loop "n" "lk"
      else "acquire" "lk".

Definition release : val :=
  λ: "lk", Fst "lk" <-at !at (Fst "lk") + #1.

(** The CMRAs we need. *)
Class tlockG Σ := {
  #[local] tlock_G :: inG Σ (authR (prodUR (optionUR (exclR natO)) (gset_disjUR nat)))
}.

Definition tlockΣ : gFunctors :=
  #[ GFunctor (authR (prodUR (optionUR (exclR natO)) (gset_disjUR nat))) ].

#[global] Instance subG_tlockΣ {Σ} : subG tlockΣ Σ → tlockG Σ.
Proof.
  solve_inG.
Qed.

Section proof.
  Context `{!cosmoG Σ, !tlockG Σ} (N : namespace).

  (*
     ICFP20: “is_lock” corresponds to the assertion “IsTicketLock” from the
     paper, Section 5.3 and Figure 14 “Internal invariant of a ticket lock”.
     With slight variations: where the paper uses two ghost variables (“served”
     and “issued”), we use only one (γ) which stores the pair of served and
     issued. Also, the assertion called “ticket n” in the paper is called
     “issued γ n” here.
  *)

  Definition lock_inv (γ : gname) (lo ln : location) (R : vProp Σ) : iProp Σ :=
    ∃ (o n : nat) (V : view),
    lo ↦at(#o, V) ∗
    ln ↦at #n ∗
    own γ (● (Excl' o, GSet (set_seq 0 n))) ∗
    ( own γ (◯ (Excl' o, GSet ∅)) ∗
      R V
    ∨ own γ (◯ (ε, GSet {[o]}))
    ).

  Definition is_lock (γ : gname) (lk : val) (R : vProp Σ) : vProp Σ :=
    ∃ lo ln : location,
    ⌜lk = (#lo, #ln)%V⌝ ∗
    ⎡inv N (lock_inv γ lo ln R)⎤.

  Definition issued (γ : gname) (x : nat) : vProp Σ :=
    ⎡own γ (◯ (ε, GSet {[x]}))⎤.

  Definition locked (γ : gname) : vProp Σ :=
    ∃ o,
    ⎡own γ (◯ (Excl' o, GSet ∅))⎤.

  #[global] Instance lock_inv_ne γ lo ln :
    NonExpansive (lock_inv γ lo ln).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance is_lock_ne γ lk :
    NonExpansive (is_lock γ lk).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance is_lock_persistent γ lk R :
    Persistent (is_lock γ lk R).
  Proof.
    apply _.
  Qed.
  #[global] Instance locked_timeless γ :
    Timeless (locked γ).
  Proof.
    apply _.
  Qed.

  Lemma locked_exclusive (γ : gname) :
    locked γ -∗
    locked γ -∗
    False.
  Proof.
    iDestruct 1 as (o1) "H1". iDestruct 1 as (o2) "H2".
    iDestruct (own_valid_2 with "H1 H2") as %[[] _]%auth_frag_op_valid_1.
  Qed.

  Lemma newlock_spec (R : vProp Σ) :
    {{{
      R
    }}}
      newlock #()
    {{{ lk γ,
      RET lk;
      is_lock γ lk R
    }}}.
  Proof.
    iIntros (Φ) "HR HΦ". rewrite -wp_fupd. wp_lam.
    iDestruct (monPred_in_intro with "HR") as (V) "[ #? ? ]".
    wp_ref ln as "Hln". wp_ref lo at V as "Hlo".
    iMod (own_alloc (● (Excl' 0%nat, GSet ∅) ⋅ ◯ (Excl' 0%nat, GSet ∅))) as (γ) "[Hγ Hγ']".
    { by apply auth_both_valid_discrete. }
    iMod (inv_alloc _ _ (lock_inv γ lo ln R) with "[-HΦ]").
    { iNext. rewrite /lock_inv.
      iExists 0%nat, 0%nat, V. iFrame. iLeft. by iFrame. }
    wp_pures. iModIntro. iApply ("HΦ" $! (#lo, #ln)%V γ). iExists lo, ln. eauto.
  Qed.

  Lemma wait_loop_spec γ lk x R :
    {{{
      is_lock γ lk R ∗
      issued γ x
    }}}
      wait_loop #x lk
    {{{
      RET #();
      locked γ ∗
      R
    }}}.
  Proof.
    iIntros (Φ) "[Hl Ht] HΦ". iDestruct "Hl" as (lo ln ->) "#Hinv".
    iLöb as "IH". wp_rec. subst. wp_pures. wp_bind (Read Atomic _ _)%E.
    iInv N as (o n V) "(Hlo & Hln & Ha)".
    wp_read. destruct (decide (x = o)) as [->|Hneq].
    - iDestruct "Ha" as "[Hainv [[Ho HR] | Haown]]".
      + iModIntro. iSplitL "Hlo Hln Hainv Ht".
        { iNext. iExists o, n, V. iFrame. }
        wp_pures. case_bool_decide; [|done]. wp_if.
        iApply ("HΦ" with "[-]").
        iDestruct (monPred_in_elim R V with "[$] [$]") as "$".
        rewrite /locked. eauto.
      + iDestruct (own_valid_2 with "Ht Haown") as % [_ ?%gset_disj_valid_op]%auth_frag_op_valid_1.
        set_solver.
    - iModIntro. iSplitL "Hlo Hln Ha".
      { iNext. iExists o, n, V. by iFrame. }
      wp_pures. case_bool_decide; [simplify_eq |].
      wp_if. iApply ("IH" with "Ht"). iNext. by iExact "HΦ".
  Qed.

  Lemma acquire_spec γ lk R :
    {{{
      is_lock γ lk R
    }}}
      acquire lk
    {{{
      RET #();
      locked γ ∗
      R
    }}}.
  Proof.
    iIntros (ϕ) "Hl HΦ". iDestruct "Hl" as (lo ln ->) "#Hinv".
    iLöb as "IH". wp_rec. wp_proj. wp_bind (Read Atomic _ _)%E.
    iInv N as (o n V) "[Hlo [Hln Ha]]".
    wp_read. iModIntro. iSplitL "Hlo Hln Ha".
    { iNext. iExists o, n, V. by iFrame. }
    wp_pures. wp_bind (CAS_ref _ _ _).
    iInv N as (o' n' V') "(>Hlo' & >Hln' & >Hauth & Haown)".
    destruct (decide (#n' = #n))%V as [[= ->%Nat2Z.inj] | Hneq].
    - iMod (own_update with "Hauth") as "[Hauth Hofull]".
      { eapply auth_update_alloc, prod_local_update_2.
        eapply (gset_disj_alloc_empty_local_update _ {[ n ]}).
        apply (set_seq_S_end_disjoint 0). }
      rewrite -(set_seq_S_end_union_L 0).
      wp_cas_suc. iModIntro. iSplitL "Hlo' Hln' Haown Hauth".
      { iNext. iExists o', (S n).
        rewrite Nat2Z.inj_succ -Z.add_1_r. iExists V'. by iFrame. }
      wp_pures.
      iApply (wait_loop_spec γ (#lo, #ln) with "[-HΦ]").
      + iFrame. rewrite /is_lock; eauto 10.
      + by iNext.
    - wp_cas_fail. iModIntro.
      iSplitL "Hlo' Hln' Hauth Haown".
      { iNext. iExists o', n', V'. by iFrame. }
      wp_pures. by iApply "IH".
  Qed.

  Lemma release_spec γ lk R :
    {{{
      is_lock γ lk R ∗
      locked γ ∗
      R
    }}}
      release lk
    {{{
      RET #();
      True
    }}}.
  Proof.
    iIntros (Φ) "(Hl & Hγ & HR) HΦ". iDestruct "Hl" as (lo ln ->) "#Hinv".
    iDestruct "Hγ" as (o) "Hγo".
    wp_lam. wp_proj. wp_bind (Read Atomic _ _)%E.
    iInv N as (o' n V) "(>Hlo & >Hln & >Hauth & Haown)".
    wp_read as "_". iDestruct (own_valid_2 with "Hauth Hγo") as
      %[[<-%Excl_included%leibniz_equiv _]%prod_included _]%auth_both_valid_discrete.
    iModIntro. iSplitL "Hlo Hln Hauth Haown".
    { iNext. iExists o, n, V. by iFrame. }
    wp_pures.
    iInv N as (o' n' V') "(>Hlo & >Hln & >Hauth & Haown)".
    iApply wp_fupd.
    iDestruct (monPred_in_intro with "HR") as (VR) "[#? ?]".
    wp_write at VR as "_". iDestruct (own_valid_2 with "Hauth Hγo") as
      %[[<-%Excl_included%leibniz_equiv _]%prod_included _]%auth_both_valid_discrete.
    iDestruct "Haown" as "[[Hγo' _]|Haown]".
    { iDestruct (own_valid_2 with "Hγo Hγo'") as %[[] ?]%auth_frag_op_valid_1. }
    iMod (own_update_2 with "Hauth Hγo") as "[Hauth Hγo]".
    { apply auth_update, prod_local_update_1.
      by apply option_local_update, (exclusive_local_update _ (Excl (S o))). }
    iModIntro. iSplitR "HΦ"; last by iApply "HΦ".
    iIntros "!> !>". iExists (S o), n', VR.
    rewrite Nat2Z.inj_succ -Z.add_1_r. iFrame. iLeft. by iFrame.
  Qed.
End proof.

#[global] Typeclasses Opaque is_lock issued locked.
