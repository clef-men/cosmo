From iris.algebra Require Import
  excl.
From iris.base_logic Require Import
  invariants.

From cosmo Require Import
  prelude.
From cosmo.language Require Export
  proofmode.

Set Default Proof Using "Type".

(** Implementation **)

Definition make : val := λ: <>,
  ref_at #false.

Definition try_acquire : val := λ: "lock",
  CAS_ref "lock" #false #true.

Definition acquire : val := rec: "acq" "lock" :=
  if: try_acquire "lock" then
    #()
  else
    "acq" "lock".

Definition release : val := λ: "lock",
  "lock" <-at #false.

(** Specification **)

(* the CMRA we need *)
Class slockG Σ := {
  #[local] slock_G :: inG Σ (exclR unitO) ;
}.

Section Spec.

  Context `{!cosmoG Σ, !slockG Σ}.

  Implicit Types (γ : gname) (lk : location) (P : vProp Σ) (V : view).

  Definition lockN lk : namespace :=
    nroot .@ "spinlock" (*.@ string_of_pos lk*).

  Definition locked γ : iProp Σ :=
    own γ (Excl tt).

  (*
     ICFP20: “is_lock” is the assertion “IsSpinLock” from the paper, Section 5.2.
     We added an exclusive token “locked γ” to keep the spec in line with more
     elaborate implementations of locks.

     “inv (lockN lk) Q” is an invariant assertion whose expression is Q.
     “lockN lk” is the namespace of this invariant, it is an Iris technicality.
     The ceiling brackets ⎡I⎤ turn the iProp assertion I into a vProp assertion,
     as seen in the article when building the lifted logic Cosmo.
  *)

  Definition lock_inv γ lk P : iProp Σ :=
    ( ∃ V,
      lk ↦at(#false, V) ∗
      locked γ ∗
      P V
    ) ∨ (
      lk ↦at #true
    ).

  Definition is_lock γ lk P : vProp Σ :=
    ⎡inv (lockN lk) (lock_inv γ lk P)⎤.

  Lemma locked_exclusive γ :
    ⊢@{vProp _}
      ⎡locked γ⎤ -∗
      ⎡locked γ⎤ -∗
      False.
  Proof.
    iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %Hvalid. iPureIntro.
    by apply (excl_exclusive (Excl tt) (Excl tt)), Hvalid.
  Qed.

  Theorem make_spec P :
    {{{
      P
    }}}
      make #()
    {{{ γ lk,
      RET #lk;
      is_lock γ lk P
    }}}.
  Proof.
    iIntros (Φ) "HP Post".
    iApply wp_fupd.
    iDestruct (monPred_in_intro with "HP") as (V) "[#? ?]".
    wp_lam. wp_ref lk at V.
    iMod (own_alloc (Excl tt)) as (γ) "Hlocked"; first done.
    iApply "Post".
    iMod (inv_alloc _ _ (lock_inv γ lk P) with "[-]") as "$"; last done.
    iLeft; iExists V; by iFrame.
  Qed.

  Theorem try_acquire_spec γ lk P :
    {{{
      is_lock γ lk P
    }}}
      try_acquire #lk
    {{{ (b : bool),
      RET #b ;
      if b then ⎡locked γ⎤ ∗ P else True
    }}}.
  Proof.
    iIntros (Φ) "#Hlock Post".
    wp_lam.
    iInv (lockN lk) as "[(%V & Hlk & HP) | Hlk]".
    {
      wp_cas_suc. iModIntro. iSplitL "Hlk".
      - by iRight.
      - iApply "Post". by iApply monPred_in_elim.
    }{
      wp_cas_fail as "_". iModIntro. iSplitL "Hlk".
      - by iRight.
      - by iApply "Post".
    }
  Qed.

  Theorem acquire_spec γ lk P :
    {{{ is_lock γ lk P }}}
      acquire #lk
    {{{ RET #() ; ⎡locked γ⎤ ∗ P }}}.
  Proof.
    iIntros (Φ) "#Hlock Post". iLöb as "IH".
    wp_rec. wp_apply (try_acquire_spec with "Hlock") ; iIntros ([|]).
    - iIntros "?". wp_if. by iApply "Post".
    - iIntros "_". wp_if. by iApply "IH".
  Qed.

  Theorem release_spec γ lk P :
    {{{ is_lock γ lk P ∗ ⎡locked γ⎤ ∗ P }}}
      release #lk
    {{{ RET #() ; True }}}.
  Proof.
    iIntros (Φ) "[#Hlock HP] Post".
    wp_lam.
    iInv (lockN lk) as "H".
    iDestruct "H" as "[H | >Hlk]" ; first iDestruct "H" as (V) "[>Hlk HP']".
    {
      wp_write at V. iModIntro.
      iSplitR "Post" ; last by iApply "Post".
      iLeft. iExists V. by iFrame.
    }{
      iDestruct (monPred_in_intro with "HP") as (V) "[#? ?]".
      wp_write at V. iModIntro.
      iSplitR "Post" ; last by iApply "Post".
      iLeft. iExists V. by iFrame.
    }
  Qed.
End Spec.
