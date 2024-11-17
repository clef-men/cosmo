From iris.algebra Require Import
  excl
  csum
  agree.
From iris.base_logic Require Import
  invariants.

From cosmo Require Import
  prelude.
From cosmo.language Require Export
  proofmode.

Set Default Proof Using "Type".

Section escrow.
  Context `{!cosmoG Σ}.

  Definition escrowN id : namespace :=
    nroot .@ "escrow" .@ string_of_pos id.

  Definition escrow_id := namespace.

  Implicit Types (σ : escrow_id) (P : vProp Σ) (Q : vProp Σ) (V : view).

  Definition escrow σ P Q : vProp Σ :=
    ∃ V,
    monPred_in V ∗
    ⎡inv σ ((∃ V0, P V0) ∨ Q V)⎤.

  Theorem escrow_intro σ P Q (E : coPset) :
    Q ⊢ |={E}=>
    escrow σ P Q.
  Proof.
    iIntros "HQ". iDestruct (monPred_in_intro with "HQ") as (V) "[HV HQ]".
    iExists V. iFrame "HV". rewrite -embed_fupd. iModIntro. iApply inv_alloc. by auto.
  Qed.

  Theorem escrow_elim σ P Q (E : coPset) :
    ↑σ ⊆ E →
    (P ∗ P ⊢ False) →
    P ∗ escrow σ P Q ⊢ |={E}=>
    ▷ Q.
  Proof.
    iIntros (? Hexcl) "[HP Hesc]". iDestruct "Hesc" as (V) "[HV Hinv]".
    iMod (inv_acc with "Hinv") as "[H Hclose]"; first done.
    iDestruct "H" as "[HP'|HQ]".
    {
      iAssert (▷False)%I as "#Hfalse".
      { iNext. rewrite -embed_pure.
        iDestruct "HP'" as (V2) "HP2".
        iDestruct (monPred_in_intro with "HP") as (V1) "[_ HP1]".
        iModIntro. iDestruct (Hexcl $! (V1 ⊔ V2) with "[$]") as "$". }
      iMod ("Hclose" with "[Hfalse]"); last iModIntro; by iNext. }
    { rewrite -monPred_at_later.
      iDestruct (monPred_in_elim with "HV HQ") as "$".
      iDestruct (monPred_in_intro with "HP") as (V1) "[_ HP]".
      by iMod ("Hclose" with "[HP]"); iModIntro; auto. }
  Qed.

  #[global] Instance escrow_persistent σ P Q : Persistent (escrow σ P Q) := _.
End escrow.
