From iris.algebra Require Import
  gmap
  auth
  frac
  agree
  csum.
From iris.program_logic Require Import
  adequacy.

From cosmo Require Import
  prelude.
From cosmo.iris.base_logic Require Import
  lib.lattice.
From cosmo.language Require Import
  notations.
From cosmo.language Require Import
  lifting
  store
  weakestpre.

Class cosmoPreG Σ := CosmoPreG {
  #[global] cosmoPreG_invPreG :: invGpreS Σ;
  #[global] cosmoPreG_store_inG :: inG Σ (authR storeUR);
  #[global] cosmoPreG_lenstore_inG :: inG Σ (authR lenstoreUR);
  #[global] cosmoPreG_seen_inG :: inG Σ (authR seenUR)
}.

Definition cosmoΣ : gFunctors := #[
  invΣ;
  GFunctor (authR storeUR);
  GFunctor (authR lenstoreUR);
  GFunctor (authR seenUR)
].
#[global] Instance subG_noprolPreG {Σ} :
  subG cosmoΣ Σ →
  cosmoPreG Σ.
Proof.
  solve_inG.
Qed.

Theorem basecosmo_adequacy Σ `{cosmoPreG Σ} (e : expr) (φ : view_lang.val → Prop) :
  (∀ `{cosmoG Σ}, ⊢ WP (e at ∅) {{ vV, ⌜φ vV⌝ }}) →
  adequate NotStuck (e at ∅) ∅ (λ vV _, φ vV).
Proof.
  intros Hwp. apply (wp_adequacy _ _).
  iIntros (Hinv ?).
  iMod (own_alloc (● (∅ : storeUR))) as (store_name) "store".
  { by apply auth_auth_valid. }
  iMod (own_alloc (● (∅ : lenstoreUR))) as (lenstore_name) "lenstore".
  { by apply auth_auth_valid. }
  iMod (own_alloc (● (to_latT ∅ : seenUR) ⋅ ◯ to_latT ∅)) as (seen_name) "[seenA #seen]".
  { by apply auth_both_valid_discrete. }
  set (STOREG := StoreG Σ _ store_name _ lenstore_name).
  set (SEENG := SeenG Σ _ seen_name).
  set (COSMOG := CosmoG Σ _ _ _).
  specialize (Hwp COSMOG).
  iExists _, _.
  iSplitL; last by iApply Hwp. simpl. iSplitL "store lenstore".
  - rewrite /store_interp /store_to_cmra /store_to_lenstore_cmra 2!fmap_empty.
    by iFrame.
  - rewrite /seen_interp. iExists ∅. iFrame. iPureIntro.
    split ; last split ; intros [ℓ i].
    + intros ??. rewrite store_lookup_eq. by case_bool_decide.
    + intros ?. rewrite store_lookup_eq. by case_bool_decide.
    + done.
Qed.

Theorem cosmo_adequacy Σ `{cosmoPreG Σ} (e : expr) (φ : val → Prop) :
  (∀ `{cosmoG Σ}, ⊢ WP e {{ v, ⌜φ v⌝ }}) →
  adequate NotStuck (e at ∅) ∅ (λ v _, φ v).
Proof.
  intros Hwp. apply (basecosmo_adequacy _).
  iIntros (COSMOG).
  iAssert (|==> seen ∅)%I as ">Hseen". { rewrite seen_eq. by iApply own_unit. }
  specialize (Hwp COSMOG). destruct Hwp as [Hwp]. rewrite wp_eq in Hwp.
  iApply (iris.program_logic.weakestpre.wp_wand with "[Hseen]").
  iApply (Hwp ∅ with "[//] [//] Hseen").
  iIntros ([v V]) "[_ ?] //".
Qed.
