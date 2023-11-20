From Coq.Program Require Import
  Program.

From iris.algebra Require Import
  gmap
  excl
  auth.
From iris.program_logic Require
  weakestpre.
From iris.program_logic Require Import
  ownp.
From iris.proofmode Require Export
  tactics.

From cosmo.iris.base_logic Require Import
  lib.lattice.
From cosmo.language Require Export
  vprop.

Notation seenUR := (
  latUR view_Lat
).

Class seenG Σ : Type := SeenG {
  #[global] seen_inG :: inG Σ (authR seenUR) ;
  seen_name : gname ;
}.

Section Seen.
  Context `{!seenG Σ}.

  Definition seen_def (V : view) : iProp Σ :=
    own seen_name (◯ to_latT V).
  Definition seen_aux :
    seal (@seen_def). Proof. by eexists. Qed.
  Definition seen :=
    unseal seen_aux.
  Definition seen_eq : @seen = @seen_def :=
    seal_eq seen_aux.

  #[global] Instance seen_timeless V :
    Timeless (seen V).
  Proof.
    rewrite seen_eq. apply _.
  Qed.

  #[global] Instance seen_persistent V :
    Persistent (seen V).
  Proof.
    rewrite seen_eq. apply _.
  Qed.

  #[global] Instance seen_mono :
    Proper ((⊑) ==> flip (⊢)) seen.
  Proof.
    rewrite seen_eq /seen_def. iIntros (?? Ext) "own".
    iApply (@own_lat_auth_downclosed with "own"). apply Ext.
  Qed.
  #[global] Instance seen_mono_flip :
    Proper (flip (⊑) ==> (⊢)) seen.
  Proof.
    intros ???. by apply seen_mono.
  Qed.

  Lemma seen_join (V1 V2 : view) :
    seen V1 -∗
    seen V2 -∗
    seen (V1 ⊔ V2).
  Proof.
    rewrite seen_eq. iIntros "H1 H2". by iCombine "H1 H2" as "H".
  Qed.

  Definition seen_interp (σ : store) : iProp Σ :=
    ∃ V,
    own seen_name (● to_latT V) ∗
    ⌜∀ ℓi v Vℓ, σ !! ℓi = Some (store_elt_at v Vℓ) → Vℓ ⊑ V⌝ ∗
    ⌜∀ ℓi h, σ !! ℓi = Some (store_elt_na h) → is_Some (h !! (V !! ℓi))⌝ ∗
    ⌜∀ ℓi, σ !! ℓi = None → V !! ℓi = None⌝.
End Seen.

Section WeakestPre.
  Context `{!irisGS view_lang Σ, !seenG Σ}.

  Implicit Types Φ : val → vProp Σ.
  Implicit Types P Q : vProp Σ.
  Implicit Types E : coPset.
  Implicit Types e : expr.

  Lemma wp_larger_view_post E e (Φ : view_lang.val → iProp Σ) V :
    WP (mkExpr e V) @ E {{ Φ }} ⊢
    WP (mkExpr e V) @ E {{ λ vV', ⌜V ⊑ vV'.(view_lang.val_view)⌝ ∗ Φ vV' }}%V.
  Proof.
    iLöb as "IH" forall (e V). iIntros "WP".
    rewrite !wp_unfold /wp_pre /= /view_lang.to_val /=.
    destruct (to_val e) as [v|] eqn:EQe; simpl; [by iSplitL ""|].
    iIntros (σ ? ? ? ?) "Hσ".
    iMod ("WP" $! σ with "Hσ") as "[$ WP]".
    iIntros "!>" (e' σ' efs [K [e_ ?] [e_' V'] He1'%eq_sym He2'%eq_sym STEP]) "?".
    iMod ("WP" $! e' σ' efs with "[%] [$]") as "WP". { by econstructor. }
    iIntros "!> !>".
    iMod "WP". iModIntro.
    iApply (step_fupdN_wand with "WP"). iIntros ">($ & WP & $)".
    rewrite /= -!fill_base_view in He1', He2'. inversion He1'. subst.
    iModIntro. iSpecialize ("IH" $! _ _ with "WP").
    iApply (wp_wand with "IH"); [done..|]. iIntros (?) "(% & $)". iPureIntro. etrans.
    apply (view_lang.head_step_view_sqsubseteq _ _ _ _ _ _ _ _ STEP). done.
  Qed.

  Program Definition wp_def E e Φ : vPropI Σ :=
    MonPred (λ V0,
      ∀ V, ⌜V0 ⊑ V⌝ -∗ seen V -∗
        WP (mkExpr e V) @ E {{ λ vV',
          let '(mkVal v V') := vV' return _ in seen V' ∗ (Φ v) V'
        }}
    )%I _.
  Next Obligation.
    solve_proper.
  Qed.
  Definition wp_aux : seal (@wp_def).
    Proof. by eexists. Qed.
  #[global] Instance wp' : Wp (vProp Σ) expr val stuckness :=
    λ _, unseal (wp_aux).
  Definition wp_eq : wp NotStuck = _ :=
    seal_eq _.

  #[global] Instance wp_ne E e n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (wp NotStuck E e).
  Proof.
    rewrite wp_eq. split=>V. solve_proper.
  Qed.
  #[global] Instance wp_proper E e :
    Proper (pointwise_relation _ (≡) ==> (≡)) (@wp _ _ _ _ wp' NotStuck E e).
  Proof.
    rewrite wp_eq. split=>V0. solve_proper.
  Qed.

  Lemma wp_value E Φ v :
    Φ v ⊢
    WP Val v @ E {{ Φ }}.
  Proof.
    iStartProof (iProp _). rewrite wp_eq /wp_def. iIntros "% HΦ %% ?".
    iApply (wp_value' _ _ _ (mkVal v _)). iFrame.
  Qed.

  Lemma wp_strong_mono E1 E2 e Φ Ψ :
    E1 ⊆ E2 →
    WP e @ E1 {{ Φ }} -∗
    (∀ v, Φ v ={E2}=∗ Ψ v) -∗
    WP e @ E2 {{ Ψ }}.
  Proof.
    iStartProof (iProp _). rewrite wp_eq /wp_def. iIntros "%% WP %-> H /=" (V HV) "#Hseen".
    iApply (wp_strong_mono NotStuck _ E1 with "[WP]"); [done|done| |].
    { iApply wp_larger_view_post. by iApply ("WP" $! V with "[-] Hseen"). }
    iIntros ([v V']) "/= (% & [$ HΦ])". iSpecialize ("H" $! v).
    rewrite (monPred_mono _ _ _ HV) //. iApply ("H" with "HΦ").
  Qed.

  Lemma fupd_wp E e Φ :
    (|={E}=> WP e @ E {{ Φ }}) ⊢
    WP e @ E {{ Φ }}.
  Proof.
    rewrite wp_eq /wp_def. iStartProof (iProp _). iIntros "% H".
    iMod "H". by iApply "H".
  Qed.

  Lemma wp_fupd E e Φ :
    WP e @ E {{ λ v, |={E}=> Φ v }} ⊢
    WP e @ E {{ Φ }}.
  Proof.
    iStartProof (iProp _). rewrite wp_eq /wp_def. iIntros "% H %% #Hseen".
    iApply wp_fupd. iApply wp_mono; [|by iApply ("H" with "[//]")].
    by iIntros ([??]) "[$ ?]".
  Qed.

  Lemma wp_atomic E1 E2 e Φ `{!AtomicExpr e} :
    (|={E1,E2}=> WP e @ E2 {{ λ v, |={E2,E1}=> Φ v }}) ⊢
    WP e @ E1 {{ Φ }}.
  Proof.
    iStartProof (iProp _). rewrite wp_eq /wp_def. iIntros "% H %% Hseen".
    iApply wp_atomic. iMod "H". iModIntro.
    iApply wp_mono; [|by iApply ("H" with "[//]")]. by iIntros ([??]) "[$ ?]".
  Qed.

  Lemma wp_step_fupd E1 E2 e P Φ :
    to_val e = None →
    E2 ⊆ E1 →
    (|={E1}[E2]▷=> P) -∗
    WP e @ E2 {{ λ v, P ={E1}=∗ Φ v }} -∗
    WP e @ E1 {{ Φ }}.
  Proof.
    iStartProof (iProp _). rewrite wp_eq /wp_def.
    iIntros (He ? V0) "VS %% WP %% #Hseen /=".
    iApply (wp_step_fupd with "VS"); [by rewrite /= /view_lang.to_val /= He|done|].
    iDestruct (wp_larger_view_post with "[WP]") as "WP"; [by iApply "WP"|].
    iApply wp_mono; [|by iApply "WP"]. iIntros ([v V']) "(% & $ & H) H'".
    by iApply ("H" with "[H']").
  Qed.

  Lemma wp_bind (K : list ectx_item) E e Φ :
    WP e @ E {{ v, WP fill K (Val v) @ E {{ Φ }} }} ⊢
    WP fill K e @ E {{ Φ }}.
  Proof.
    iStartProof (iProp _). rewrite wp_eq /=. iIntros "% Hwp" (V ?) "#Hseen".
    rewrite fill_base_view. iApply wp_bind.
    iApply (wp_wand with "[Hwp]"). iApply "Hwp"=>//.
    iIntros ([v V']) "[Hseen' Hwp]". rewrite -fill_base_view.
    by iApply "Hwp".
  Qed.
End WeakestPre.

#[global] Arguments wp' {_ _} _ _ _%E _%I.

Section WeakestPre_derived.
  Context `{!irisGS view_lang Σ, !seenG Σ}.

  Implicit Types Φ Ψ : val → vProp Σ.
  Implicit Types E: coPset.
  Implicit Types e : expr.
  Implicit Types P Q : vProp Σ.
  Implicit Types 𝓟 : iProp Σ.

  Lemma wp_mono E e Φ Ψ :
    (∀ v, Φ v ⊢ Ψ v) →
    WP e @ E {{ Φ }} ⊢
    WP e @ E {{ Ψ }}.
  Proof.
    iIntros (HΦ) "H"; iApply (wp_strong_mono with "H"); auto.
    iIntros (v) "?". by iApply HΦ.
  Qed.
  Lemma wp_mask_mono E1 E2 e Φ :
    E1 ⊆ E2 →
    WP e @ E1 {{ Φ }} ⊢
    WP e @ E2 {{ Φ }}.
  Proof.
    iIntros (?) "H"; iApply (wp_strong_mono with "H"); auto.
  Qed.
  #[global] Instance wp_mono' E e :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp NotStuck E e).
  Proof.
    by intros Φ Φ' ?; apply wp_mono.
  Qed.

  Lemma wp_value_fupd E Φ v :
    (|={E}=> Φ v) ⊢
    WP Val v @ E {{ Φ }}.
  Proof.
    intros. by rewrite -wp_fupd -wp_value.
  Qed.

  Lemma wp_frame_l E e Φ R :
    R ∗ WP e @ E {{ Φ }} ⊢
    WP e @ E {{ v, R ∗ Φ v }}.
  Proof.
    iIntros "[? H]". iApply (wp_strong_mono with "H"); auto with iFrame.
  Qed.
  Lemma wp_frame_r E e Φ R :
    WP e @ E {{ Φ }} ∗ R ⊢
    WP e @ E {{ v, Φ v ∗ R }}.
  Proof.
    iIntros "[H ?]". iApply (wp_strong_mono with "H"); auto with iFrame.
  Qed.

  Lemma wp_frame_step_l E1 E2 e Φ R :
    to_val e = None →
    E2 ⊆ E1 →
    (|={E1}[E2]▷=> R) ∗ WP e @ E2 {{ Φ }} ⊢
    WP e @ E1 {{ v, R ∗ Φ v }}.
  Proof.
    iIntros (??) "[Hu Hwp]". iApply (wp_step_fupd with "Hu"); try done.
    iApply (wp_mono with "Hwp"). by iIntros (?) "$$".
  Qed.
  Lemma wp_frame_step_r E1 E2 e Φ R :
    to_val e = None →
    E2 ⊆ E1 →
    WP e @ E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢
    WP e @ E1 {{ v, Φ v ∗ R }}.
  Proof.
    rewrite [(WP _ @ _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
    apply wp_frame_step_l.
  Qed.
  Lemma wp_frame_step_l' E e Φ R :
    to_val e = None →
    ▷ R ∗ WP e @ E {{ Φ }} ⊢
    WP e @ E {{ v, R ∗ Φ v }}.
  Proof.
    iIntros (?) "[??]". iApply (wp_frame_step_l E E); try iFrame; eauto.
  Qed.
  Lemma wp_frame_step_r' E e Φ R :
    to_val e = None →
    WP e @ E {{ Φ }} ∗ ▷ R ⊢
    WP e @ E {{ v, Φ v ∗ R }}.
  Proof.
    iIntros (?) "[??]". iApply (wp_frame_step_r E E); try iFrame; eauto.
  Qed.

  Lemma wp_wand E e Φ Ψ :
    WP e @ E {{ Φ }} -∗
    (∀ v, Φ v -∗ Ψ v) -∗
    WP e @ E {{ Ψ }}.
  Proof.
    iIntros "Hwp H". iApply (wp_strong_mono with "Hwp"); auto.
    iIntros (?) "?". by iApply "H".
  Qed.
  Lemma wp_wand_l E e Φ Ψ :
    (∀ v, Φ v -∗ Ψ v) ∗ WP e @ E {{ Φ }} ⊢
    WP e @ E {{ Ψ }}.
  Proof.
    iIntros "[H Hwp]". by iApply (wp_wand with "Hwp H").
  Qed.
  Lemma wp_wand_r E e Φ Ψ :
    WP e @ E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢
    WP e @ E {{ Ψ }}.
  Proof.
    iIntros "[Hwp H]". by iApply (wp_wand with "Hwp H").
  Qed.
  Lemma wp_frame_wand_l s E e Q Φ :
    Q ∗ WP e @ s; E {{ v, Q -∗ Φ v }} ⊢
    WP e @ s; E {{ Φ }}.
  Proof.
    iIntros "[HQ HWP]". iApply (wp_wand with "HWP").
    iIntros (v) "HΦ". by iApply "HΦ".
  Qed.

  #[global] Instance frame_wp p E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ E {{ Φ }}) (WP e @ E {{ Ψ }}).
  Proof.
    rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR.
  Qed.

  #[global] Instance is_except_0_wp E e Φ :
    IsExcept0 (WP e @ E {{ Φ }}).
  Proof.
    by rewrite /IsExcept0 -{2}fupd_wp// -except_0_fupd -fupd_intro.
  Qed.

  #[global] Instance elim_modal_bupd_wp p E e P Φ :
    ElimModal True p false (|==> P) P (WP e @ E {{ Φ }}) (WP e @ E {{ Φ }}).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd_wp.
  Qed.

  #[global] Instance elim_modal_fupd_wp p E e P Φ :
    ElimModal True p false (|={E}=> P) P (WP e @ E {{ Φ }}) (WP e @ E {{ Φ }}).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim fupd_frame_r bi.wand_elim_r fupd_wp.
  Qed.

  #[global] Instance elim_modal_fupd_wp_atomic p E1 E2 e P Φ :
    AtomicExpr e →
    ElimModal True p false (|={E1,E2}=> P) P (WP e @ E1 {{ Φ }}) (WP e @ E2 {{ v, |={E2,E1}=> Φ v }})%I.
  Proof.
    intros. by rewrite /ElimModal bi.intuitionistically_if_elim fupd_frame_r bi.wand_elim_r wp_atomic.
  Qed.

  #[global] Instance add_modal_fupd_wp E e P Φ :
    AddModal (|={E}=> P) P (WP e @ E {{ Φ }}).
  Proof.
    intros. by rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd_wp.
  Qed.

  #[global] Instance elim_acc_wp {X} E1 E2 α β γ e Φ :
    AtomicExpr e →
    ElimAcc (X := X) True (fupd E1 E2) (fupd E2 E1) α β γ (WP e @ E1 {{ Φ }}) (λ x, WP e @ E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    intros ? ?.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  #[global] Instance elim_acc_wp_nonatomic {X} E α β γ e Φ :
    ElimAcc (X := X) True (fupd E E) (fupd E E) α β γ (WP e @ E {{ Φ }}) (λ x, WP e @ E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    intros ?.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply wp_fupd. iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.
End WeakestPre_derived.
