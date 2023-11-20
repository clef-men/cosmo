From stdpp Require Import
  namespaces.

From iris.algebra Require Import
  gmap
  auth
  frac
  agree
  csum.
From iris.bi Require Import
  fractional.
From iris.base_logic Require Import
  lib.own.
From iris.proofmode Require Export
  tactics.

From cosmo Require Import
  prelude.
From cosmo.common Require Import
  gmap.
From cosmo.language Require Import
  vprop.

Notation histO := (
  gmapO timestamp valO
).

Notation atomO := (
  prodO valO (gmapO locoff fracO)
).

Notation store_eltR := (
  prodR (csumR (agreeR atomO) (agreeR histO)) fracR
).
Notation storeUR := (
  gmapUR locoff store_eltR
).

Notation lenstoreUR := (
  gmapUR location (agreeR ZO)
).

Class storeG Σ := StoreG {
  #[global] store_inG :: inG Σ (authR storeUR) ;
  store_name : gname ;
  #[global] lenstore_inG :: inG Σ (authR lenstoreUR) ;
  lenstore_name : gname ;
}.

Definition storeN : namespace :=
  nroot .@ "store".

Definition elt_to_cmra (elt : store_elt) : store_eltR :=
  ( match elt with
    | store_elt_at v V =>
        Cinl (to_agree (v, V))
    | store_elt_na h =>
        Cinr (to_agree h)
    end,
    1%Qp
  ).

#[global] Instance pair_to_locoff_nat_inj :
  Inj eq eq (λ '(ℓ, i), Locoff ℓ (Z.of_nat i)).
Proof.
  move=> [??] [??] [= -> /(inj Z.of_nat) -> //].
Qed.

Definition store_to_cmra (σ : store) : storeUR :=
  gmap_fmap_dom (λ '(ℓ, i), Locoff ℓ (Z.of_nat i)) $
  gmap_uncurry $
  fmap (λ blk,
    fmap elt_to_cmra (map_seq 0 blk : gmap nat _)
  ) σ.

Lemma lookup_store_to_cmra_neg σ ℓ i :
  (i < 0)%Z →
  store_to_cmra σ !! ℓ.[i] = None.
Proof.
  intros Hineq. destruct (store_to_cmra σ !! ℓ.[i]) eqn:Heq ; [exfalso | done].
  apply mk_is_Some, lookup_gmap_map_dom_ne in Heq as [[ℓ' i'] [=]]. lia.
Qed.

Lemma lookup_store_to_cmra σ ℓi :
  store_to_cmra σ !! ℓi = elt_to_cmra <$> (σ !! ℓi).
Proof.
  destruct ℓi as [ℓ i]. rewrite [lookup (Locoff _ _) σ]/lookup /store_lookup.
  destruct (decide (0 ≤ i)%Z).
  - rewrite /store_to_cmra -{1}(Z2Nat.id i) ; last done.
    rewrite (lookup_gmap_fmap_dom _ _ (ℓ, Z.to_nat i)) lookup_gmap_uncurry lookup_fmap.
    rewrite bool_decide_true ; last lia.
    case: (σ !! ℓ) => [blk|] ; setoid_subst ; last done.
    by rewrite lookup_fmap lookup_map_seq_0.
  - case_bool_decide; first done. cbn.
    apply lookup_store_to_cmra_neg. lia.
Qed.

Lemma store_to_cmra_insert_block σ ℓ blk :
  σ !! ℓ = None →
  store_to_cmra (<[ℓ := blk]> σ) ≡ store_to_cmra {[ ℓ := blk ]} ⋅ store_to_cmra σ.
Proof.
  intros Hfresh [ℓ' i'].
  rewrite lookup_op.
  destruct (decide (0 ≤ i')%Z).
  - rewrite /store_to_cmra -(Z2Nat.id i') ; last done.
    rewrite !(lookup_gmap_fmap_dom _ _ (_ ,_))
            !lookup_gmap_uncurry !lookup_fmap.
    destruct (decide (ℓ' = ℓ)) as [->|Hℓℓ'].
    + rewrite lookup_insert lookup_singleton Hfresh /= right_id //.
    + rewrite lookup_insert_ne // lookup_singleton_ne // left_id //.
  - rewrite !lookup_store_to_cmra_neg ; [ done | lia ..].
Qed.

Lemma store_to_cmra_insert σ ℓi elt elt' :
  σ !! ℓi = Some elt →
  store_to_cmra (<[ℓi := elt']> σ) ≡ <[ℓi := elt_to_cmra elt']> (store_to_cmra σ).
Proof.
  intros H ℓi'. rewrite lookup_store_to_cmra. destruct (decide (ℓi = ℓi')) as [<-|].
  - rewrite lookup_insert (store_lookup_insert _ _ elt) //.
  - rewrite lookup_insert_ne //. rewrite store_lookup_insert_ne //.
    by rewrite lookup_store_to_cmra.
Qed.

Definition store_to_lenstore_cmra (σ : store) : lenstoreUR :=
  fmap (λ (blk : list store_elt), to_agree (Z.of_nat (length blk))) σ.

Lemma lookup_store_to_lenstore_cmra σ ℓ :
  store_to_lenstore_cmra σ !! ℓ = (to_agree ∘ Z.of_nat ∘ length) <$> (σ !! ℓ).
Proof.
  by rewrite /store_to_lenstore_cmra lookup_fmap.
Qed.

Lemma store_to_lenstore_cmra_insert_block σ ℓ blk :
  σ !! ℓ = None →
  store_to_lenstore_cmra (<[ℓ := blk]> σ) ≡ {[ℓ := to_agree $ Z.of_nat $ length blk]} ⋅ store_to_lenstore_cmra σ.
Proof.
  intros Hfresh.
  rewrite /store_to_lenstore_cmra fmap_insert insert_singleton_op // lookup_fmap Hfresh //.
Qed.

Lemma store_to_lenstore_cmra_insert σ ℓi elt :
  store_to_lenstore_cmra (<[ℓi := elt]> σ) ≡ store_to_lenstore_cmra σ.
Proof.
  intros ℓ'. destruct ℓi as [ℓ i]. rewrite /insert /store_insert.
  case_bool_decide ; last done. rewrite lookup_store_to_lenstore_cmra.
  destruct (σ !! ℓ) as [blk|] eqn:E.
  - destruct (decide (ℓ = ℓ')) as [<-|].
    + rewrite lookup_insert /= insert_length lookup_store_to_lenstore_cmra E //.
    + rewrite lookup_insert_ne // lookup_store_to_lenstore_cmra //.
   - rewrite lookup_store_to_lenstore_cmra //.
Qed.

Section definitions.
  Context `{!storeG Σ}.

  Definition store_interp σ : iProp Σ :=
    own store_name (● store_to_cmra σ) ∗
    own lenstore_name (● store_to_lenstore_cmra σ).

  Definition hist_na_def ℓi (h : history) (q : frac) : iProp Σ :=
    own store_name (◯ {[ ℓi := (Cinr $ to_agree h, q) ]}).
  Definition hist_na_aux : seal (@hist_na_def).
    Proof. by eexists. Qed.
  Definition hist_na :=
    unseal hist_na_aux.
  Definition hist_na_eq : @hist_na = @hist_na_def :=
    seal_eq hist_na_aux.

  Definition mapsto_na ℓi (v : val) q : vProp Σ :=
    tc_opaque (
      ∃ V h,
      monPred_in V ∗
      ⎡hist_na ℓi h q⎤ ∗
      ⌜h !! (V !! ℓi) = Some v ∧ ∀ t, h !! t = None ∨ t ⊑ V !! ℓi⌝
    )%I.

  Definition mapsto_at_view_def ℓi (v : val) (V : view) (q : frac) : iProp Σ :=
    ∃ Vℓ,
    ⌜V ⊑ Vℓ⌝ ∗
    own store_name (◯ {[ ℓi := (Cinl $ to_agree (v, Vℓ), q) ]}).
  Definition mapsto_at_view_aux : seal (@mapsto_at_view_def).
    Proof. by eexists. Qed.
  Definition mapsto_at_view :=
    unseal mapsto_at_view_aux.
  Definition mapsto_at_view_eq : @mapsto_at_view = @mapsto_at_view_def :=
    seal_eq mapsto_at_view_aux.

  Definition has_length_def ℓ (n : Z) : iProp Σ :=
    own lenstore_name (◯ {[ ℓ := to_agree n ]}).
  Definition has_length_aux : seal (@has_length_def).
    Proof. by eexists. Qed.
  Definition has_length :=
    unseal has_length_aux.
  Definition has_length_eq : @has_length = @has_length_def :=
    seal_eq has_length_aux.
End definitions.

Notation "ℓi ↦{ q } v" := (
  mapsto_na ℓi v q
)(at level 20,
  q at level 50,
  format "ℓi ↦{ q } v"
) : bi_scope.
Notation "ℓi ↦ v" := (
  mapsto_na ℓi v 1
)(at level 20
) : bi_scope.
Notation "ℓi ↦at{ q }( v , V )" := (
  mapsto_at_view ℓi v V q
)(at level 20,
  q at level 50,
  format "ℓi ↦at{ q }( v ,  V )"
) : bi_scope.
Notation "ℓi ↦at( v , V )" := (
  mapsto_at_view ℓi v V 1
)(at level 20,
  format "ℓi ↦at( v ,  V )"
) : bi_scope.
Notation "ℓi ↦at{ q } v" := (
  mapsto_at_view ℓi v ∅ q
)(at level 20,
  q at level 50, format "ℓi ↦at{ q } v"
) : bi_scope.
Notation "ℓi ↦at v" := (
  mapsto_at_view ℓi v ∅ 1
)(at level 20
) : bi_scope.

Section store.
  Context `{!storeG Σ}.

  #[global] Instance hist_na_timeless ℓi h q :
    Timeless (hist_na ℓi h q).
  Proof.
    rewrite hist_na_eq. apply _.
  Qed.

  #[global] Instance hist_na_fractional ℓi h :
    Fractional (λ q, hist_na ℓi h q).
  Proof.
    rewrite hist_na_eq. iIntros (p q). iSplit.
    - iIntros "[$$] //".
    - iIntros "[Hp Hq]". by iCombine "Hp Hq" as "H".
  Qed.
  #[global] Instance hist_na_as_fractional ℓi h q :
    AsFractional (hist_na ℓi h q) (λ q, hist_na ℓi h q) q.
  Proof.
    split. done. apply _.
  Qed.

  Lemma hist_na_agree ℓi h1 h2 q1 q2 :
    hist_na ℓi h1 q1 -∗
    hist_na ℓi h2 q2 -∗
    ⌜h1 = h2⌝.
  Proof.
    rewrite hist_na_eq /hist_na_def. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hℓ%auth_frag_op_valid_1. iPureIntro.
    specialize (Hℓ ℓi). rewrite /= singleton_op lookup_singleton in Hℓ.
    by destruct Hℓ as [Hℓ%to_agree_op_inv_L _].
  Qed.

  Lemma store_interp_hist_na σ ℓi h q :
    store_interp σ -∗
    hist_na ℓi h q -∗
    ⌜σ !! ℓi = Some (store_elt_na h)⌝.
  Proof.
    iIntros "[Hσ _] Hℓ". rewrite hist_na_eq.
    iDestruct (own_valid_2 with "Hσ Hℓ")
      as %[[[xx q'] [Hσ [Hincl _]%Some_pair_included]]
             %singleton_included_l _]%auth_both_valid_discrete.
    iPureIntro ; clear dependent Σ q.
    rewrite lookup_store_to_cmra in Hσ.
    revert Hσ ; case: (σ !! ℓi) => [elt Hσ|Hσ] ; [|by inversion Hσ].
    apply Some_equiv_inj, pair_equiv_inj in Hσ as [Hσ _]. setoid_subst.
    apply Some_included in Hincl. destruct elt, Hincl as [Hincl|Hincl].
    - inversion Hincl.
    - apply csum_included in Hincl. naive_solver.
    - do 2 apply (inj (R:=equiv) _) in Hincl. by setoid_subst.
    - f_equal. f_equal. symmetry. apply leibniz_equiv, to_agree_included.
      apply csum_included in Hincl. naive_solver.
  Qed.

  #[global] Instance mapsto_na_timeless ℓi v q :
    Timeless (ℓi ↦{q} v).
  Proof.
    rewrite /mapsto_na /=. apply _.
  Qed.

  #[global] Instance mapsto_na_fractional ℓi v :
    Fractional (λ q, ℓi ↦{q} v)%I.
  Proof.
    rewrite /mapsto_na /=. iIntros (p q). iSplit.
    - iIntros "H". iDestruct "H" as (V h) "(#HV & [Hp Hq] & %)".
      iSplitL "Hp"; eauto.
    - iIntros "[Hp Hq]".
      iDestruct "Hp" as (Vp hp) "(#HVp & Hhp & %)".
      iDestruct "Hq" as (Vq hq) "(#HVq & Hhq & %)".
      iDestruct (hist_na_agree with "Hhp Hhq") as %->.
      rename hq into h. iExists Vp, h. iFrame "#∗". iSplit; last done.
      iApply hist_na_fractional. iModIntro. iFrame.
  Qed.
  #[global] Instance mapsto_na_as_fractional ℓi v q :
    AsFractional (ℓi ↦{q} v) (λ q, ℓi ↦{q} v)%I q.
  Proof.
    split. done. apply _.
  Qed.

  #[global] Instance mapsto_at_view_timeless ℓi v V q :
    Timeless (ℓi ↦at{q}(v, V)).
  Proof.
    rewrite mapsto_at_view_eq. apply _.
  Qed.

  #[global] Instance mapsto_at_view_mono ℓi v :
    Proper (flip (⊑) ==> eq ==> (⊢)) (mapsto_at_view ℓi v).
  Proof.
    rewrite mapsto_at_view_eq. solve_proper.
  Qed.
  #[global] Instance mapsto_at_view_mono_flip ℓi v :
    Proper ((⊑) ==> eq ==> flip (⊢)) (mapsto_at_view ℓi v).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance mapsto_at_view_fractional ℓi v V :
    Fractional (λ q, ℓi ↦at{q}(v, V))%I.
  Proof.
    intros p q. rewrite mapsto_at_view_eq. iSplit.
    - iIntros "H". iDestruct "H" as (Vℓ) "[% [Hp Hq]]".
      iSplitL "Hp"; iExists Vℓ; auto.
    - iIntros "[Hp Hq]".
      iDestruct "Hp" as (Vℓp) "[% Hp]". iDestruct "Hq" as (Vℓq) "[% Hq]".
      iCombine "Hp Hq" as "H". rewrite -Cinl_op.
      iDestruct (own_valid with "H") as %[[= ->]%to_agree_op_inv_L _]%auth_frag_valid%singleton_valid.
      rewrite agree_idemp. iExists _. auto.
  Qed.
  #[global] Instance mapsto_at_view_as_fractional ℓi v q V :
    AsFractional (ℓi ↦at{q}(v, V)) (λ q, ℓi ↦at{q}(v, V))%I q.
  Proof.
    split. done. apply _.
  Qed.

  Lemma mapsto_at_view_agree ℓi v1 v2 q1 q2 V1 V2 :
    ℓi ↦at{q1}(v1, V1) -∗
    ℓi ↦at{q2}(v2, V2) -∗
    ⌜v1 = v2⌝.
  Proof.
    iIntros "H1 H2". rewrite mapsto_at_view_eq /mapsto_at_view_def.
    iDestruct "H1" as (Vℓ1 ?) "H1". iDestruct "H2" as (Vℓ2 ?) "H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hℓi%auth_frag_op_valid_1. iPureIntro.
    specialize (Hℓi ℓi).
    rewrite /= singleton_op lookup_singleton -pair_op -Cinl_op in Hℓi.
    by destruct Hℓi as [[= -> _]%to_agree_op_inv_L _].
  Qed.

  Lemma store_interp_mapsto_at_view σ ℓi v V q :
    store_interp σ -∗
    ℓi ↦at{q}(v, V) -∗
    ⌜∃ Vℓ, V ⊑ Vℓ ∧ σ !! ℓi = Some (store_elt_at v Vℓ)⌝.
  Proof.
    iIntros "[Hσ _] Hℓ". rewrite mapsto_at_view_eq.
    iDestruct "Hℓ" as (Vℓ ?) "Hℓ".
    iDestruct (own_valid_2 with "Hσ Hℓ")
      as %[[[xx q'] [Hσ [Hincl _]%Some_pair_included]]%singleton_included_l _]
          %auth_both_valid_discrete.
    iPureIntro ; clear dependent Σ q. exists Vℓ. split=>//.
    rewrite lookup_store_to_cmra in Hσ.
    revert Hσ ; case: (σ !! ℓi) => [elt Hσ|Hσ] ; [|by inversion Hσ].
    apply Some_equiv_inj, pair_equiv_inj in Hσ as [Hσ _]. setoid_subst.
    apply Some_included in Hincl. destruct elt, Hincl as [Hincl|Hincl].
    - do 2 apply (inj (R:=equiv) _) in Hincl. by setoid_subst.
    - eassert ((v, Vℓ) = (_, _)) as [= -> ->] ; [|done].
      apply leibniz_equiv, to_agree_included.
      apply csum_included in Hincl. naive_solver.
    - inversion Hincl.
    - apply csum_included in Hincl. naive_solver.
  Qed.

  #[global] Instance has_length_timeless ℓ n :
    Timeless (has_length ℓ n).
  Proof.
    rewrite has_length_eq. apply _.
  Qed.

  #[global] Instance has_length_persistent ℓ n :
    Persistent (has_length ℓ n).
  Proof.
    rewrite has_length_eq. apply _.
  Qed.

  Lemma has_length_agree ℓ n1 n2 :
    has_length ℓ n1 -∗
    has_length ℓ n2 -∗
    ⌜n1 = n2⌝.
  Proof.
    rewrite has_length_eq /has_length_def. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hℓ%auth_frag_op_valid_1. iPureIntro.
    specialize (Hℓ ℓ). rewrite /= singleton_op lookup_singleton in Hℓ.
    by apply to_agree_op_inv_L, Some_valid.
  Qed.

  Lemma store_interp_has_length σ ℓ n :
    store_interp σ -∗
    has_length ℓ n -∗
    ⌜∃ blk, σ !! ℓ = Some blk ∧ Z.of_nat (length blk) = n⌝.
  Proof.
    iIntros "[_ Hσlen] Hℓ". rewrite has_length_eq /has_length_def.
    iDestruct (own_valid_2 with "Hσlen Hℓ")
      as % [ (agr_n & Hσ & Hagr)%singleton_included_l _ ]%auth_both_valid_discrete.
    iPureIntro ; clear dependent Σ.
    rewrite lookup_fmap in Hσ.
    revert Hσ ; case: (σ !! ℓ) => [blk Hσ|Hσ] ; [|by inversion Hσ].
    apply Some_equiv_inj in Hσ. setoid_subst.
    exists blk. split ; [done|].
    by apply Some_included in Hagr as [ ?%to_agree_inj | ?%to_agree_included ].
  Qed.
End store.

Section blockwise_definitions.
  Context `{!storeG Σ}.

  Definition hist_na_block_def (ℓ : location) (hs : list histO) q : iProp Σ :=
    has_length ℓ (length hs) ∗
    [∗ list] i ↦ h ∈ hs, hist_na (Locoff ℓ i) h q.
  Definition hist_na_block_aux : seal (@hist_na_block_def).
    Proof. by eexists. Qed.
  Definition hist_na_block :=
    unseal hist_na_block_aux.
  Definition hist_na_block_eq : @hist_na_block = @hist_na_block_def :=
    seal_eq hist_na_block_aux.

  Definition mapsto_na_block' ℓ (vs : list val) q : vProp Σ :=
    tc_opaque (
      ∃ V hs,
      monPred_in V ∗
      ⎡hist_na_block ℓ hs q⎤ ∗
      [∗ list] i ↦ v; h ∈ vs; hs,
      ⌜h !! (V !! (Locoff ℓ i)) = Some v ∧ ∀ t, h !! t = None ∨ t ⊑ V !! (Locoff ℓ i)⌝
    )%I.
  Definition mapsto_na_block (ℓ : location) (vs : list val) q : vProp Σ :=
    ⎡has_length ℓ (length vs)⎤ ∗
    [∗ list] i ↦ v ∈ vs, mapsto_na (Locoff ℓ i) v q.

  Definition mapsto_at_view_block_def ℓ vVs q : iProp Σ :=
    (has_length ℓ (length vVs) ∗
    [∗ list] i ↦ vV ∈ vVs,
      let '(v, V) := vV in
      mapsto_at_view (Locoff ℓ i) v V q)%I.
  Definition mapsto_at_view_block_aux : seal (@mapsto_at_view_block_def).
    Proof. by eexists. Qed.
  Definition mapsto_at_view_block :=
    unseal mapsto_at_view_block_aux.
  Definition mapsto_at_view_block_eq : @mapsto_at_view_block = @mapsto_at_view_block_def :=
    seal_eq mapsto_at_view_block_aux.
End blockwise_definitions.

Notation "ℓ *↦{ q } vs" := (
  mapsto_na_block ℓ vs q
)(at level 20,
  q at level 50,
  format "ℓ *↦{ q } vs"
) : bi_scope.
Notation "ℓ *↦ vs" := (
  mapsto_na_block ℓ vs 1
)(at level 20
) : bi_scope.
Notation "ℓ *↦at{ q }() vVs" := (
  mapsto_at_view_block ℓ vVs q
)(at level 20,
  q at level 50,
  format "ℓ *↦at{ q }() vVs"
) : bi_scope.
Notation "ℓ *↦at() vVs" := (
  mapsto_at_view_block ℓ vVs 1
)(at level 20,
  format "ℓ *↦at() vVs"
) : bi_scope.

Notation "ℓ *↦at{ q } vs" := (
  mapsto_at_view_block ℓ ((λ v, (v, ∅)) <$> vs) q
)(at level 20,
  q at level 50,
  format "ℓ *↦at{ q } vs"
) : bi_scope.
Notation "ℓ *↦at vs" := (
  mapsto_at_view_block ℓ ((λ v, (v, ∅)) <$> vs) 1
)(at level 20
) : bi_scope.

Section blockwise_store.
  Context `{!storeG Σ}.

  Lemma mapsto_na_block_equiv ℓ vs q :
    mapsto_na_block ℓ vs q ⊣⊢
    mapsto_na_block' ℓ vs q.
  Proof.
    iSplit.
    { rewrite /mapsto_na_block /mapsto_na /mapsto_na_block' /=. iIntros "[#Hlen H]".
      iAssert (∃ V hs, monPred_in V ∗
        [∗ list] i↦v;h ∈ vs;hs,
             ⎡ hist_na ℓ.[i] h q ⎤
             ∗ ⌜h !! (V !! ℓ.[i]) = Some v
             ∧ (∀ t : timestamp, h !! t = None ∨ t ⊑ V !! ℓ.[i])⌝)%I
        with "[H]" as (V hs) "[#HV H]" .
      { iClear "Hlen". iInduction vs as [|v vs] "IH" using rev_ind.
        - iExists ∅, []. rewrite big_sepL2_nil. iSplit; [|done].
          iDestruct (monPred_in_intro emp%I with "[//]") as (V) "[HV _]".
          by rewrite -(lat_bottom_sqsubseteq V).
        - rewrite big_sepL_app/=. iDestruct "H" as "[H [H0 _]]".
          iDestruct ("IH" with "H") as (V hs) "[#HV H]".
          iDestruct "H0" as (V0 h0) "[#HV0 H0]".
          set (t := V0 !! ℓ.[strings.length vs]).
          iExists (match t with
                   | None => delete (ℓ.[strings.length vs]) V
                   | Some t => (<[ℓ.[strings.length vs]:=t]>V)
                   end),
                  (hs ++ [h0]).
          iSplitR.
          { iCombine "HV HV0" as "HVV0". iApply (monPred_in_mono with "HVV0").
            intros ℓi. rewrite lookup_join /=.
            destruct (decide (ℓi = ℓ.[strings.length vs])) as [->|Hℓi].
            - fold t. destruct t; rewrite ?lookup_insert ?lookup_delete; solve_lat.
            - destruct t; rewrite ?lookup_insert_ne ?lookup_delete_ne //; solve_lat. }
          iApply (big_sepL2_app with "[H] [H0]"); simpl.
          + iApply (big_sepL2_mono with "H"). iIntros (? v' h' Hk _) "/= [$ ?]".
            assert (ℓ.[strings.length vs] ≠ ℓ.[k]).
            { intros [= <-%(inj Z.of_nat)]. by rewrite lookup_ge_None_2 in Hk. }
            destruct t; rewrite ?lookup_insert_ne ?lookup_delete_ne //.
          + iDestruct "H0" as "[$ ?]". rewrite Nat.add_0_r.
            fold t. destruct t; rewrite ?lookup_insert ?lookup_delete //. }
      iExists V, hs. iFrame "HV". rewrite big_sepL2_sep. iDestruct "H" as "[H $]".
      rewrite big_sepL2_alt hist_na_block_eq /hist_na_block_def embed_sep embed_big_sepL.
      iDestruct "H" as (Hlen) "H". rewrite Hlen. iFrame "Hlen".
      rewrite -[in ([∗ list] k↦x ∈ hs, _)%I](snd_zip vs hs); [|lia].
      by rewrite big_sepL_fmap. }
    { rewrite /mapsto_na_block /mapsto_na_block' hist_na_block_eq.
      iIntros "Hblk" ; iDestruct "Hblk" as (V hs) "(#HV & [#Hlen Hhistcells] & Hviewcells)".
      rewrite big_sepL2_alt ; iDestruct "Hviewcells" as (Heqlen) "Hviewcells".
      rewrite Heqlen embed_big_sepL. iFrame "Hlen".
      rewrite -[in ([∗ list] k↦x ∈ hs, _)%I](snd_zip vs hs); [|lia].
      rewrite -[in ([∗ list] i↦v ∈ vs, _)%I](fst_zip vs hs); [|lia].
      rewrite !big_sepL_fmap.
      iAssert ([∗ list] k↦y ∈ zip vs hs, monPred_in V)%I as "HV'".
      { iApply big_sepL_forall. by auto. }
      iCombine "Hhistcells Hviewcells" as "Hcells". rewrite -big_sepL_sep.
      iCombine "HV' Hcells" as "Hcells". rewrite -big_sepL_sep.
      rewrite /mapsto_na hist_na_eq/hist_na_def /=.
      iApply (big_sepL_mono with "Hcells"). simpl. eauto. }
  Qed.

  #[global] Instance hist_na_block_timeless ℓ hs q :
    Timeless (hist_na_block ℓ hs q).
  Proof.
    rewrite hist_na_block_eq. apply _.
  Qed.

  #[global] Instance hist_na_block_fractional ℓ hs :
    Fractional (λ q, hist_na_block ℓ hs q).
  Proof.
    rewrite hist_na_block_eq. apply _.
  Qed.
  #[global] Instance hist_na_block_as_fractional ℓ h q :
    AsFractional (hist_na_block ℓ h q) (λ q, hist_na_block ℓ h q) q.
  Proof.
    split. done. apply _.
  Qed.

  Lemma hist_na_block_agree ℓ hs1 hs2 q1 q2 :
    hist_na_block ℓ hs1 q1 -∗
    hist_na_block ℓ hs2 q2 -∗
    ⌜hs1 = hs2⌝.
  Proof.
    rewrite hist_na_block_eq/hist_na_block_def.
    iIntros "[Hlen1 Hh1] [Hlen2 Hh2]".
    iDestruct (has_length_agree with "Hlen1 Hlen2") as %Hlen.
    iDestruct (big_sepL2_split with "[$Hh1 $Hh2]") as "H12" ; first lia.
    iDestruct (big_sepL2_mono with "H12") as "H12".
    { intros. apply bi.wand_elim_l', bi.wand_entails, hist_na_agree. }
    iDestruct "H12" as %[??]. iPureIntro.
    eauto using list_eq_same_length.
  Qed.

  Lemma store_interp_hist_na_block σ ℓ hs q :
    store_interp σ -∗
    hist_na_block ℓ hs q -∗
    [∧ list] i↦h ∈ hs, ⌜σ !! ℓ.[i] = Some (store_elt_na h)⌝.
  Proof.
    rewrite hist_na_block_eq/hist_na_block_def big_andL_forall.
    iIntros "Hσ [_?]" (i h Hi). iApply (store_interp_hist_na with "Hσ").
    by iApply (big_sepL_lookup (λ i h, hist_na _ _ _) _ _ _ Hi).
  Qed.

  #[global] Instance mapsto_na_block_timeless ℓ vs q :
    Timeless (ℓ *↦{q} vs).
  Proof.
    apply _.
  Qed.

  #[global] Instance mapsto_na_block_fractional ℓ vs :
    Fractional (λ q, ℓ *↦{q} vs)%I.
  Proof.
    apply _.
  Qed.
  #[global] Instance mapsto_na_block_as_fractional ℓ vs q :
    AsFractional (ℓ *↦{q} vs) (λ q, ℓ *↦{q} vs)%I q.
  Proof.
    split. done. apply _.
  Qed.

  #[global] Instance mapsto_at_view_block_timeless ℓ vVs q :
    Timeless (ℓ *↦at{q}() vVs).
  Proof.
    rewrite mapsto_at_view_block_eq. apply bi.sep_timeless ; first by apply _.
    apply big_sepL_timeless. intros ? (?,?). apply _.
  Qed.

  #[global] Instance mapsto_at_view_block_mono ℓ :
    Proper (Forall2 (prod_relation eq (flip (⊑))) ==> eq ==> (⊢)) (mapsto_at_view_block ℓ).
  Proof.
    rewrite mapsto_at_view_block_eq/mapsto_at_view_block_def.
    intros vVs vVs' HvVs q ? <-.
    rewrite (Forall2_length _ _ _ HvVs).
    iIntros "[$ Hlist]".
    iInduction vVs as [|[v V] vVs] "IH" using rev_ind forall (vVs' HvVs).
    - inversion HvVs; subst; done.
    - apply Forall2_app_inv_l in HvVs as (vVs'1 & vVs'2 & HvVs'1 & HvVs'2 & ?); subst.
      pose proof (Forall2_length _ _ _ HvVs'2). destruct vVs'2 as [|[v' V'] []]; try done.
      rewrite 2!big_opL_app; simpl.
      rewrite -(Forall2_length _ _ _ HvVs'1).
      pose proof HvVs'2 as (? & ? & [] & _ & Heq)%Forall2_cons_inv_l. simplify_eq/=.
      iDestruct "Hlist" as "(Hlist & H & $)".
      iDestruct (mapsto_at_view_mono with "H") as "$"; [done.. |].
      by iApply "IH".
  Qed.
  #[global] Instance mapsto_at_view_block_mono_flip ℓ :
    Proper (Forall2 (prod_relation eq (⊑)) ==> eq ==> flip (⊢)) (mapsto_at_view_block ℓ).
  Proof.
    (* TODO: we should reuse the previous lemma instead of copy-pasting its
       proof; unfortunately we lack lemmas about flip and Proper instances about
       relation_equivalence. *)
    rewrite mapsto_at_view_block_eq/mapsto_at_view_block_def.
    intros vVs vVs' HvVs q ? <-.
    rewrite (Forall2_length _ _ _ HvVs).
    iIntros "[$ Hlist]".
    iInduction vVs as [|[v V] vVs] "IH" using rev_ind forall (vVs' HvVs).
    - inversion HvVs; subst ; done.
    - apply Forall2_app_inv_l in HvVs as (vVs'1 & vVs'2 & HvVs'1 & HvVs'2 & ?); subst.
      pose proof (Forall2_length _ _ _ HvVs'2). destruct vVs'2 as [|[v' V'] []]; try done.
      rewrite 2!big_opL_app; simpl.
      rewrite -(Forall2_length _ _ _ HvVs'1).
      pose proof HvVs'2 as (? & ? & [] & _ & Heq)%Forall2_cons_inv_l. simplify_eq/=.
      iDestruct "Hlist" as "(Hlist & H & $)".
      iDestruct (mapsto_at_view_mono with "H") as "$"; [done.. |].
      by iApply "IH".
  Qed.

  #[global] Instance mapsto_at_view_block_fractional ℓ vVs :
    Fractional (λ q, ℓ *↦at{q}() vVs)%I.
  Proof.
    rewrite mapsto_at_view_block_eq. apply fractional_sep ; first by apply _.
    apply fractional_big_sepL. intros ? (?,?). apply _.
  Qed.
  #[global] Instance mapsto_at_view_block_as_fractional ℓ vVs q :
    AsFractional (ℓ *↦at{q}() vVs) (λ q, ℓ *↦at{q}() vVs)%I q.
  Proof.
    split. done. apply _.
  Qed.

  Lemma mapsto_at_view_block_agree ℓ vVs1 vVs2 q1 q2 :
    ℓ *↦at{q1}() vVs1 -∗
    ℓ *↦at{q2}() vVs2 -∗
    ⌜fst <$> vVs1 = fst <$> vVs2⌝.
  Proof.
    rewrite mapsto_at_view_block_eq/mapsto_at_view_block_def.
    iIntros "[Hlen1 H1] [Hlen2 H2]".
    iDestruct (has_length_agree with "Hlen1 Hlen2") as %Hlen.
    iDestruct (big_sepL2_split with "[$H1 $H2]") as "H12"; first lia.
    iDestruct (big_sepL2_mono _ (λ _ vV1 vV2, ⌜fst vV1 = fst vV2⌝%I) with "H12") as "H12".
    { intros i [??] [??] ??. apply bi.wand_elim_l', bi.wand_entails, mapsto_at_view_agree. }
    iDestruct "H12" as %[??]. iPureIntro.
    eapply list_eq_same_length; try by rewrite fmap_length.
    intros i v1 v2 Hi H1 H2.
    rewrite ->list_lookup_fmap, fmap_Some in H1; destruct H1 as (vV1 & H1 & ->).
    rewrite ->list_lookup_fmap, fmap_Some in H2; destruct H2 as (vV2 & H2 & ->).
    by eauto.
  Qed.

  Lemma store_interp_mapsto_at_view_block σ ℓ vVs q :
    store_interp σ -∗
    ℓ *↦at{q}() vVs -∗
    [∧ list] i↦vV ∈ vVs, let '(v, V) := vV in
      ⌜∃ Vℓ, V ⊑ Vℓ ∧ σ !! ℓ.[i] = Some (store_elt_at v Vℓ)⌝.
  Proof.
    rewrite mapsto_at_view_block_eq/mapsto_at_view_block_def big_andL_forall.
    iIntros "Hσ [_?]" (i [v V] Hi). iApply (store_interp_mapsto_at_view with "Hσ").
    by iApply (big_sepL_lookup (λ i vV, let '(v, V) := vV in mapsto_at_view _ _ _ _) _ _ _ Hi).
  Qed.
End blockwise_store.
