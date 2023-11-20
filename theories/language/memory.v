From stdpp Require Export
  gmap.

From cosmo Require Import
  prelude.
From cosmo.common Require Export
  lattice.

Notation location :=
  positive.
Notation offset :=
  Z
( only parsing
).
Record locoff := Locoff {
  locoff_loc : location ;
  locoff_off : offset ;
}.

Definition locoff_to_pair '(Locoff ℓ i) :=
  (ℓ, i).
Definition pair_to_locoff '(ℓ, i) :=
  Locoff ℓ i.
#[global] Instance pair_to_locoff_inj :
  Inj eq eq pair_to_locoff.
Proof.
  by intros [] [] [= -> ->].
Qed.
#[global] Instance locoff_to_pair_inj :
  Inj eq eq locoff_to_pair.
Proof.
  by intros [] [] [= -> ->].
Qed.
#[global] Instance locoff_eq_dec : EqDecision locoff :=
  ltac:(eapply (inj_eq_dec locoff_to_pair)).
#[global] Instance locoff_countable :
  Countable locoff.
Proof.
  apply (inj_countable' locoff_to_pair pair_to_locoff). by intros [].
Qed.
Definition location_to_locoff ℓ :=
  Locoff ℓ 0.

Coercion location_to_locoff : location >-> locoff.
Notation "ℓ .[ i ]" := (
  Locoff ℓ i
)(at level 9,
  format "ℓ .[ i ]"
).

Notation timestamp := (
  option Qp
).

Notation view := (
  gmap locoff Qp
).

Definition view_Lat : latticeT :=
  gmap_Lat locoff Qp_Lat.

Section operational.
  Context {val expr : Type}.

  Definition history :=
    gmap timestamp val.

  Inductive store_elt :=
    | store_elt_at (v : val) (V : view)
    | store_elt_na (h : history).
  Definition store :=
    gmap location (list store_elt).

  #[global] Instance store_lookup : Lookup locoff store_elt store :=
    λ '(Locoff ℓ i) σ,
      if bool_decide (0 ≤ i)%Z then
        σ !! ℓ ≫= λ blk, blk !! Z.to_nat i
      else
        None.
  #[global] Instance store_insert : Insert locoff store_elt store :=
    λ '(Locoff ℓ i) s σ,
      if bool_decide (0 ≤ i)%Z then
        match σ !! ℓ with
        | None =>
            σ
        | Some blk =>
            <[ℓ := <[Z.to_nat i := s]> blk]> σ
        end
      else
        σ.

  Lemma store_lookup_eq (σ : store) (ℓ : location) (i : offset) :
    σ !! ℓ.[i] =
      if bool_decide (0 ≤ i)%Z then
        σ !! ℓ ≫= λ blk, blk !! Z.to_nat i
      else
        None.
  Proof.
    reflexivity.
  Qed.

  Lemma store_lookup_insert (σ : store) (ℓi : locoff) (s0 s : store_elt) :
    σ !! ℓi = Some s0 →
    <[ℓi := s]> σ !! ℓi = Some s.
  Proof.
    destruct ℓi as [ℓ i]. rewrite /lookup /insert /=.
    case_bool_decide ; last done.
    case_match ; last done. cbn=>?.
    rewrite lookup_insert /= list_lookup_insert//. by eapply lookup_lt_Some.
  Qed.

  Lemma store_lookup_insert_ne (σ : store) (ℓi ℓi' : locoff) (s : store_elt) :
    ℓi ≠ ℓi' →
    <[ℓi := s]> σ !! ℓi' = σ !! ℓi'.
  Proof.
    destruct ℓi as [ℓ i], ℓi' as [ℓ' i']. rewrite /lookup /insert /=.
    intros ?. case_bool_decide ; last done.
    case_bool_decide ; last done.
    destruct (σ !! ℓ) as [blk|] eqn:Hσℓ ; last done.
    destruct (decide (ℓ = ℓ')) as [<-|].
    - destruct (decide (i = i')) as [<-|] ; first done.
      assert (Z.to_nat i ≠ Z.to_nat i') by lia.
      by rewrite Hσℓ lookup_insert /= list_lookup_insert_ne.
    - by rewrite lookup_insert_ne.
  Qed.

  Inductive atomicity :=
    | Atomic
    | NonAtomic.

  #[global] Instance atomicity_eq_dec : EqDecision atomicity :=
    ltac:(solve_decision).
  #[global] Instance atomicity_countable :
    Countable atomicity.
  Proof.
    refine (inj_countable' (λ a, bool_decide (a = Atomic))
                           (λ b, if b then Atomic else NonAtomic) _).
    by intros [].
  Qed.

  Implicit Types v : val.
  Implicit Types e : expr.
  Implicit Types ℓ : location.
  Implicit Types ℓi : locoff.
  Implicit Types n : Z.
  Implicit Types t : timestamp.
  Implicit Types V Vℓ : view.
  Implicit Types h : history.
  Implicit Types blk : list store_elt.
  Implicit Types σ : store.
  Implicit Types α : atomicity.

  Inductive mem_event : Type :=
    | mem_event_read α ℓi v
    | mem_event_write_na ℓi v
    | mem_event_update ℓi v0 v1
    | mem_event_length ℓ n
    | mem_event_alloc α ℓ n v.

  Inductive mem_step : store → view → mem_event → store → view → Prop :=
    | mem_step_read_na σ V ℓi h t t' v :
        σ !! ℓi = Some (store_elt_na h) →
        V !! ℓi = t →
        (t ⊑ t') →
        h !! t' = Some v →
        mem_step
          σ V
          (mem_event_read NonAtomic ℓi v)
          σ V
    | mem_step_write_na σ V ℓi h t (t' : Qp) v :
        σ !! ℓi = Some (store_elt_na h) →
        V !! ℓi = t →
        (t ⊑ Some t') →
        h !! Some t' = None →
        mem_step
          σ V
          (mem_event_write_na ℓi v)
          (<[ℓi := store_elt_na $ <[Some t' := v]> h]> σ)
          (<[ℓi := t']> V)
    | mem_step_read_at σ V ℓi Vℓ v :
        σ !! ℓi = Some (store_elt_at v Vℓ) →
        mem_step
          σ V
          (mem_event_read Atomic ℓi v)
          σ (Vℓ ⊔ V)
    | mem_step_update σ V ℓi Vℓ v0 v1 :
        σ !! ℓi = Some (store_elt_at v0 Vℓ) →
        mem_step
          σ V
          (mem_event_update ℓi v0 v1)
          (<[ℓi := store_elt_at v1 (Vℓ ⊔ V)]> σ) (Vℓ ⊔ V)
    | mem_step_length σ V ℓ blk n :
        σ !! ℓ = Some blk →
        Z.of_nat (length blk) = n →
        mem_step
          σ V
          (mem_event_length ℓ n)
          σ V
    | mem_step_alloc_na σ V ℓ n v :
        σ !! ℓ = None →
        (0 ≤ n)%Z →
        mem_step
          σ V
          (mem_event_alloc NonAtomic ℓ n v)
          (<[ℓ := replicate (Z.to_nat n) $ store_elt_na {[ None := v ]} ]> σ) V
    | mem_step_alloc_at σ V ℓ n v :
        σ !! ℓ = None →
        (0 ≤ n)%Z →
        mem_step
          σ V
          (mem_event_alloc Atomic ℓ n v)
          (<[ℓ := replicate (Z.to_nat n) $ store_elt_at v V]> σ) V.
End operational.
