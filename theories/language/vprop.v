From iris.bi Require Export
  monpred.
From iris.bi Require Import
  big_op.
From iris.base_logic Require Export
  lib.own.
From iris.base_logic Require Import
  lib.fancy_updates.
From iris.proofmode Require Import
  tactics
  monpred.

From cosmo Require Import
  prelude.
From cosmo.language Require Export
  lang.

Lemma monPred_in_bot {I : biIndex} {PROP : bi} `{!BiIndexBottom bot} :
  bi_entails (PROP := monPredI I PROP) True (monPred_in bot).
Proof.
  iStartProof PROP. iIntros (i) "_". by iPureIntro.
Qed.

Canonical lat_bi_index (Lat : latticeT) :=
  {| bi_index_type := Lat |}.
#[global] Instance lat_bi_index_bot (Lat : latticeT) (bot : Lat) :
  LatBottom bot →
  BiIndexBottom bot.
Proof.
  done.
Qed.

Canonical view_bi_index :=
  {| bi_index_type := view |}.

Definition vProp Σ :=
  monPred view_bi_index (uPredI (iResUR Σ)).
Definition vPropO Σ :=
  monPredO view_bi_index (uPredI (iResUR Σ)).
Definition vPropI Σ :=
  monPredI view_bi_index (uPredI (iResUR Σ)).

Bind Scope bi_scope with vProp.
Bind Scope bi_scope with vPropO.
Bind Scope bi_scope with vPropI.

#[global] Hint Extern 10 (
  IsBiIndexRel _ _
) =>
  unfold IsBiIndexRel; solve_lat
: typeclass_instances.

#[global] Instance into_sep_monPred_in Σ V1 V2 :
  IntoSep (PROP := vPropI Σ) (monPred_in (V1 ⊔ V2)) (monPred_in V1) (monPred_in V2).
Proof.
  split => ?. rewrite monPred_at_sep. iPureIntro. split; solve_lat.
Qed.

#[global] Instance from_sep_monPred_in Σ V1 V2 :
  FromSep (PROP := vPropI Σ) (monPred_in (V1 ⊔ V2)) (monPred_in V1) (monPred_in V2).
Proof.
  split => ?. rewrite monPred_at_sep. iPureIntro. intros [??]; solve_lat.
Qed.

#[global] Instance combine_sep_as_monPred_in Σ V1 V2 :
  CombineSepAs (PROP := vPropI Σ) (monPred_in V1) (monPred_in V2) (monPred_in (V1 ⊔ V2)).
Proof.
  split => ?. rewrite monPred_at_sep. iPureIntro. intros [??]; solve_lat.
Qed.

#[global] Instance into_and_monPred_in Σ V1 V2 p :
  IntoAnd (PROP := vPropI Σ) p (monPred_in (V1 ⊔ V2)) (monPred_in V1) (monPred_in V2).
Proof.
  split => ?. destruct p; rewrite /= 2?monPred_at_intuitionistically monPred_at_and;
  iPureIntro; split; solve_lat.
Qed.

#[global] Instance from_and_monPred_in Σ V1 V2 :
  FromAnd (PROP := vPropI Σ) (monPred_in (V1 ⊔ V2)) (monPred_in V1) (monPred_in V2).
Proof.
  split => ?. rewrite monPred_at_and. iPureIntro. intros [??]; solve_lat.
Qed.
