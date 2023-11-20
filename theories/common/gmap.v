From stdpp Require Export
  gmap.

From cosmo Require Import
  prelude.

Section gmap_fmap_dom.
  Context `{Countable K, Countable K'} {A : Type}.

  Definition gmap_fmap_dom (f : K → K') : gmap K A → gmap K' A :=
    map_fold (insert ∘ f) ∅.

  Lemma lookup_gmap_fmap_dom (f : K → K') `{Inj K K' eq eq f} (m : gmap K A) (k : K) :
    gmap_fmap_dom f m !! (f k) = (m !! k).
  Proof.
    remember (f k) as k' eqn:EQ. revert k k' EQ.
    apply (map_fold_ind (λ b m, ∀ k k', k' = f k → b !! k' = m !! k)).
    { intros k. by rewrite !lookup_empty. }
    clear m. intros k0 a m m' _ ? k k' ->.
    destruct (decide (k0 = k)) as [<-|].
    - by rewrite !lookup_insert.
    - rewrite !lookup_insert_ne ; by auto.
  Qed.

  Lemma lookup_gmap_map_dom_ne (f : K → K') (m : gmap K A) (k' : K') :
    is_Some (gmap_fmap_dom f m !! k') →
    ∃ (k : K), f k = k'.
  Proof.
    unfold gmap_fmap_dom.
    apply (map_fold_ind (λ m' _, is_Some (m' !! k') → ∃ k : K, f k = k')).
    - rewrite lookup_empty. by intros [].
    - intros k y _ m' _ ? Hinsert.
      destruct (decide (f k = k')) ; first by eauto.
      rewrite lookup_insert_ne in Hinsert; first done.
      by auto.
  Qed.
End gmap_fmap_dom.
