From stdpp Require Export
  list.

From cosmo Require Import
  prelude.

Section basic.
  Context {A : Type}.

  Implicit Types x y z : A.
  Implicit Types l : list A.

  Lemma rev_elim l :
    l = [] ∨ ∃ l' x, l = l' ++ [x].
  Proof.
    revert l. refine (rev_ind _ _ _); [| intros x l _]; naive_solver.
  Qed.
End basic.

Section Z.
  Implicit Types i : Z.

  Open Scope Z.

  Section lookup_insert.
    Context {A : Type}.

    #[global] Instance list_lookup_Z : Lookup Z A (list A) :=
      λ i xs,
        if bool_decide (0 ≤ i) then
          xs !! Z.to_nat i
        else
          None.

    #[global] Instance list_insert_Z : Insert Z A (list A) :=
      λ i x' xs,
        if bool_decide (0 ≤ i) then
          <[ Z.to_nat i := x' ]> xs
        else
          xs.

    Lemma list_lookup_Z_to_nat (i : Z) :
      0 ≤ i →
      lookup (M := list A) i = lookup (Z.to_nat i).
    Proof.
      rewrite {1}/lookup/list_lookup_Z. by intros -> % (bool_decide_eq_true _).
    Qed.
    Lemma list_lookup_Z_Some_to_nat (xs : list A) (i : Z) (x : A) :
      xs !! i = Some x →
      xs !! Z.to_nat i = Some x.
    Proof. rewrite {1}/lookup/list_lookup_Z. by case_decide. Qed.

    Lemma list_lookup_Z_lt_Some (xs : list A) (i : Z) (x : A) :
      xs !! i = Some x →
      0 ≤ i < Z.of_nat (length xs).
    Proof.
      rewrite /lookup/list_lookup_Z. case_decide ; cbn ; last congruence.
      intros ?%lookup_lt_Some. lia.
    Qed.
    Lemma list_lookup_Z_lt_is_Some_1 (xs : list A) (i : Z) :
      is_Some (xs !! i) →
      0 ≤ i < Z.of_nat (length xs).
    Proof.
      intros [??]. by eapply list_lookup_Z_lt_Some.
    Qed.
    Lemma list_lookup_Z_lt_is_Some_2 (xs : list A) (i : Z) :
      0 ≤ i < Z.of_nat (length xs) →
      is_Some (xs !! i).
    Proof.
      intros ?. rewrite list_lookup_Z_to_nat ; first lia. apply lookup_lt_is_Some_2 ; lia.
    Qed.
    Lemma list_lookup_Z_lt_is_Some (xs : list A) (i : Z) :
      is_Some (xs !! i) ↔
      0 ≤ i < Z.of_nat (length xs).
    Proof.
      split ; by [ apply list_lookup_Z_lt_is_Some_1 | apply list_lookup_Z_lt_is_Some_2 ].
    Qed.

    Lemma list_insert_Z_to_nat (i : Z) :
      0 ≤ i →
      insert (M := list A) i = insert (Z.to_nat i).
    Proof.
      rewrite {1}/insert/list_insert_Z. by intros -> % (bool_decide_eq_true _).
    Qed.

    Lemma insert_Z_length (l : list A) (i : Z) (x : A) :
      length (<[i:=x]> l) = length l.
    Proof.
      destruct (decide (0 ≤ i)) ; last (destruct i =>// ; lia).
      rewrite list_insert_Z_to_nat//. apply insert_length.
    Qed.

    Lemma list_lookup_Z_insert_Z_ne (l : list A) (i j : Z) (x : A) :
      i ≠ j →
      <[i := x]> l !! j = l !! j.
    Proof.
      intros ?.
      destruct (decide (0 ≤ i)), (decide (0 ≤ j)) ; try (destruct i, j => // ; lia).
      rewrite list_lookup_Z_to_nat// list_insert_Z_to_nat// list_lookup_insert_ne//. lia.
    Qed.
    Lemma list_lookup_Z_insert_Z (l : list A) (i : Z) (x : A) :
      (0 ≤ i < Z.of_nat (length l))%Z →
      <[i:=x]> l !! i = Some x.
    Proof.
      intros ?.
      rewrite list_insert_Z_to_nat ; first lia.
      rewrite list_lookup_Z_to_nat ; first lia.
      apply list_lookup_insert. lia.
    Qed.

    Lemma list_insert_Z_id' (xs : list A) (i : Z) (x : A) :
      (0 ≤ i < Z.of_nat (length xs) → xs !! i = Some x) →
      <[i:=x]> xs = xs.
    Proof.
      destruct (decide (0 ≤ i)).
      - rewrite list_lookup_Z_to_nat ?list_insert_Z_to_nat ; [lia|lia|].
        intros ?. apply list_insert_id'. auto with lia.
      - rewrite /insert/list_insert_Z bool_decide_eq_false_2 //.
    Qed.
    Lemma list_insert_Z_id (xs : list A) (i : Z) (x : A) :
      xs !! i = Some x →
      <[i:=x]> xs = xs.
    Proof.
      auto using list_insert_Z_id'.
    Qed.

    #[global] Instance list_insert_Z_proper (R : relation A) (i : Z) :
      Proper (R ==> Forall2 R ==> Forall2 R) (insert i).
    Proof.
      intros. destruct (decide (0 ≤ i)).
      - rewrite list_insert_Z_to_nat ; solve_proper.
      - intros ??????. by do 2 (rewrite list_insert_Z_id' ; first lia).
    Qed.
  End lookup_insert.

  Lemma list_fmap_insert_Z {A B : Type} (f : A → B) (l : list A) (i : Z) (x : A) :
    f <$> <[i := x]> l = <[i := f x]> (f <$> l).
  Proof.
    destruct (decide (0 ≤ i)); last (destruct i => //; lia).
    rewrite !list_insert_Z_to_nat // list_fmap_insert //.
  Qed.
End Z.
