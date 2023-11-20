From stdpp Require Import
  gmap.

From cosmo Require Import
  prelude.

Structure latticeT : Type := Make_Lat {
  lat_ty :> Type;

  #[global] lat_equiv ::
    Equiv lat_ty;
  #[global] lat_sqsubseteq ::
    SqSubsetEq lat_ty;
  #[global, canonical=no] lat_join ::
    Join lat_ty;
  #[global, canonical=no] lat_meet ::
    Meet lat_ty;

  #[global] lat_inhabited ::
    Inhabited lat_ty;
  #[global] lat_sqsubseteq_proper ::
    Proper ((≡) ==> (≡) ==> iff) (⊑@{lat_ty});
  #[global] lat_join_proper ::
    Proper ((≡) ==> (≡) ==> (≡)) (⊔@{lat_ty});
  #[global] lat_meet_proper ::
    Proper ((≡) ==> (≡) ==> (≡)) (⊓@{lat_ty});
  #[global] lat_equiv_equivalence ::
    Equivalence (≡@{lat_ty});
  #[global] lat_pre_order ::
    PreOrder (⊑@{lat_ty});
  #[global] lat_sqsubseteq_antisym ::
    AntiSymm (≡@{lat_ty}) (⊑);

  lat_join_sqsubseteq_l (X Y : lat_ty) :
    X ⊑ X ⊔ Y;
  lat_join_sqsubseteq_r (X Y : lat_ty) :
    Y ⊑ X ⊔ Y;
  lat_join_lub (X Y Z : lat_ty) :
    X ⊑ Z →
    Y ⊑ Z →
    X ⊔ Y ⊑ Z;
  lat_meet_sqsubseteq_l (X Y : lat_ty) :
    X ⊓ Y ⊑ X;
  lat_meet_sqsubseteq_r (X Y : lat_ty) :
    X ⊓ Y ⊑ Y;
  lat_meet_glb (X Y Z : lat_ty) :
    X ⊑ Y →
    X ⊑ Z →
    X ⊑ Y ⊓ Z
}.
#[global] Arguments lat_equiv : simpl never.
#[global] Arguments lat_sqsubseteq : simpl never.
#[global] Arguments lat_join : simpl never.
#[global] Arguments lat_join_sqsubseteq_l {_} _ _.
#[global] Arguments lat_join_sqsubseteq_r {_} _ _.
#[global] Arguments lat_join_lub {_} _ _ _.
#[global] Arguments lat_meet : simpl never.
#[global] Arguments lat_meet_sqsubseteq_l {_} _ _.
#[global] Arguments lat_meet_sqsubseteq_r {_} _ _.
#[global] Arguments lat_meet_glb {_} _ _ _.

Lemma lat_join_sqsubseteq_l' (Lat : latticeT) (X Y Z : Lat) :
  Z ⊑ X →
  Z ⊑ X ⊔ Y.
Proof.
  intros ->; apply lat_join_sqsubseteq_l.
Qed.

Lemma lat_join_sqsubseteq_r' (Lat : latticeT) (X Y Z : Lat) :
  Z ⊑ Y →
  Z ⊑ X ⊔ Y.
Proof.
  intros ->; apply lat_join_sqsubseteq_r.
Qed.

Lemma lat_meet_sqsubseteq_l' (Lat : latticeT) (X Y Z : Lat) :
  X ⊑ Z →
  X ⊓ Y ⊑ Z.
Proof.
  intros <-; apply lat_meet_sqsubseteq_l.
Qed.

Lemma lat_meet_sqsubseteq_r' (Lat : latticeT) (X Y Z : Lat) :
  Y ⊑ Z →
  X ⊓ Y ⊑ Z.
Proof.
  intros <-; apply lat_meet_sqsubseteq_r.
Qed.

Create HintDb lat.
Ltac solve_lat :=
  by typeclasses eauto with lat typeclass_instances.
#[global] Hint Resolve lat_join_lub lat_meet_glb : lat.
#[global] Hint Extern 0 (?a ⊑ ?b) =>
  (* We first check whether a and b are unifiable, in order not to
     trigger typeclass search for Reflexivity when this is not needed. *)
  unify a b with lat; reflexivity : lat.
#[global] Hint Extern 0 (_ = _) => apply (anti_symm (⊑)) : lat.
#[global] Hint Extern 0 (_ ≡ _) => apply (anti_symm (⊑)) : lat.
(* Hint Resolve lat_join_sqsubseteq_or | 10 : lat. *)
#[global] Hint Resolve lat_join_sqsubseteq_l' | 10 : lat.
#[global] Hint Resolve lat_join_sqsubseteq_r' | 10 : lat.
#[global] Hint Resolve lat_meet_sqsubseteq_l' | 10 : lat.
#[global] Hint Resolve lat_meet_sqsubseteq_r' | 10 : lat.
#[global] Hint Extern 100 (?a ⊑ ?c) =>
  match goal with H : a ⊑ ?b |- _ => transitivity b; [exact H|] end
  : lat.
#[global] Hint Extern 200 (?a ⊑ ?c) =>
  match goal with H : ?b ⊑ c |- _ => transitivity b; [|exact H] end
  : lat.

Section Lat.
  Context {Lat : latticeT}.

  #[global] Instance lat_sqsubseteq_order_L `{!LeibnizEquiv Lat} :
    PartialOrder (A:=Lat) (⊑).
  Proof.
    split; [apply lat_pre_order|] => x y ??.
    by apply leibniz_equiv, (anti_symm (⊑)).
  Qed.

  #[global] Instance lat_join_assoc :
    @Assoc Lat (≡) (⊔).
  Proof.
    intros ???. solve_lat.
  Qed.
  #[global] Instance lat_join_assoc_L `{!LeibnizEquiv Lat} :
    @Assoc Lat (=) (⊔).
  Proof.
    intros ???. solve_lat.
  Qed.

  #[global] Instance lat_join_comm :
    @Comm Lat Lat (≡) (⊔).
  Proof.
    intros ??; solve_lat.
  Qed.
  #[global] Instance lat_join_comm_L `{!LeibnizEquiv Lat} :
    @Comm Lat Lat (=) (⊔).
  Proof.
    intros ??; solve_lat.
  Qed.

  #[global] Instance lat_join_mono :
    Proper ((⊑) ==> (⊑) ==> (⊑)) (@join Lat _).
  Proof.
    intros ?????. solve_lat.
  Qed.
  #[global] Instance lat_join_mono_flip :
    Proper (flip (⊑) ==> flip (⊑) ==> flip (⊑)) (@join Lat _).
  Proof.
    solve_proper.
  Qed.

  Lemma lat_le_join_l (x y : Lat) :
    y ⊑ x →
    x ⊔ y ≡ x.
  Proof.
    solve_lat.
  Qed.
  Lemma lat_le_join_l_L `{!LeibnizEquiv Lat} (x y : Lat) :
    y ⊑ x →
    x ⊔ y = x.
  Proof.
    solve_lat.
  Qed.

  Lemma lat_le_join_r (x y : Lat) :
    x ⊑ y →
    x ⊔ y ≡ y.
  Proof.
    solve_lat.
  Qed.
  Lemma lat_le_join_r_L `{!LeibnizEquiv Lat} (x y : Lat) :
    x ⊑ y →
    x ⊔ y = y.
  Proof.
    solve_lat.
  Qed.

  Lemma lat_join_idem (x : Lat) :
    x ⊔ x ≡ x.
  Proof.
    solve_lat.
  Qed.
  Lemma lat_join_idem_L `{!LeibnizEquiv Lat} (x : Lat) :
    x ⊔ x = x.
  Proof.
    solve_lat.
  Qed.

  #[global] Instance lat_meet_assoc :
    @Assoc Lat (≡) (⊓).
  Proof.
    intros ???; solve_lat.
  Qed.
  #[global] Instance lat_meet_assoc_L `{!LeibnizEquiv Lat} :
    @Assoc Lat (=) (⊓).
  Proof.
    intros ???. solve_lat.
  Qed.

  #[global] Instance lat_meet_comm :
    @Comm Lat Lat (≡) (⊓).
  Proof.
    intros ??; solve_lat.
  Qed.
  #[global] Instance lat_meet_comm_L `{!LeibnizEquiv Lat} :
    @Comm Lat Lat (=) (⊓).
  Proof.
    intros ??; solve_lat.
  Qed.

  #[global] Instance lat_meet_mono :
    Proper ((⊑) ==> (⊑) ==> (⊑)) (@meet Lat _).
  Proof.
    intros ?????. solve_lat.
  Qed.
  #[global] Instance lat_meet_mono_flip :
    Proper (flip (⊑) ==> flip (⊑) ==> flip (⊑)) (@meet Lat _).
  Proof.
    solve_proper.
  Qed.

  Lemma lat_le_meet_l (x y : Lat) :
    x ⊑ y →
    x ⊓ y ≡ x.
  Proof.
    solve_lat.
  Qed.
  Lemma lat_le_meet_l_L `{!LeibnizEquiv Lat} (x y : Lat) :
    x ⊑ y →
    x ⊓ y = x.
  Proof.
    solve_lat.
  Qed.

  Lemma lat_le_meet_r (x y : Lat) :
    y ⊑ x →
    x ⊓ y ≡ y.
  Proof.
    solve_lat.
  Qed.
  Lemma lat_le_meet_r_L `{!LeibnizEquiv Lat} (x y : Lat) :
    y ⊑ x →
    x ⊓ y = y.
  Proof.
    solve_lat.
  Qed.

  Lemma lat_meet_idem (x : Lat) :
    x ⊓ x ≡ x.
  Proof.
    solve_lat.
  Qed.
  Lemma lat_meet_idem_L `{!LeibnizEquiv Lat} (x : Lat) :
    x ⊓ x = x.
  Proof.
    solve_lat.
  Qed.

  (* Lattices with a bottom element. *)
  Class LatBottom (bot : Lat) :=
    lat_bottom_sqsubseteq X : bot ⊑ X.
  Hint Resolve lat_bottom_sqsubseteq : lat.

  #[global] Instance lat_join_bottom_rightid `{!LatBottom bot} :
    RightId (≡) bot (⊔).
  Proof.
    intros ?; solve_lat.
  Qed.
  #[global] Instance lat_join_bottom_rightid_L `{!LeibnizEquiv Lat} `{!LatBottom bot} :
    RightId (=) bot (⊔).
  Proof.
    intros ?; solve_lat.
  Qed.

  #[global] Instance lat_join_bottom_leftid `{!LatBottom bot} :
    LeftId (≡) bot (⊔).
  Proof.
    intros ?; solve_lat.
  Qed.
  #[global] Instance lat_join_bottom_leftid_L `{!LeibnizEquiv Lat} `{!LatBottom bot} :
    LeftId (=) bot (⊔).
  Proof.
    intros ?; solve_lat.
  Qed.

  #[global] Instance lat_meet_bottom_leftabsorb `{!LatBottom bot} (x : Lat) :
    LeftAbsorb (≡) bot (⊓).
  Proof.
    intros ?; solve_lat.
  Qed.
  #[global] Instance lat_meet_bottom_leftabsorb_L `{!LeibnizEquiv Lat} `{!LatBottom bot} :
    LeftAbsorb (=) bot (⊓).
  Proof.
    intros ?. solve_lat.
  Qed.

  #[global] Instance lat_meet_bottom_rightabsorb `{!LatBottom bot} (x : Lat) :
    RightAbsorb (≡) bot (⊓).
  Proof.
    intros ?; solve_lat.
  Qed.
  #[global] Instance lat_meet_bottom_rightabsorb_L `{!LeibnizEquiv Lat} `{!LatBottom bot} :
    RightAbsorb (=) bot (⊓).
  Proof.
    intros ?. solve_lat.
  Qed.
End Lat.
#[global] Hint Resolve lat_bottom_sqsubseteq : lat.

Section prod.
  Context (A B : latticeT).

  Program Canonical prod_Lat :=
    Make_Lat (A * B) prod_equiv (prod_relation (⊑) (⊑))
             (λ p1 p2, (p1.1 ⊔ p2.1, p1.2 ⊔ p2.2))
             (λ p1 p2, (p1.1 ⊓ p2.1, p1.2 ⊓ p2.2))
             _ _ _ _ _ _ _ _ _ _ _ _ _.
  Next Obligation.
    intros ??[a b]??[c d]. split=>-[??]; split;
    rewrite -?a -?b // -?c -?d // ?a ?c // ?b ?d //.
  Qed.
  Next Obligation.
    intros ??[a b]??[c d]. split; rewrite /= ?a ?c // ?b ?d //.
  Qed.
  Next Obligation.
    intros ??[a b]??[c d]. split; rewrite /= ?a ?c // ?b ?d //.
  Qed.
  Next Obligation.
    split; [apply: prod_relation_refl | apply: prod_relation_trans].
  Qed.
  Next Obligation.
    intros ??[??][??]; split; by apply (anti_symm (⊑)).
  Qed.
  Next Obligation.
    intros ??. split; solve_lat.
  Qed.
  Next Obligation.
    intros ??. split; solve_lat.
  Qed.
  Next Obligation.
    intros ??? [??] [??]. by split; solve_lat.
  Qed.
  Next Obligation.
    intros ??. split; solve_lat.
  Qed.
  Next Obligation.
    intros ??. split; solve_lat.
  Qed.
  Next Obligation.
    intros ??? [??] [??]. by split; solve_lat.
  Qed.

  #[global] Instance prod_sqsubseteq_dec :
    RelDecision (A:=A) (⊑) →
    RelDecision (A:=B) (⊑) →
    RelDecision (A:=A * B) (⊑).
  Proof.
    move => ?? ab ab'.
    case: (decide (fst ab ⊑ fst ab'));
    case: (decide (snd ab ⊑ snd ab'));
      [left => //|right|right|right]; move => []; abstract naive_solver.
  Qed.

  #[global] Instance prod_latbottom `{!@LatBottom A botA, !@LatBottom B botB} :
    LatBottom (botA, botB).
  Proof.
    split; solve_lat.
  Qed.

  #[global] Instance fst_lat_mono :
    Proper ((⊑) ==> (⊑)) (@fst A B).
  Proof.
    move => [??][??][-> _]//.
  Qed.

  #[global] Instance snd_lat_mono :
    Proper ((⊑) ==> (⊑)) (@snd A B).
  Proof.
    move => [??][??][_ ->]//.
  Qed.

  Lemma lat_join_fst x y :
    fst (x ⊔ y) = fst x ⊔ fst y.
  Proof.
    done.
  Qed.

  Lemma lat_join_snd x y :
    snd (x ⊔ y) = snd x ⊔ snd y.
  Proof.
    done.
  Qed.
End prod.

#[global] Instance option_sqsubseteq `{SqSubsetEq A} : SqSubsetEq (option A) :=
  λ o1 o2, if o1 is Some x1 return _ then
              if o2 is Some x2 return _ then x1 ⊑ x2 else False
           else True.

#[global] Instance option_sqsubseteq_preorder `{SqSubsetEq A} `{!@PreOrder A (⊑)} :
  @PreOrder (option A) (⊑).
Proof.
  split.
  - move=>[x|] //. apply (@reflexivity A (⊑) _).
  - move=>[x|] [y|] [z|] //. apply (@transitivity A (⊑) _).
Qed.

#[global] Instance option_sqsubseteq_po `{SqSubsetEq A} `{!@PartialOrder A (⊑)} :
  @PartialOrder (option A) (⊑).
Proof.
  split; [apply _|].
  move => [?|] [?|] ??; [|done|done|done]. f_equal. apply: anti_symm; try done. apply _.
Qed.

Section option.
  Context (Lat : latticeT).

  Program Canonical option_Lat :=
    Make_Lat (option Lat) option_equiv option_sqsubseteq
             (λ o1 o2, if o1 is Some x1 return _ then
                         if o2 is Some x2 return _ then Some (x1 ⊔ x2) else o1
                       else o2)
             (λ o1 o2, if o1 is Some x1 return _ then
                         if o2 is Some x2 return _ then Some (x1 ⊓ x2) else None
                       else None) _ _ _ _ _ _ _ _ _ _ _ _ _.
  Next Obligation.
    intros ??[???|]??[???|]; try by split. by apply lat_sqsubseteq_proper.
  Qed.
  Next Obligation.
    intros ??[?? EQ1|]??[?? EQ2|]=>//; constructor; by setoid_subst.
  Qed.
  Next Obligation.
    intros ??[?? EQ1|]??[?? EQ2|]=>//; constructor; by setoid_subst.
  Qed.
  Next Obligation.
    move=>[x|] [y|] //. constructor. solve_lat.
  Qed.
  Next Obligation.
    move=>[x|] [y|] //. solve_lat.
  Qed.
  Next Obligation.
    move=>[x|] [y|] //. solve_lat.
  Qed.
  Next Obligation.
    move=>[x|] [y|] [z|] //. solve_lat.
  Qed.
  Next Obligation.
    move=>[x|] [y|] //. solve_lat.
  Qed.
  Next Obligation.
    move=>[x|] [y|] //. solve_lat.
  Qed.
  Next Obligation.
    move=>[x|] [y|] [z|] //. solve_lat.
  Qed.

  #[global] Instance option_sqsubseteq_dec :
    RelDecision (A:=Lat) (⊑) →
    RelDecision (A:=option Lat) (⊑).
  Proof.
    move=>DEC [a|][a'|]; unfold Decision; [edestruct (DEC a a')|..]; auto with lat.
  Qed.

  #[global] Instance option_latbottom :
    LatBottom (@None Lat).
  Proof.
    done.
  Qed.

  #[global] Instance option_Total `{!@Total Lat (⊑)}:
    @Total (option Lat) (⊑).
  Proof.
    move => [x|] [y|]; (try by right); (try by left). destruct (total (⊑) x y); auto.
  Qed.

  #[global] Instance Some_mono :
    Proper ((⊑) ==> (⊑)) (@Some Lat).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance Some_mono_flip :
    Proper (flip (⊑) ==> flip (⊑)) (@Some Lat).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance fmap_sqsubseteq_mono f :
    Proper ((⊑) ==> (⊑)) f ->
    Proper ((⊑) ==> (⊑)) (@fmap option option_fmap Lat (option Lat) f).
  Proof.
    move => H.
    repeat move => ? ? S. rewrite /fmap /option_fmap /option_map.
    repeat case_match; simplify_option_eq; cbn; [by apply H|destruct S|done|done].
  Qed.
End option.

Section Forall2.
  Context {A} (R : relation A).

  #[global] Instance option_Forall2_refl :
    Reflexive R →
    Reflexive (option_Forall2 R).
  Proof.
    intros ? [?|]; by constructor.
  Qed.
  #[global] Instance option_Forall2_sym :
    Symmetric R →
    Symmetric (option_Forall2 R).
  Proof.
    destruct 2; by constructor.
  Qed.
  #[global] Instance option_Forall2_trans :
    Transitive R →
    Transitive (option_Forall2 R).
  Proof.
    destruct 2; inversion_clear 1; constructor; etrans; eauto.
  Qed.
  #[global] Instance option_Forall2_equiv :
    Equivalence R →
    Equivalence (option_Forall2 R).
  Proof.
    destruct 1; split; apply _.
  Qed.
End Forall2.

Section gmap.
  Context K `{Countable K}.

  #[global] Instance gmap_sqsubseteq `{SqSubsetEq A} : SqSubsetEq (gmap K A) :=
    λ m1 m2, ∀ i : K, sqsubseteq (A:=option A) (m1 !! i) (m2 !! i).

  #[global] Instance gmap_sqsubseteq_preorder `{SqSubsetEq A} `{!@PreOrder A (⊑)} :
    @PreOrder (gmap K A) (⊑).
  Proof.
    split=>??//? LE1 LE2 ?; etrans; [apply LE1|apply LE2].
  Qed.

  #[global] Instance gmap_sqsubseteq_po `{SqSubsetEq A} `{!@PartialOrder A (⊑)} :
    @PartialOrder (gmap K A) (⊑).
  Proof.
    constructor; [apply _|].
    move => ????. apply map_eq => ?. by apply : (anti_symm (⊑)).
  Qed.

  #[global] Instance gmap_key_filter {A} : Filter K (gmap K A) :=
    λ P _, filter (λ kv, P (kv.1)).

  Context (A : latticeT).

  Program Canonical gmap_Lat :=
    Make_Lat (gmap K A) map_equiv gmap_sqsubseteq
             (union_with (λ x1 x2, Some (x1 ⊔ x2)))
             (intersection_with (λ x1 x2, Some (x1 ⊓ x2)))
             _ _ _ _ _ _ _ _ _ _ _ _ _.
  Next Obligation.
    move=> ??? ???; split=>??; setoid_subst=>//.
  Qed.
  Next Obligation.
    move=> X1 Y1 EQ1 X2 Y2 EQ2 i. rewrite !lookup_union_with.
    by destruct (EQ1 i), (EQ2 i); setoid_subst.
  Qed.
  Next Obligation.
    move=> X1 Y1 EQ1 X2 Y2 EQ2 i. rewrite !lookup_intersection_with.
    by destruct (EQ1 i), (EQ2 i); setoid_subst.
  Qed.
  Next Obligation.
    move=>?? LE1 LE2 ?. apply (anti_symm (⊑)); [apply LE1|apply LE2].
  Qed.
  Next Obligation.
    move=>???. rewrite lookup_union_with.
    repeat destruct lookup=>//. solve_lat.
  Qed.
  Next Obligation.
    move=>???. rewrite lookup_union_with.
    repeat destruct lookup=>//. solve_lat.
  Qed.
  Next Obligation.
    move=>??? LE1 LE2 i. rewrite lookup_union_with.
    specialize (LE1 i). specialize (LE2 i).
    repeat destruct lookup=>//. solve_lat.
  Qed.
  Next Obligation.
    move=>???. rewrite lookup_intersection_with.
    repeat destruct lookup=>//. solve_lat.
  Qed.
  Next Obligation.
    move=>???. rewrite lookup_intersection_with.
    repeat destruct lookup=>//. solve_lat.
  Qed.
  Next Obligation.
    move=>??? LE1 LE2 i. rewrite lookup_intersection_with.
    specialize (LE1 i). specialize (LE2 i).
    repeat destruct lookup=>//. solve_lat.
  Qed.

  #[global] Instance gmap_bottom :
    LatBottom (@empty (gmap K A) _).
  Proof.
    done.
  Qed.

  #[global] Instance gmap_sqsubseteq_dec :
    RelDecision (A:=A) (⊑) →
    RelDecision (A:=gmap K A) (⊑).
  Proof.
    move => ? m m'.
    destruct (decide (set_Forall (λ k, m !! k ⊑ m' !! k) (dom m))) as [Y|N].
    - left => k.
      case: (decide (k ∈ dom m)).
      + by move/Y.
      + move/not_elem_of_dom => -> //.
    - right.
      apply not_set_Forall_Exists in N; last apply _.
      case: N => x [/elem_of_dom [a ?]] NSqsubseteq ?. by apply NSqsubseteq.
  Qed.

  #[global] Instance lookup_mono l :
    Proper ((⊑) ==> (⊑)) (@lookup K A (gmap K A) _ l).
  Proof.
    intros ?? Le. apply Le.
  Qed.
  #[global] Instance lookup_mono_flip l :
    Proper (flip (⊑) ==> flip (⊑)) (@lookup K A (gmap K A) _ l).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance gmap_sqsubseteq_dom_proper :
    Proper ((@sqsubseteq (gmap K A) _) ==> (⊆)) dom.
  Proof.
    move => m1 m2 Sqsubseteq k /elem_of_dom [a Eqa].
    specialize (Sqsubseteq k). rewrite Eqa in Sqsubseteq.
    destruct (m2 !! k) as [|] eqn:Eq2; last done.
    apply elem_of_dom. by eexists.
  Qed.

  Lemma gmap_join_dom_union (m1 m2 : gmap K A):
    dom (m1 ⊔ m2) ≡ dom m1 ∪ dom m2.
  Proof.
    move => k. rewrite elem_of_union 3!elem_of_dom lookup_union_with /=.
    case (m1 !! k) => [v1|]; case (m2 !! k) => [v2|] /=; naive_solver.
  Qed.

  Lemma gmap_meet_dom_intersection (m1 m2 : gmap K A):
    dom (m1 ⊓ m2) ≡ dom m1 ∩ dom m2.
  Proof.
    move => k. rewrite elem_of_intersection 3!elem_of_dom lookup_intersection_with /=.
    case (m1 !! k) => [v1|]; case (m2 !! k) => [v2|] /=; naive_solver.
  Qed.

  Lemma lookup_join (m1 m2 : gmap K A) k:
    (m1 ⊔ m2) !! k = m1 !! k ⊔ m2 !! k.
  Proof.
    rewrite lookup_union_with. by do 2!case: (_ !! k).
  Qed.

  Lemma lookup_meet (m1 m2 : gmap K A) k:
    (m1 ⊓ m2) !! k = m1 !! k ⊓ m2 !! k.
  Proof.
    rewrite lookup_intersection_with. by do 2!case: (_ !! k).
  Qed.

  #[global] Instance gmap_leibniz_eq :
    LeibnizEquiv A → LeibnizEquiv (gmap K A).
  Proof.
    intros. apply map_leibniz.
  Qed.
End gmap.

Lemma gmap_subseteq_empty `{Countable K} {A} (m : gmap K A) :
  ∅ ⊆ m.
Proof.
  intros ?. rewrite lookup_empty. by case lookup.
Qed.

Program Canonical Z_Lat :=
  Make_Lat (Z) (=) (≤)%Z  Z.max Z.min
           _ _ _ _ _ _ _ _ _ _ _ _ _.
Solve Obligations with (unfold sqsubseteq, join, meet ; lia).

#[global] Instance Z_leibnizequiv : LeibnizEquiv Z :=
  λ _ _ H, H.

Program Canonical pos_Lat :=
  Make_Lat (positive) (=) (≤)%positive
           (λ (p q : positive), if (decide (p ≤ q)%positive) then q else p)
           (λ (p q : positive), if (decide (p ≤ q)%positive) then p else q)
           _ _ _ _ _ _ _ _ _ _ _ _ _.
Next Obligation.
  move=>x y ??. erewrite Pos.le_antisym; eauto.
Qed.
Next Obligation.
  move=>x y. unfold join. destruct decide=>//.
Qed.
Next Obligation.
  move=> x y. unfold join. destruct decide => //. apply Pos.le_nlt. lia.
Qed.
Next Obligation.
  move=>x y z. unfold join; destruct decide=>?? //.
Qed.
Next Obligation.
  move=>x y. unfold meet. destruct decide => //. apply Pos.le_nlt. lia.
Qed.
Next Obligation.
  move=>x y. unfold meet. destruct decide=>//.
Qed.
Next Obligation.
  move=>x y z. unfold meet; destruct decide=>?? //.
Qed.

#[global] Instance pos_leibnizequiv : LeibnizEquiv positive :=
  λ _ _ H, H.

#[global] Instance pos_Total :
  Total (@sqsubseteq positive _).
Proof.
  move => x y. case: (decide (x ≤ y)%positive); first tauto.
  move => /Pos.lt_nle /Pos.lt_le_incl. tauto.
Qed.

#[global] Instance pos_sqsubseteq_decision :
  RelDecision (@sqsubseteq positive _).
Proof.
  intros ??. apply _.
Qed.

Section gset.
  Context (A: Type) `{Countable A}.

  (* Lattice of sets with subseteq *)
  Program Canonical gset_Lat  :=
    Make_Lat (gset A) (≡) subseteq union intersection
             _ _ _ _ _ _ _ _ _ _ _ _ _.
  Next Obligation.
    move => ???. by apply union_subseteq_l.
  Qed.
  Next Obligation.
    move => ???. by apply union_subseteq_r.
  Qed.
  Next Obligation.
    move => ???. by apply union_least.
  Qed.
  Next Obligation.
    move => ???. by apply intersection_subseteq_l.
  Qed.
  Next Obligation.
    move => ???. by apply intersection_subseteq_r.
  Qed.
  Next Obligation.
    move => ??????. by apply intersection_greatest.
  Qed.

  #[global] Instance gset_Lat_bot :
    LatBottom (∅ : gset_Lat).
  Proof.
    done.
  Qed.

  #[global] Instance gset_sqsubseteq_dec : RelDecision (A:=gset A) (⊑) :=
    _.
End gset.

(* We restrict these to semilattices to avoid divergence. *)
#[global] Instance flip_total {A : latticeT} :
  @Total A (⊑) →
  @Total A (flip (⊑)).
Proof.
  move=>Ht x y. destruct (Ht y x); auto.
Qed.
#[global] Instance flip_sqsubseteq_antisymm {A : latticeT} :
  @AntiSymm A (≡) (⊑) →
  @AntiSymm A (≡) (flip (⊑)).
Proof.
  move=>?????. by apply (anti_symm (⊑)).
Qed.
#[global] Instance flip_sqsubseteq_antisymm_L {A : latticeT} :
  @AntiSymm A (=) (⊑) →
  @AntiSymm A (=) (flip (⊑)).
Proof.
  move=>?????. by apply (anti_symm (⊑)).
Qed.
#[global] Instance flip_partialorder {A : latticeT} :
  @PartialOrder A (⊑) →
  @PartialOrder A (flip (⊑)).
Proof.
  move=>?. constructor; apply _.
Qed.

From iris.bi Require Import
  big_op.
From iris.proofmode Require Import
  tactics.

Section big_sepL2.
  Lemma big_sepL2_split {PROP : bi} {A B : Type} (xs : list A) (ys : list B) (Φ Ψ : nat → _ → PROP) :
    length xs = length ys →
    ([∗ list] i↦x ∈ xs, Φ i x) ∗ ([∗ list] i↦y ∈ ys, Ψ i y) ⊢
    ([∗ list] i↦x;y ∈ xs;ys, Φ i x ∗ Ψ i y).
  Proof.
    iIntros (?) "(HΦ & HΨ)". rewrite big_sepL2_sep. iSplitL "HΦ".
    { rewrite big_sepL2_alt. iSplit; first done.
      rewrite -(big_sepL_fmap fst) fst_zip; last lia. done. }
    { rewrite big_sepL2_alt. iSplit; first done.
      rewrite -(big_sepL_fmap snd) snd_zip; last lia. done. }
  Qed.

  #[local] Lemma destruct_list_end {A : Type} (xs : list A) :
    xs = [] ∨ ∃ xs' x, xs = xs' ++ [x].
  Proof.
    induction xs as [|x0 xs' IH]; first auto. right. destruct IH as [->|(xs'' & x & ->)].
    - by exists [], x0.
    - by exists (x0 :: xs''), x.
  Qed.

  #[global] Instance big_sepL2_into_pure {PROP : bi} {A B : Type} (xs : list A) (ys : list B)
    (Φ φ : nat → A → B → _) :
    (∀ i x y, xs !! i = Some x → ys !! i = Some y → IntoPure (Φ i x y) (φ i x y)) →
    IntoPure (PROP:=PROP) ([∗ list] i↦x;y ∈ xs;ys, Φ i x y)
      (length xs = length ys ∧
       ∀ i x y, xs !! i = Some x → ys !! i = Some y → φ i x y).
  Proof.
    intros H. rewrite /IntoPure. iIntros "Hxys".
    iAssert ⌜length xs = length ys⌝%I as %Hlen. { by iApply big_sepL2_length. }
    iSplit; first done.
    iInduction xs as [|x xs'] "IH" using rev_ind forall (ys H Hlen); first by destruct ys.
    destruct (destruct_list_end ys) as [->|(ys' & y & ->)].
    { exfalso. rewrite app_length /= in Hlen. lia. }
    assert (length xs' = length ys') as Hlen'. { rewrite 2!app_length/= in Hlen. lia. }
    iDestruct (big_sepL2_app_inv with "Hxys") as "[Hxys' Hxy]"; first naive_solver.
    eassert _ as H'; last iDestruct ("IH" $! ys' H' Hlen' with "Hxys'") as %Hxys'.
    { intros. apply H; by apply lookup_app_l_Some. }
    iClear "IH Hxys'". rewrite /= (right_id emp%I) Nat.add_0_r.
    assert (IntoPure (Φ (length xs') x y) (φ (length xs') x y)) as H0.
    { apply H; rewrite lookup_app_r ?Hlen' ?Nat.sub_diag; done. }
    iDestruct "Hxy" as %Hxy. iPureIntro. clear dependent PROP Hlen.
    intros i x0 y0 EQxs EQys.
    destruct (decide (i < length xs')%nat).
    { rewrite lookup_app_l in EQxs; last done.
      rewrite lookup_app_l in EQys; last by rewrite -Hlen'.
      auto.
    } {
      assert (i = length xs') as ->.
      { apply lookup_lt_Some in EQxs. rewrite app_length/= in EQxs. lia. }
      rewrite lookup_app_r Hlen' ?Nat.sub_diag /= in EQxs; last done. injection EQxs as <-.
      rewrite lookup_app_r Hlen' ?Nat.sub_diag /= in EQys; last done. injection EQys as <-.
      done.
    }
  Qed.
End big_sepL2.

From Coq Require Import
  QArith.Qcanon.

Program Canonical Qp_Lat :=
  Make_Lat (Qp) (=) (≤)%Qp
           (λ (p q : Qp), if (decide (p ≤ q)%Qp) then q else p)
           (λ (p q : Qp), if (decide (p ≤ q)%Qp) then p else q)
           _ _ _ _ _ _ _ _ _ _ _ _ _.
Next Obligation.
  move=> x y. unfold sqsubseteq, join. destruct decide=>//.
Qed.
Next Obligation.
  move=> x y. unfold sqsubseteq, join. destruct decide as [|?%Qp.lt_nge]=>//.
  by apply Qp.lt_le_incl.
Qed.
Next Obligation.
  move=>x y z. unfold join; destruct decide=>?? //.
Qed.
Next Obligation.
  move=> x y. unfold sqsubseteq, meet. destruct decide as [|?%Qp.lt_nge]=>//.
  by apply Qp.lt_le_incl.
Qed.
Next Obligation.
  move=>x y. unfold sqsubseteq, meet. destruct decide=>//.
Qed.
Next Obligation.
  move=>x y z. unfold meet; destruct decide=>?? //.
Qed.

#[global] Instance Qp_leibnizequiv : LeibnizEquiv Qp :=
  λ _ _ H, H.
