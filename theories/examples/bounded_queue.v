From iris.algebra Require Import
  excl_auth
  csum
  numbers
  list.
From iris.unstable.algebra Require Import
  list.
From iris.base_logic Require Import
  invariants.

From cosmo Require Import
  prelude.
From cosmo.common Require Import
  list.
From cosmo.iris.base_logic Require Import
  lib.lattice.
From cosmo.language Require Export
  proofmode
  atomic.

Set Default Proof Using "Type".

Open Scope Z.

(** Implementation **)

Section bounded_queue.
  Context (capacity : nat) (capacity_min : capacity ≥ 1).

  Definition init_array (α : atomicity) : val := λ: "n" "f",
    let: "a" := Alloc α "n" #() in
    (rec: "loop" "i" :=
      if: "n" ≤ "i" then "a" else (
        Write α "a" "i" ("f" "i") ;;
        "loop" ("i" + #1)
      )
    ) #0.

  (*
     ICFP21: Below follows the implementation, in our toy deep-embedded language,
     of the bounded queue with a circular buffer. It corresponds to Figure 8 of
     the paper. “capacity” is a non-zero integer constant.

     It is worth noting that the toy language is untyped. This code, in particular,
     does not typecheck, because it uses the unit value as a dummy element for
     filling cells in the queue, regardless of the intended type for elements of
     the queue. To make it typecheck, assuming it was actual OCaml code, there
     would be a number of options:
      (1) store option values in the queue: that implies a significant overhead
          (when allocating the boxes and when reading these extra indirections);
      (2) when creating the queue, ask the user for an arbitrary inhabitant of the
          element type, just for the sake of using it as a dummy value internally:
          that is odd from the user perspective, and requires storing the dummy as
          an additional field in the data structure);
      (3) use unsafe OCaml features to evade the type system (i.e. Obj.magic).
   *)

  Definition make : val := λ: <>,
    let: "elements" := Alloc NonAtomic #capacity #() in
    let: "statuses" := init_array Atomic #capacity (λ: "i", #2*"i") in
    let: "tail" := ref_at #0 in
    let: "head" := ref_at #0 in
    ("tail", "head", "statuses", "elements").

  Definition try_enqueue : val := λ: "q" "x",
    let: ("tail", "head", "statuses", "elements") := "q" in
    let: "h" := !at "head" in
    let: "hmod" := "h" `mod` #capacity in
    let: "s" := Read Atomic "statuses" "hmod" in
    if: ("s" = #2*"h") && CAS_ref "head" "h" ("h" + #1) then (
      Write NonAtomic "elements" "hmod" "x" ;;
      Write Atomic "statuses" "hmod" (#2*"h" + #1) ;;
      #true
    )
    else
      #false.

  Definition enqueue : val := rec: "enqueue" "q" "x" :=
    if: try_enqueue "q" "x" then
      #()
    else
      "enqueue" "q" "x".

  Definition try_dequeue : val := λ: "q",
    let: ("tail", "head", "statuses", "elements") := "q" in
    let: "t" := !at "tail" in
    let: "tmod" := "t" `mod` #capacity in
    let: "s" := Read Atomic "statuses" "tmod" in
    if: ("s" = #2*"t" + #1) && CAS_ref "tail" "t" ("t" + #1) then (
      let: "x" := Read NonAtomic "elements" "tmod" in
      Write NonAtomic "elements" "tmod" #() ;; (* optional, useful for GC *)
      Write Atomic "statuses" "tmod" (#2*("t" + #capacity)) ;;
      SOME "x"
    )
    else
      NONEV.

  Definition dequeue : val := rec: "dequeue" "q" :=
    match: try_dequeue "q" with
      SOME "x" => "x"
    | NONE     => "dequeue" "q"
    end.

  (** Specification **)

  (* ICFP21: Here is the construction of the lattice described by the paper in
     Section 4.3 “Monotonicity of statuses“. *)
  (* Here we define a lattice structure for pairs Z × view, equipped with the
     lexicographic order where the order on views is flipped. This serves to
     express the monotonicity of statuses: the “status” for a given index only
     grows AND, as long as it has not grown, the view stored in this atomic
     location has not grown either. *)
  Section lexico.
    Inductive statuspair : Type := StatusPair { statuspair_s : Z ; statuspair_V : view }.
    (** Lattice for statuspair *)
    Definition statuspair_le '(StatusPair s1 V1) '(StatusPair s2 V2) : Prop :=
      s1 < s2 ∨ (s1 = s2 ∧ V2 ⊑ V1).
    Program Canonical statuspair_Lat :=
      Make_Lat statuspair (=) statuspair_le
               (λ '(StatusPair s1 V1) '(StatusPair s2 V2),
                  if decide (s1 < s2) then StatusPair s2 V2
                  else if decide (s2 < s1) then StatusPair s1 V1
                  else StatusPair s1 (V1 ⊓ V2) )
               (λ '(StatusPair s1 V1) '(StatusPair s2 V2),
                  if decide (s1 < s2) then StatusPair s1 V1
                  else if decide (s2 < s1) then StatusPair s2 V2
                  else StatusPair s1 (V1 ⊔ V2) )
               _ _ _ _ _ _ _ _ _ _ _ _ _.
    Next Obligation. exact (populate $ StatusPair 0 ∅). Qed.
    Next Obligation.
      exists.
      - intros [s V]. by right.
      - intros [s1 V1][s2 V2][s3 V3] [? | [??]] [? | [??]] ; [left ; lia ..|].
        right. split ; by etrans.
    Qed.
    Next Obligation.
      intros [s1 V1][s2 V2] [? | [??]] [? | [??]] ; [exfalso ; lia ..|].
      f_equal ; solve_lat.
    Qed.
    Next Obligation.
      intros [s1 V1][s2 V2]. rewrite /sqsubseteq/join/=.
      case_decide ; [by left|]. case_decide ; [by right|]. right. split ; solve_lat.
    Qed.
    Next Obligation.
      intros [s1 V1][s2 V2]. rewrite /sqsubseteq/join/=.
      case_decide ; [by right|]. case_decide ; [by left|]. right. split ; [lia|solve_lat].
    Qed.
    Next Obligation.
      intros [s1 V1][s2 V2][s3 V3] [? | [??]] [? | [??]].
      all: cbn ; case_decide ; [|case_decide] ; first [by left | by right|idtac].
      all: right ; split ; [done|].
      - exfalso. lia.
      - solve_lat.
    Qed.
    Next Obligation.
      intros [s1 V1][s2 V2]. rewrite /sqsubseteq/meet/=.
      case_decide ; [by right|]. case_decide ; [by left|]. right. split ; solve_lat.
    Qed.
    Next Obligation.
      intros [s1 V1][s2 V2]. rewrite /sqsubseteq/meet/=.
      case_decide ; [by left|]. case_decide ; [by right|]. right. split ; [lia|solve_lat].
    Qed.
    Next Obligation.
      intros [s1 V1][s2 V2][s3 V3] [? | [??]] [? | [??]].
      all: cbn ; case_decide ; [|case_decide] ; first [by left | by right|idtac].
      all: right ; split ; [done|].
      - exfalso. lia.
      - by apply lat_join_lub.
    Qed.

    Instance statuspair_leibnizequiv : LeibnizEquiv statuspair := λ _ _ H, H.

    Instance statuspair_sqsubseteq_decision : RelDecision (@sqsubseteq statuspair _).
    Proof.
      intros [s1 V1][s2 V2].
      destruct (decide (s1 < s2)) ; first (left ; by left).
      destruct (decide (s2 < s1)) ; first (right ; intros [? | [? _]] ; lia).
      destruct (decide (V2 ⊑ V1)) ; first (left ; right ; split ; [lia|done]).
      right. by intros [? | [_ ?]].
    Qed.

    Lemma statuspair_le_Z_le (sV1 sV2 : statuspair) :
      sV1 ⊑ sV2 → statuspair_s sV1 ≤ statuspair_s sV2.
    Proof. destruct sV1, sV2. intros [? | [? _]] ; cbn ; lia. Qed.
  End lexico.

  (* ICFP21: The typeclass “queueG” describes which CMRAs we need for specifying
     the data structure. In fact, the Iris framework is parameterized by a single,
     very large product CMRA named Σ, so we require this large product to include
     at least the desired CMRAs. *)
  Class queueG Σ := {
    (* public state *)
    #[local] queueG_G :: inG Σ (excl_authUR (prodO (prodO
      (* view of writers *)
        viewO
      (* view of readers *)
        viewO )
      (* values in the queue, with associated views *)
        (listO valViewO) )
    ) ;
    (* tokens for readers (no payload) and writers (a value and a view) *)
    #[local] queueG_tokensG :: inG Σ (authUR $ listUR $ optionUR $ csumR (exclR unitO) (exclR valViewO)) ;
    (* monotonicity of statuses *)
    #[local] queueG_mono_statusesG :: inG Σ (listUR $ authUR $ latUR (option_Lat statuspair_Lat)) ;
  }.

  Section Spec.
    Context `{!cosmoG Σ, !queueG Σ}.

    Implicit Types (q : val) (tail head statuses elements : location).
    Implicit Types (γ γtoks γmonos : gname) (V Vt Vh : view).
    Implicit Types (x dummy : val) (xV : val * view) (xVs : list (val * view)).
    Implicit Types (s : Z) (sV : Z * view) (sVs : list (Z * view)).
    Implicit Types (t h i tmod hmod imod : Z).

    Open Scope Z.

    Notation "⌊ z ⌋" := (Z.to_nat z).
    Notation "x -- y" := (Z.sub x%Z y%Z) (at level 50, left associativity).
    (* NOTE: Coq defines Zlength as a recursive function. *)
    Notation Zlength ls := (Z.of_nat (length ls)) (only parsing).

    (* ICFP21: This is the definition of the ghost state representing slot tokens
       (Section 4.5 and Figure 9d of the paper).
       Whereas the paper uses finite maps over Z, here we model them using lists.
       There isn’t really a technical advantage in doing so, to be honest, and it
       requires careful shifting so that no negative index is involved. *)
    Definition token_read γtoks i : iProp Σ :=
      own γtoks (◯ {[ ⌊i + capacity⌋ := Some $ Cinl $ Excl () ]}).
    Definition token_write γtoks i xV : iProp Σ :=
      own γtoks (◯ {[ ⌊i⌋ := Some $ Cinr $ Excl xV ]}).
    Definition tokens_auth γtoks t h xVs : iProp Σ :=
      own γtoks (● (
        replicate ⌊t⌋ None                                      (* 0 .. t          ; length = t   *)
        ++ ((λ xV, Some $ Cinr $ Excl xV) <$> xVs)              (* t .. h          ; length = h-t *)
        ++ replicate ⌊t--(h--capacity)⌋ (Some $ Cinl $ Excl ()) (* h .. t+capacity ; length = t-(h-capacity) *)
      )).

  (* TODO: merge this into Iris *)
    Lemma list_lookup_local_update {A : ucmra} (l l' : list A) (i : nat) (x x' y y' : A) :
      l !! i ≡ Some x →
      l' ≡ <[i := y]> l →
      (x, x') ~l~> (y, y') →
      (l, {[i := x']})  ~l~>  (l', {[i := y']}).
    Proof. clear.
      move=> Hlookup -> Hxy n lo /= Hvalidl Hdistl.
      rewrite ->(list_dist_lookup (A:=A)) in Hdistl.
      case: (Hxy n (lo ≫= lookup i)) => /= [||Hvalidy Hdisty].
      { by eapply list_lookup_validN_Some, equiv_dist. }
      { specialize (Hdistl i). revert Hdistl.
        rewrite list_lookup_opM list_lookup_singletonM Hlookup.
        case: (lo ≫= lookup i) => [?|] ; intros ?%(inj Some) ; rewrite ?right_id //. }
      assert (i < length l)%nat.
      { destruct (l !! i) eqn:? ; by [eapply lookup_lt_Some | inversion Hlookup]. }
      split.
      { apply list_lookup_validN => j.
        destruct (decide (i = j)) as [<- | Hne].
        - rewrite list_lookup_insert //.
        - rewrite list_lookup_insert_ne //. by apply list_lookup_validN. }
      { apply list_dist_lookup => j.
        specialize (Hdistl j). revert Hdistl. rewrite 2!list_lookup_opM.
        destruct (lt_eq_lt_dec i j) as [[ Hij | <- ]| Hji ].
        - rewrite 2?list_lookup_singletonM_gt // list_lookup_insert_ne //. lia.
        - rewrite 2!list_lookup_singletonM list_lookup_insert // Hdisty.
          by case: (lo ≫= lookup i).
        - rewrite 2?list_lookup_singletonM_lt // list_lookup_insert_ne //. lia. }
    Qed.

  (* TODO: merge this into Iris *)
    Lemma list_middle_local_update {A : ucmra} (l1 l2 : list A) (x x' y y' : A) :
      (x, x') ~l~> (y, y') →
      (l1 ++ x :: l2, {[length l1 := x']})  ~l~>  (l1 ++ y :: l2, {[length l1 := y']}).
    Proof. clear.
      intros ?. eapply list_lookup_local_update ; last done.
      - rewrite lookup_app_r // Nat.sub_diag //=.
      - rewrite insert_app_r_alt // Nat.sub_diag //=.
    Qed.

    (* ICFP21: The lemmas below correspond to properties of the tokens. They are
       more specific than the properties shown in Figure 10c of the paper. *)

    Lemma own_token_list_read γtoks t h xVs i :
      0 ≤ t →
      -capacity ≤ i →
      Z.of_nat $ length xVs = h -- t →
      tokens_auth γtoks t h xVs -∗
      token_read γtoks i -∗
      ⌜h -- capacity ≤ i < t⌝.
    Proof. clear.
      iIntros (???) "H● H◯". iCombine "H● H◯" as "H". rewrite own_valid.
      iDestruct "H" as %Hvalid. iPureIntro.
      apply auth_both_valid_discrete in Hvalid as [Hle Hvalid].
      apply list_singletonM_included in Hle as (otok & Hlookup & Hle).
      apply option_included in Hle as [ |(? & tok & [=<-] & -> & Hle)] ; first discriminate.
      destruct Hle as [ <-%leibniz_equiv | Hle ].
      { apply lookup_app_Some in Hlookup as [Hlookup|[Hineq1 Hlookup]] ; last
        apply lookup_app_Some in Hlookup as [Hlookup|[Hineq2 Hlookup]].
        - by apply lookup_replicate in Hlookup as [[=] _].
        - by apply list_lookup_fmap_inv in Hlookup as (? & [=] & _).
        - apply lookup_replicate in Hlookup as [_ Hlookup].
          rewrite replicate_length fmap_length in Hineq1 Hineq2 Hlookup.
          rewrite (_ : (⌊i + capacity⌋ - ⌊t⌋ - length xVs)%nat
                      = ⌊i -- (h -- capacity)⌋) in Hlookup ;
            last lia.
          lia. }
      exfalso.
      apply leibniz_equiv_iff in Hlookup.
      apply csum_included in Hle
        as [   ->
           |[ (? & ? & [=<-] & -> & e' & ->%leibniz_equiv)
            | (? & _ & [=]   & _)
           ]] ;
        [|] ; by destruct (list_lookup_valid_Some _ _ _ Hvalid Hlookup).
    Qed.

    Lemma own_token_list_write γtoks t h xVs i xV :
      0 ≤ t →
      0 ≤ i →
      Zlength xVs = h -- t →
      tokens_auth γtoks t h xVs -∗
      token_write γtoks i xV -∗
      ⌜t ≤ i < h  ∧  xVs !! (i -- t) = Some xV⌝.
    Proof. clear.
      iIntros (???) "H● H◯". iCombine "H● H◯" as "H". rewrite own_valid.
      iDestruct "H" as %Hvalid. iPureIntro.
      apply auth_both_valid_discrete in Hvalid as [Hle Hvalid].
      apply list_singletonM_included in Hle as (otok & Hlookup & Hle).
      apply option_included in Hle as [ |(? & tok & [=<-] & -> & Hle)] ; first discriminate.
      destruct Hle as [ <-%leibniz_equiv | Hle ].
      { apply lookup_app_Some in Hlookup as [Hlookup|[Hineq1 Hlookup]] ; last
        apply lookup_app_Some in Hlookup as [Hlookup|[Hineq2 Hlookup]].
        - by apply lookup_replicate in Hlookup as [[=] _].
        - apply list_lookup_fmap_inv in Hlookup as (_ & [=<-] & Hlookup).
          rewrite replicate_length in Hineq1 Hlookup.
          rewrite (_ : (⌊i⌋ - ⌊t⌋)%nat = ⌊i--t⌋) in Hlookup ; last lia.
          rewrite -list_lookup_Z_to_nat in Hlookup ; last lia.
          split ; last done. apply list_lookup_Z_lt_Some in Hlookup. lia.
        - by apply lookup_replicate in Hlookup as [[=] _]. }
      exfalso.
      apply leibniz_equiv_iff in Hlookup.
      apply csum_included in Hle
        as [   ->
           |[ (? & _ & [=]   & _)
            | (? & ? & [=<-] & -> & e' & ->%leibniz_equiv)
           ]] ;
        [|] ; by destruct (list_lookup_valid_Some _ _ _ Hvalid Hlookup).
    Qed.

    Lemma own_token_list_update_to_write γtoks t h xVs xV :
      0 ≤ t →
      Zlength xVs = h -- t →
      tokens_auth γtoks t h xVs -∗
      token_read γtoks (h--capacity) -∗
      |==>
          (*⌜h -- capacity < t⌝
        ∗*) tokens_auth γtoks t (h+1) (xVs ++ [xV])
        ∗ token_write γtoks h xV.
    Proof. clear.
      iIntros (??) "H● H◯".
      iDestruct (own_token_list_read with "H● H◯") as "[% %]" ; try lia.
      iCombine "H● H◯" as "H". iMod (own_update with "H") as "[$$]" ; last done.
      apply auth_update.
      rewrite (_ : h -- capacity + capacity = h) ; last lia.
      rewrite (_ : ⌊t--(h--capacity)⌋ = S ⌊t--((h+1)--capacity)⌋) ; last lia.
      assert (⌊ t ⌋ ≤ ⌊ h ⌋)%nat by lia.
      assert (⌊h⌋ - ⌊t⌋ = length xVs)%nat as Hlen by lia.
      eapply list_lookup_local_update.
      { rewrite lookup_app_r replicate_length // Hlen
                lookup_app_r fmap_length // Nat.sub_diag //=. }
      { rewrite fmap_app -app_assoc
                insert_app_r_alt replicate_length // Hlen
                insert_app_r_alt fmap_length // Nat.sub_diag //=. }
      by apply option_local_update, exclusive_local_update.
    Qed.

    Lemma own_token_list_update_to_read γtoks t h xVs xV :
      0 ≤ t →
      h -- capacity ≤ t →
      Zlength xVs = h -- t →
      tokens_auth γtoks t h xVs -∗
      token_write γtoks t xV -∗
      |==> ∃ xVs',
          ⌜xVs = xV :: xVs'⌝
        ∗ tokens_auth γtoks (t+1) h xVs'
        ∗ token_read γtoks t.
    Proof. clear.
      iIntros (???) "H● H◯".
      iDestruct (own_token_list_write with "H● H◯") as "[[% %] #HxVs]" ; try lia.
      rewrite Zminus_diag. iDestruct "HxVs" as %HxVs.
      destruct xVs as [|? xVs'] ; first discriminate ; injection HxVs as -> ; cbn in *|-.
      iExists xVs'. iSplitR ; first done.
      iAssert ( |==> (_∗_) ∗ own γtoks (◯ {[⌊t⌋ := None]}) )%I with "[-]" as ">[$_]" ; last done.
      iCombine "H● H◯" as "H". iMod (own_update with "H") as "($&$&$)" ; last done.
      apply auth_update.
      etrans.
      {
        eapply list_lookup_local_update ; [|done|].
        { rewrite lookup_app_r replicate_length ?Nat.sub_diag //=. }
        by apply delete_option_local_update, _.
      }
      {
        rewrite insert_app_r_alt replicate_length // Nat.sub_diag /=.
        rewrite (_ : ⌊t+1--(h--capacity)⌋ = S ⌊t--(h--capacity)⌋) ?replicate_S_end ; last try lia.
        rewrite cons_middle !app_assoc -replicate_S_end (_ : S ⌊t⌋ = ⌊t+1⌋) ; last lia.
        set li := (_ ++ _) ++ _.
        rewrite (_ : ⌊t+capacity⌋ = length li) ; last first.
        { rewrite !app_length !replicate_length fmap_length. lia. }
        rewrite - {1} [ {[⌊t⌋ := None]} ] left_id.
        by apply op_local_update_frame, list_alloc_singletonM_local_update.
      }
    Qed.

    Definition queueN : namespace :=
      nroot .@ "bounded_queue".

    Notation seqZ' a b := (seqZ a%Z (b -- a)).

    (*
      ICFP21: Here is the internal invariant of the bounded queue as described in
      Figure 9e of the paper (“queue_proto” being called “QueueInvInner” in the
      paper).

      Vt and Vh are the head and tail views, respectively (denoted by calligraphic
      letters T and H in the paper).
      xVs is the list of value-view pairs appearing in the public state, denoted
      by (vt, Vt), …, (vh, Vh) in the paper.
      sVs in the list of the value-view pairs of the atomic locations in the array
      “statuses”. It is denoted by (s0, S0), …, (s_{C-1}, S_{C-1}) in the paper.
     *)

    Definition queue_proto γ γtoks γmonos tail head statuses elements : iProp Σ := (
      ∃ t h Vt Vh xVs sVs,
        (* authority over the public state: *)
          own γ (●E (Vt, Vh, xVs))
        (* various arithmetic conditions: *)
        ∗ ⌜0 ≤ t ≤ h ≤ t + capacity⌝
        ∗ ⌜Zlength xVs = h -- t⌝
        ∗ ⌜length sVs = capacity⌝
        (* authority over the ghost state representing the tokens: *)
        ∗ tokens_auth γtoks t h xVs
        (* authority over the ghost state representing the monotonicity of statuses: *)
        ∗ own (A:=listUR _) γmonos ((λ sV, ● to_latT (Some (StatusPair sV.1 sV.2))) <$> sVs)
        (* ownership and value of the physical locations “tail”, “head“ and “statuses“: *)
        ∗ tail ↦at(#t, Vt)
        ∗ head ↦at(#h, Vh)
        ∗ statuses *↦at() ((λ sV, (#sV.1, sV.2)) <$> sVs)
        (* description of slots: *)
          (* for every i in the range [h-capacity, t): *)
        ∗ ([∗ list] i ∈ seqZ' (h -- capacity) t,
            let imod := i mod capacity in
            (* cell bearing no value, available for next round: *)
              ( ∃ dummy V,
                  ⌜sVs !! imod = Some ((2*(i+capacity))%Z, V)⌝
                ∗ (elements.[imod] ↦ dummy) V
                ∗ token_read γtoks i
              )
            (* cell being emptied by a dequeuer: *)
            ∨ ( ∃ V,
                  ⌜sVs !! imod = Some ((2*i+1)%Z, V)⌝
  (*               ∗ ⌜0 ≤ i⌝ *)
              )
          )
          (* for every i in the range [t, h): *)
        ∗ ([∗ list] i;xV ∈ seqZ' t h ; xVs,
            let imod := i mod capacity in
            (* cell bearing a value: *)
              ( ∃ V,
                  ⌜xV.2 ⊑ V⌝
                ∗ ⌜sVs !! imod = Some ((2*i+1)%Z, V)⌝
                ∗ (elements.[imod] ↦ xV.1) V
                ∗ token_write γtoks i xV
              )
            (* cell being filled with a value by an enqueuer: *)
            ∨ ( ∃ V,
                  ⌜sVs !! imod = Some ((2*i)%Z, V)⌝
              )
          )
      (* NOTE: additional assertions that we can maintain in the invariant, but
               which are not required by this proof:
        ∗ has_length statuses capacity
        ∗ has_length elements capacity
        ∗ ⌜Forall (λ sV, 0 ≤ sV.1) sVs⌝
        ∗ monotonicity of t
        ∗ monotonicity of h
      *)
    )%I.

    Definition queue_inv q γ : iProp Σ := (
      ∃ γtoks γmonos tail head statuses elements,
          ⌜q = (#tail, #head, #statuses, #elements)%V⌝
        ∗ inv queueN (queue_proto γ γtoks γmonos tail head statuses elements)
    )%I.

    Global Instance queue_inv_persistent q γ : Persistent (queue_inv q γ).
    Proof. by apply _. Qed.

    (* ICFP21: this is the predicate “IsQueue” from the paper, which exposes the
       public state of the queue (Figure 9a of the paper). *)
    Definition is_queue γ Vt Vh xVs : iProp Σ := (
      own γ (◯E (Vt, Vh, xVs))
    )%I.

  (*
    Definition Is_queue q Vt Vh xVs : iProp Σ := (
      ∃ (γ : gname),
        queue_inv q γ ∗ is_queue γ Vt Vh xVs
    )%I.
  *)

    Lemma own_list_auth_update_frag
    {A : latticeT} `{inG Σ (listUR $ authUR $ latUR (option_Lat A))}
    (γ : gname) (xs : list A) (i : nat) (x : A) :
      xs !! i = Some x →
      own (A:= listUR _) γ ((λ (x : A), ● to_latT (Some x)) <$> xs) ⊢ |==>
        own (A:= listUR _) γ ((λ (x : A), ● to_latT (Some x)) <$> xs)
      ∗ own (A:= listUR _) γ {[i := ◯ to_latT (Some x)]}.
    Proof. clear.
      intros Hi. rewrite -own_op. apply own_update.
      revert xs Hi ; induction i as [|i IH] => xs Hi.
      { destruct xs as [|x0 xs] ; inversion Hi ; subst x0.
        apply cons_update ; last by rewrite right_id.
        apply auth_update_alloc, latT_local_unit_update. reflexivity. }
      { destruct xs as [|x0 xs] ; first discriminate.
        apply cons_update ; first by rewrite right_id. by apply IH. }
    Qed.

    Lemma own_list_auth_both_le
    {A : latticeT} `{inG Σ (listUR $ authUR $ latUR (option_Lat A))}
    (γ : gname) (xs : list A) (i : nat) (x y : A) :
      xs !! i = Some y →
        own (A:= listUR _) γ {[i := ◯ to_latT (Some x)]}
      ∗ own (A:= listUR _) γ ((λ (x : A), ● to_latT (Some x)) <$> xs) ⊢
          ⌜x ⊑ y⌝.
    Proof. clear.
      rewrite -own_op own_valid. iIntros "!% /=".
      revert xs ; induction i as [|i IH] => xs Hi.
      { destruct xs as [|x0 xs] ; inversion Hi ; subst x0. rewrite comm.
        by intros [[?%latT_included _]%auth_both_valid_discrete _]%cons_valid. }
      { destruct xs as [|x0 xs] ; first discriminate. rewrite fmap_cons.
        intros [_ ?]%cons_valid. by apply (IH xs). }
    Qed.

    Lemma seqZ_app (len1 len2 start : Z):
      0 ≤ len1 →
      0 ≤ len2 →
      seqZ start (len1 + len2) = seqZ start len1 ++ seqZ (start + len1) len2.
    Proof. clear.
      intros H1 H2. rewrite /seqZ Z2Nat.inj_add// seq_app fmap_app. f_equal.
      rewrite [(0 + _)%nat]comm -fmap_add_seq -list_fmap_compose.
      apply list_fmap_ext. cbn. lia.
    Qed.

    Lemma init_array_atomic_spec (E : coPset) (n : Z) (f : val) (φ : Z → val) V :
      {{{ monPred_in V ∗ ⌜0 ≤ n⌝
        ∗ <pers> ∀ (i : Z) Φ, (∀ y, ⌜y = φ i⌝ -∗ Φ y) -∗ WP f #i @ E {{ Φ }}
      }}}
        init_array Atomic #n f @ E
      {{{ arr, RET #arr ; ⎡ arr *↦at() ((λ i, (φ i, V)) <$> seqZ 0 n) ⎤ }}}.
    Proof using capacity_min.
      iIntros (Φ) "(#? & Hn & #Hf) HΦ". iDestruct "Hn" as %Hn.
      wp_lam. wp_alloc arr as "Harr". wp_let. wp_closure.
      pose k := 0. rewrite [in #0](_ : 0 = k)//.
      assert (0 ≤ k ≤ n) as Hk by lia.
      rewrite (_ : replicate _ _ = ((λ i, (φ i, V)) <$> seqZ 0 k) ++ replicate ⌊n--k⌋ (#(), ∅)) ;
        last (rewrite /k (_ : n-k = n) //; lia).
      clearbody k. iLöb as "IH" forall (k Hk). wp_pures.
      destruct (bool_decide _) eqn:Hcmp.
      {
        apply bool_decide_eq_true in Hcmp.
        wp_pures. iApply "HΦ". rewrite (_ : k = n) ; last lia.
        rewrite (_ : n - n = 0) ; last lia. rewrite (_ : ⌊0⌋ = 0%nat)//= right_id //.
      }
      {
        apply bool_decide_eq_false in Hcmp.
        wp_pures. wp_apply "Hf" ; iIntros (?->). wp_write_block at V as ??? "_".
        { rewrite app_length fmap_length seqZ_length replicate_length. lia. }
        rewrite (_ : <[_ := _]> _ = ((λ i, (φ i, V)) <$> seqZ 0 (k+1)) ++ replicate ⌊n--(k+1)⌋ (#(), ∅)) ; last first. {
          rewrite list_insert_Z_to_nat ; last lia.
          rewrite insert_app_r_alt fmap_length seqZ_length ; last lia.
          rewrite Nat.sub_diag (_ : ⌊n--k⌋ = S ⌊n--(k+1)⌋) /= ; last lia.
          rewrite seqZ_app ; [|lia..].
          rewrite /seqZ (_ : ⌊1⌋ = 1%nat)// fmap_app -app_assoc //=.
        }
        wp_op. iApply ("IH" $! (k+1) with "[] HΦ Harr"). iPureIntro. lia.
      }
    Qed.

    (* ICFP21: this is the spec of “make“, as presented in Figure 5 of the paper,
       along with its proof for this particular implementation (recall that
       “monPred_in V” is what is denoted by ↑V in the paper; ⎡P⎤ is the embedding
       of an objective assertion P (of type iProp) into general Cosmo assertions
       (of type vProp)). *)
    Lemma make_spec (E : coPset) V :
      {{{ monPred_in V }}}
        make #() @ E
      {{{ q γ, RET q ; ⎡queue_inv q γ⎤ ∗ ⎡is_queue γ V V []⎤ }}}.
    Proof.
      iIntros (Φ) "#HV HΦ". wp_lam.
      (* allocate locations *)
      wp_alloc elements as "Helements". rewrite Nat2Z.id.
      (* make ownership of elements objective and get the corresponding view: *)
      iDestruct (monPred_in_intro with "Helements") as (Ve) "[ #HVe Helements ]".
      wp_apply init_array_atomic_spec ; last iIntros (statuses) "Hstatuses".
      { iSplit ; last iSplit ; [ iExact "HVe" | iPureIntro ; lia |].
        iIntros "!>" (i Ψ) "HΨ". wp_lam. wp_pures. iApply "HΨ". done. }
      wp_ref tail at V as "Htail". wp_ref head at V as "Hhead".
      (* create ghost variables *)
      iMod (own_alloc (●E (V, V, []) ⋅ ◯E (V, V, []))) as (γ) "[Hγ● Hγ◯]".
      { by apply auth_both_valid_discrete. }
      epose (tokens := replicate capacity (Some $ Cinl $ Excl ())).
      iMod (own_alloc (● tokens ⋅ ◯ tokens)) as (γtoks) "[Hγtoks● Hγtoks◯]".
      { apply auth_both_valid_discrete. split ; first done.
        apply list_lookup_valid => ?. destruct (_ !! _) eqn:Hlookup ; last done.
        apply lookup_replicate in Hlookup as [[=->] _]. done. }
      epose (monos := (λ sV, ● to_latT (Some (StatusPair sV.1 sV.2))) <$> (
                      (λ i, (2*i, Ve)) <$> seqZ 0 capacity ) ).
      iMod (own_alloc monos) as (γmonos) "Hγmonos●".
      { apply list_lookup_valid => ?. rewrite list_lookup_fmap.
        destruct (_ !! _) => //=. by apply Some_valid, auth_auth_valid. }
      (* create invariant *)
      iMod (inv_alloc _ _ (queue_proto γ γtoks γmonos tail head statuses elements)
            with "[- Hγ◯ HΦ]")  as "#I".
      {
        iIntros "!> !>". iExists 0, 0, V, V, [], _. iFrame "Hγ● Htail Hhead Hγmonos●".
        rewrite -(list_fmap_compose _ _ (seqZ _ _)). iFrame "Hstatuses".
        rewrite /tokens_auth (_ : ⌊0⌋ = 0%nat)// (_ : ⌊ 0 -- (0 -- capacity) ⌋ = capacity) ; last lia. iFrame "Hγtoks●".
        rewrite fmap_length seqZ_length. repeat (iSplit ; first (iPureIntro ; cbn ; lia)).
        rewrite /= right_id.
        rewrite (_ : 0 -- capacity = -capacity) ; last lia.
        rewrite /(seqZ' _ _) big_sepL_fmap (_ : ⌊ 0 -- (0 -- capacity) ⌋ = capacity) ; last lia.
        iDestruct "Helements" as "[_ Helements]". rewrite /tokens.
        iApply big_sepL_mono. { iIntros (?? _) "?". by iLeft. } cbn.
        pose k := capacity.
          rewrite [in replicate capacity](_ : capacity = k)//.
          rewrite [in replicate capacity](_ : capacity = k)//.
          rewrite [in seq 0 capacity](_ : capacity = k)//.
          assert (k ≤ capacity)%nat as Hk by lia.
          clearbody k.
        iInduction k as [|k'] "IH" forall (Hk) ; first done.
        rewrite 2!replicate_S_end.
        iDestruct "Helements" as "[Helements' Helementk]". rewrite replicate_length.
        rewrite (_ : replicate k' (Some $ Cinl $ Excl ()) ++ [ Some $ Cinl $ Excl () ]
                   = replicate k' (Some $ Cinl $ Excl ()) ⋅ {[ k' := Some $ Cinl $ Excl () ]}
                ) ; last first.
        { apply leibniz_equiv. rewrite -list_singletonM_snoc replicate_length [_ ⋅ _]comm //. }
        iDestruct "Hγtoks◯" as "[Hγtoks' Hγtokk]".
        rewrite seq_S.
        iDestruct ("IH" with "[] Helements' Hγtoks'") as "$" ; first (iPureIntro; lia).
        iClear "IH".
        rewrite /= 2!(right_id emp%I) (_ : k' + 0 = k')%nat ; last lia.
        rewrite /token_read.
        rewrite (_ : k' + -capacity + capacity = k') ?Nat2Z.id ; last lia.
        rewrite (_ : (k' + - capacity) mod capacity = k') ; last first.
        { rewrite -Zminus_mod_idemp_r Z.mod_same ?Z.sub_0_r ?Z.mod_small ; lia. }
        iExists _, _. iFrame. iPureIntro.
        rewrite /lookup/list_lookup_Z/=; destruct (bool_decide _) eqn:Hpos;
          last (apply bool_decide_eq_false in Hpos ; lia).
        rewrite list_lookup_fmap lookup_seqZ_lt /= ; first repeat f_equal ; lia.
      }
      (* return, providing the invariant and the representation predicate in the post-condition *)
      wp_pures. iApply "HΦ".
      iFrame "Hγ◯". repeat (iExists _). by iFrame "I".
    Qed.

    (* ICFP21: this is the spec of “try_enqueue“, as presented in Figure 5 of the
       paper, along with its proof.
       <<< ∀ x, P >>> e <<< Q, RET v >>> is the notation for a logically atomic
       triple (P,e,Q) with a binder x and returning value v.
       The first condition is about namespaces, it is an Iris technicality. *)
    Lemma try_enqueue_spec (E : coPset) q γ x V :
      E ## ↑queueN →
      ⎡queue_inv q γ⎤ -∗
      monPred_in V -∗
      <<< ∀ Vt Vh xVs, ⎡is_queue γ Vt Vh xVs⎤ >>>
          try_enqueue q x @ E
      <<< ∃ (b : bool),
        if b
        then ⎡is_queue γ Vt (Vh ⊔ V) (xVs ++ [(x,V)])⎤ ∗ monPred_in Vh
        else ⎡is_queue γ Vt Vh xVs⎤,
            (* NOTE: we can add this, even if useless: ∗ monPred_in Vh *)
      RET #b >>>.
    Proof using capacity_min.
      iIntros (HE). iIntros "#Inv #HV" (Φ) "AU".
      iDestruct "Inv" as (γtoks γmonos tail head statuses elements ->) "#Inv".
      wp_lam. repeat first [ wp_proj | wp_let ].

      (* (1) atomic read head *)
      (* --- open invariant *)
      wp_bind (!at _)%E.
      iInv queueN as (t0 h0 Vt0 Vh0 xVs0 sVs0) ">(Hγ● & %Hineq & Hlenx & Hlens & Htoks & Hmonos & Htail & Hhead & InvRest)" "InvClose".
      (* --- read h from head *)
      wp_read as "_".
      assert (0 ≤ h0) by lia.
      (* --- close invariant *)
      iMod ("InvClose" with "[-AU]") as "_". { repeat (iExists _). by iFrame. }
      clear dependent t0 Vt0 Vh0 xVs0 sVs0.

      (* pure steps *)
      iModIntro. wp_let. wp_op. wp_let.

      (* (2) atomic read statuses.[h % capacity] *)
      (* --- open invariant *)
      wp_bind (Read Atomic _ _)%E.
      iInv queueN as (t1 h1 Vt1 Vh1 xVs1 sVs1) ">(Hγ● & %Hineq & %Hlenx & %Hlens & Htoks & Hmonos & Htail & Hhead & Hstatuses & Hfree & Hfill)".
      (* --- read s1 from statuses.[h % capacity] *)
      wp_read_block as s1 V1 HsVs1 "HV1".
      { rewrite fmap_length -Hlens. apply Z_mod_lt. lia. }
      (* value s1 is in fact an integer s1' *)
      apply list_lookup_Z_Some_to_nat in HsVs1. rewrite list_lookup_fmap in HsVs1.
      destruct lookup as [[s1' ?]|] eqn:HsVs1' ; last done. injection HsVs1 as <- ->.
      (* --- get monotonicity witness for s1 *)
      iMod ( own_list_auth_update_frag _
          ((λ sV, StatusPair sV.1 sV.2) <$> sVs1)
          ⌊h0 `mod` capacity⌋
          with "[Hmonos]" )
        as "[Hmonos Hmonos1]" ;
          [|by rewrite -list_fmap_compose|].
      { by rewrite list_lookup_fmap HsVs1'. }
      rewrite -list_fmap_compose.
      (* --- close invariant *)
      iModIntro. iSplitR "AU Hmonos1". { repeat (iExists _). by iFrame. }
      cbn. clear dependent t1 h1 Vt1 Vh1 xVs1 sVs1.

      (* (3) test whether s1 = 2*h0 *)
      wp_pures. case_bool_decide ; last first.
      (* (3a) case: s1 ≠ 2*h0: return false *)
      { iApply wp_fupd. wp_pures. iMod "AU" as (???) "[? [_ H]]". by iApply "H". }
      (* (3b) case: s1 = 2*h0: CAS head *)
      subst s1'. wp_pures.

      (* --- open invariant *)
      wp_bind (CAS_ref _ _ _).
      iInv queueN as (t2 h2 Vt2 Vh2 xVs2 sVs2) ">(Hγ● & %Hineq & %Hlenx & %Hlens & Htoks & Hmonos & Htail & Hhead & Hstatuses & Hfree & Hfill)".
      (* --- CAS head *)
      wp_cas at (Vh2 ⊔ V) as "HVh2", Heqh | _ ; last first.
      (* (3b-a) case: h0 ≠ h2: CAS fails *)
      {
        (* --- close invariant *)
        iModIntro. iSplitR "AU Hmonos1". { repeat (iExists _). by iFrame. }
        (* --- return false *)
        iApply wp_fupd. wp_pures. iMod "AU" as (???) "[? [_ H]]". by iApply "H".
      }
      (* (3b-b) case: h0 = h2 *)
      injection Heqh as ->.

      simpl.

      (* --- Eliminate the absurd case where the buffer is full (h0 = t2 + capacity). *)
      destruct (decide (h0 = t2 + capacity)) as [Heq|Hineq2].
      {
        assert (length xVs2 > 0) by lia.
        destruct xVs2 as [|[x0 V0] xVs] ; first by exfalso.
        rewrite [seqZ t2 _] seqZ_cons ; last lia.
        rewrite big_sepL2_cons.
        iDestruct "Hfill" as "[Hfillt2 _]".
        iAssert False%I with "[Hmonos1 Hmonos Hfillt2]" as "?" ; last done.
        assert (h0 `mod` capacity = t2 `mod` capacity) as ->.
        { subst h0. by rewrite Zplus_mod Z_mod_same_full [_ + 0] Z.add_0_r Zmod_mod. }
        iDestruct "Hfillt2" as "[ Hex | Hex ]".
        { iDestruct "Hex" as (? _ HsVs) "_".
          iDestruct (own_list_auth_both_le _ ((λ sV, StatusPair sV.1 sV.2) <$> sVs2) with "[$Hmonos1 Hmonos]") as %Hle ;
            [|by rewrite -list_fmap_compose|].
          - by erewrite list_lookup_fmap, list_lookup_Z_Some_to_nat.
          - exfalso. apply statuspair_le_Z_le in Hle. cbn in Hle. lia. }
        { iDestruct "Hex" as (?) "%HsVs".
          iDestruct (own_list_auth_both_le _ ((λ sV, StatusPair sV.1 sV.2) <$> sVs2) with "[$Hmonos1 Hmonos]") as %Hle ;
            [|by rewrite -list_fmap_compose|].
          - by erewrite list_lookup_fmap, list_lookup_Z_Some_to_nat.
          - exfalso. apply statuspair_le_Z_le in Hle. cbn in Hle. lia. }
      }
      (* --- Now we know that cell number h0 is in the free-list. *)
      assert (h0 < t2 + capacity) by lia.
      rewrite [seqZ' _ t2]seqZ_cons ; last lia.
      (* --- Eliminate the absurd case where cell number h0 is “being emptied”. *)
      iDestruct "Hfree" as "[[Hex|Hex] Hfree]" ; last first.
      { iDestruct "Hex" as (?) "%HsVs".
        rewrite (_ : (h0 -- capacity) `mod` capacity = h0 `mod` capacity) in HsVs ; last first.
        { rewrite Zminus_mod Z.mod_same ; last lia.
          rewrite Z.sub_0_r Z.mod_mod// ; last lia. }
        iDestruct (own_list_auth_both_le _ ((λ sV, StatusPair sV.1 sV.2) <$> sVs2) with "[$Hmonos1 Hmonos]") as %Hle ;
          [|by rewrite -list_fmap_compose|].
        - by erewrite list_lookup_fmap, list_lookup_Z_Some_to_nat.
        - exfalso. apply statuspair_le_Z_le in Hle. cbn in Hle. lia. }
      (* --- Now we know that cell number h0 is really free. *)
      iDestruct "Hex" as (dummy V2) "(HsVs2 & Helement & Hr)".
      rewrite (_ : h0 -- capacity + capacity = h0) ; last lia.
      rewrite (_ : (h0 -- capacity) `mod` capacity = h0 `mod` capacity) ; last first.
      { rewrite Zminus_mod Z.mod_same ; last lia.
        rewrite Z.sub_0_r Z.mod_mod// ; last lia. }
      iDestruct "HsVs2" as %HsVs2.
      (* --- The view V2 is in fact V1, it hasn’t changed since we read it. *)
      iAssert ⌜V2 ⊑ V1⌝%I with "[Hmonos Hmonos1]" as %HV2.
      {
        iDestruct (own_list_auth_both_le _ ((λ sV, StatusPair sV.1 sV.2) <$> sVs2) with "[$Hmonos1 Hmonos]") as %Hle ;
          [|by rewrite -list_fmap_compose|].
        - by erewrite list_lookup_fmap, list_lookup_Z_Some_to_nat.
        - cbn in Hle. destruct Hle as [? | [_ ?]] ; [exfalso ; lia | done].
      }
      rewrite [in _ V2] HV2.
      (* --- We “commit” the atomic Hoare triple. *)
      iMod "AU" as (Vt3 Vh3 xVs3) "[Hγ◯ [_ Hclose]]".
      (* --- Unify Vt3 with Vt2, Vh3 with Vh2, xVs3 with xVs2. *)
      iDestruct (own_valid_2 with "Hγ● Hγ◯") as %[= <- <- <-]%excl_auth_agree_L.
      (* --- Update the public state *)
      iMod (own_update_2 with "Hγ● Hγ◯") as "[Hγ● Hγ◯]" ; first apply excl_auth_update.
      (* --- Forge a token_write from the token_read from the previous round. *)
      iMod (own_token_list_update_to_write with "Htoks Hr") as "[Htoks Hw]" ; try lia.

      iMod ("Hclose" $! true with "[$]") as "HΦ".

      (* --- close invariant *)
      iModIntro. iSplitR "Hmonos1 HΦ Hw Helement".
      {
        iModIntro. iNext. repeat (iExists _).
        rewrite (_ : Z.succ (h0 - capacity) = (h0+1) - capacity) ; last lia.
        rewrite (_ : Z.pred (t2 - (h0 - capacity)) = t2 - ((h0+1) - capacity)) ; last lia.
        iFrame "Hγ● Htoks Hmonos Htail Hhead Hstatuses Hfree".
        rewrite app_length /=.
        repeat (iSplitL "" ; first (iPureIntro ; eauto with lia)).
        rewrite (_ : h0 + 1 - t2 = (h0 - t2) + 1) ; last lia.
        rewrite seqZ_app ; try lia.
        iApply (big_sepL2_app with "Hfill").
        rewrite (_ : t2 + (h0 - t2) = h0) ; last lia.
        rewrite (eq_refl : seqZ h0 1 = [h0]) /= right_id.
        iRight. auto with iFrame.
      }
      iClear "HVh2 Hmonos1". clear dependent t2 Vh2 Vt2 xVs2 sVs2 V2.

      (* (4) non-atomic write to elements.[h0 % capacity] *)

      wp_pures.
      iDestruct (monPred_in_elim with "HV1 Helement") as "Helement" ; iClear (V1) "HV1".
      wp_write.
      iDestruct (monPred_in_intro with "Helement") as (Ve) "[#HVe Helement]".

      (* (5) atomic write to statuses.[h0 % capacity] *)

      (* --- open invariant *)
      wp_pures. wp_bind (Write Atomic _ _ _).
      iInv queueN as (t3 h3 Vt3 Vh3 xVs3 sVs3) ">(Hγ● & %Hineq & %Hlenx & %Hlens & Htoks & Hmonos & Htail & Hhead & Hstatuses & Hfree & Hfill)".

      (* --- perform write *)
      wp_write_block at (V ⊔ Ve) as s3 V3 _ "_" ; last clear s3 V3.
      { rewrite fmap_length Hlens. apply Z_mod_lt. lia. }

      (* --- close invariant *)
      iSplitR "HΦ".
      {
        rewrite -embed_fupd. iModIntro. repeat (iExists _).
        assert (0 ≤ h0 `mod` capacity). { apply Z.mod_pos. lia. }
        iDestruct (own_token_list_write with "Htoks Hw") as "[%Hh0 %HxVs3]" ; [lia .. |].
        (* frame Hstatuses first (so as to unify the existential list with sVs3) *)
        rewrite -(list_fmap_insert_Z _ _ _ (2*h0+1, V ⊔ Ve)).
        iFrame "Hstatuses".
        (* frame trivial things *)
        rewrite insert_Z_length.
        iFrame (Hineq Hlenx Hlens) "Hγ● Htoks Htail Hhead".

        iAssert (∃ V0 : view, ⌜sVs3 !! (h0 `mod` capacity) = Some ((2*h0)%Z, V0)⌝)%I with "[Hw Hfill]" as (V0) "%HsVs3".
        {
          assert (seqZ' t3 h3 !! ⌊h0 -- t3⌋ = Some h0) as HseqZ.
          { apply lookup_seqZ. lia. }
          apply list_lookup_Z_Some_to_nat in HxVs3.
          iDestruct (big_sepL2_lookup _ _ _ _ _ _ HseqZ HxVs3 with "Hfill") as "[Hfilli|?]" ;
            last done.
          iDestruct "Hfilli" as (?) "(_ & _ & _ & Hw')".
          iCombine "Hw Hw'" as "Hexcl". rewrite list_singletonM_op.
          iDestruct (own_valid with "Hexcl")
            as %[]%auth_frag_valid%list_singletonM_valid.
        }

        iSplitL "Hmonos" ; last iSplitL "Hfree".
        {
          (* 1st goal: Hmonos with updated sVs3 *)
          set f := (λ sV : Z * view, ● to_latT (Some $ StatusPair sV.1 sV.2)).
          iMod (own_update with "Hmonos") as "$" ; last done.
          rewrite list_fmap_insert_Z. simpl.
          apply list_lookup_Z_Some_to_nat in HsVs3.
          rewrite -(take_drop_middle sVs3 ⌊h0 `mod` capacity⌋ (2*h0, V0))//.
          rewrite fmap_app list_insert_Z_to_nat// insert_app_r_alt ; last first.
          { rewrite fmap_length take_length. lia. }
          rewrite [x in <[x := _]>](_ : _ = 0%nat) ; last first.
          { rewrite fmap_length take_length min_l ?Hlens ; first lia.
            pose proof (Z.mod_pos_bound h0 (Z.of_nat capacity)). lia. }
          eapply list_middle_update, auth_update_auth, latT_local_unit_update.
          simpl. left. lia.
        }
        {
          (* 2nd goal: Hfree *)
          iModIntro. iNext.
          iApply (big_sepL_mono with "Hfree").
          intros k _ [-> Hk]%lookup_seqZ.
          rewrite /= list_lookup_Z_insert_Z_ne ; first done.
          clear -Hineq Hh0 Hk. set h3k := h3 -- capacity + k. intros Heq.
          assert ((h0 -- h3k) `mod` capacity = h0 -- h3k) as Heq'.
          { apply Zmod_small. lia. }
          rewrite Zminus_mod Heq Zminus_diag Zmod_0_l in Heq'. lia.
        }
        {
          (* 3rd goal: Hfill *)
          iModIntro. iNext.
          apply list_lookup_Z_Some_to_nat in HxVs3.
          rewrite -(take_drop_middle xVs3 ⌊h0--t3⌋ (x, V))//.
          rewrite -(take_drop_middle (seqZ t3 (h3--t3)) ⌊h0--t3⌋ h0) ; last first.
          { apply lookup_seqZ. lia. }
          iDestruct (big_sepL2_app_inv with "Hfill") as "(Hfill1 & Hfilli & Hfill2)".
          { rewrite 2!take_length seqZ_length -Hlenx Nat2Z.id. auto. }
          iApply (big_sepL2_app with "[Hfill1]").
          {
            iApply (big_sepL2_mono with "Hfill1").
            iIntros (k j ? Hj ?) "?".
            rewrite list_lookup_Z_insert_Z_ne//.
            destruct (decide (k < ⌊h0--t3⌋)) ; last first.
            { rewrite lookup_take_ge in Hj ; [done|lia]. }
            rewrite lookup_take in Hj ; last lia.
            apply lookup_seqZ in Hj.
            intro Hij.
            assert ((h0 -- j) `mod` capacity = 0) as Hij' by
              rewrite Zminus_mod Hij Z.sub_diag//.
            rewrite Zmod_small in Hij' ; lia.
          }
          iSplitR "Hfill2" ; last first.
          {
            iApply (big_sepL2_mono with "Hfill2").
            iIntros (k j ? Hj ?) "?".
            rewrite list_lookup_Z_insert_Z_ne//.
            rewrite lookup_drop in Hj.
            apply lookup_seqZ in Hj.
            intro Hij.
            assert ((j - h0) `mod` capacity = 0) as Hij' by
              rewrite Zminus_mod Hij Z.sub_diag//.
            rewrite Zmod_small in Hij' ; lia.
          }
          rewrite list_lookup_Z_insert_Z ; last first.
          { rewrite Hlens. apply Z_mod_lt. lia. }
          iLeft.
          iDestruct "Hfilli" as "[Hfilli | Hfilli]".
          { iDestruct "Hfilli" as (?) "(_ & _ & _ & Hw')".
            iCombine "Hw Hw'" as "Hexcl". rewrite list_singletonM_op.
            iDestruct (own_valid with "Hexcl")
              as %[]%auth_frag_valid%list_singletonM_valid. }
          simpl. iExists (V ⊔ Ve).
          iFrame "Hw Helement". iPureIntro. split ; [solve_lat | done].
        }
      }
      clear dependent t3 h3 Vt3 Vh3 xVs3 sVs3.
      iModIntro.

      (* (6) return true *)
      wp_pures. by iApply "HΦ".
    Qed.

    (* ICFP21: this is the spec of “try_dequeue“, as presented in Figure 5 of the
       paper, along with its proof. Same remarks as with “try_enqueue”. *)
    Lemma try_dequeue_spec (E : coPset) q γ V :
      E ## ↑queueN →
      ⎡queue_inv q γ⎤ -∗
      monPred_in V -∗
      <<< ∀ Vt Vh xVs, ⎡is_queue γ Vt Vh xVs⎤ >>>
          try_dequeue q @ E
      <<< ∃ (opt_xV : option (val*view)),
        match opt_xV with
        | Some xV =>
            ∃ xVs', ⌜xVs = xV :: xVs'⌝ ∗ ⎡is_queue γ (Vt ⊔ V) Vh xVs'⎤ ∗ monPred_in Vt ∗ monPred_in xV.2
        | None =>
            ⎡is_queue γ Vt Vh xVs⎤
            (* NOTE: we can add this, even if useless: ∗ monPred_in Vt *)
        end,
      RET
        match opt_xV with
        | Some xV => SOMEV xV.1
        | None    => NONEV
        end
      >>>.
    Proof using capacity_min.
      iIntros (HE). iIntros "#Inv #HV" (Φ) "AU".
      iDestruct "Inv" as (γtoks γmonos tail head statuses elements ->) "#Inv".
      wp_lam. repeat first [ wp_proj | wp_let ].

      (* (1) atomic read tail *)
      (* --- open invariant *)
      wp_bind (!at _)%E.
      iInv queueN as (t0 h0 Vt0 Vh0 xVs0 sVs0) ">(Hγ● & %Hineq & Hlenx & Hlens & Htoks & Hmonos & Htail & Hhead & InvRest)" "InvClose".
      (* --- read t from tail *)
      wp_read as "_".
      assert (0 ≤ t0) by lia.
      (* --- close invariant *)
      iMod ("InvClose" with "[-AU]") as "_". { repeat (iExists _). by iFrame. }
      clear dependent h0 Vt0 Vh0 xVs0 sVs0.

      (* pure steps *)
      iModIntro. wp_let. wp_op. wp_let.

      (* (2) atomic read statuses.[h % capacity] *)
      (* --- open invariant *)
      wp_bind (Read Atomic _ _)%E.
      iInv queueN as (t1 h1 Vt1 Vh1 xVs1 sVs1) ">(Hγ● & %Hineq & %Hlenx & %Hlens & Htoks & Hmonos & Htail & Hhead & Hstatuses & Hfree & Hfill)".
      (* --- read s1 from statuses.[h % capacity] *)
      wp_read_block as s1 V1 HsVs1 "HV1".
      { rewrite fmap_length -Hlens. apply Z_mod_lt. lia. }
      (* value s1 is in fact an integer s1' *)
      apply list_lookup_Z_Some_to_nat in HsVs1. rewrite list_lookup_fmap in HsVs1.
      destruct lookup as [[s1' ?]|] eqn:HsVs1' ; last done. injection HsVs1 as <- ->.
      (* --- get monotonicity witness for s1 *)
      iMod ( own_list_auth_update_frag _
          ((λ sV, StatusPair sV.1 sV.2) <$> sVs1)
          ⌊t0 `mod` capacity⌋
          with "[Hmonos]" )
        as "[Hmonos Hmonos1]" ;
          [|by rewrite -list_fmap_compose|].
      { by rewrite list_lookup_fmap HsVs1'. }
      rewrite -list_fmap_compose.
      (* --- close invariant *)
      iModIntro. iSplitR "AU Hmonos1". { repeat (iExists _). by iFrame. }
      cbn. clear dependent t1 h1 Vt1 Vh1 xVs1 sVs1.

      (* (3) test whether s1 = 2*t0 + 1 *)
      wp_pures. case_bool_decide ; last first.
      (* (3a) case: s1 ≠ 2*t0 + 1: return None *)
      { iApply wp_fupd. wp_pures. iMod "AU" as (???) "[? [_ H]]". by iApply ("H" $! None). }
      (* (3b) case: s1 = 2*t0 + 1: CAS head *)
      subst s1'. wp_pures.

      (* --- open invariant *)
      wp_bind (CAS_ref _ _ _).
      iInv queueN as (t2 h2 Vt2 Vh2 xVs2 sVs2) ">(Hγ● & %Hineq & %Hlenx & %Hlens & Htoks & Hmonos & Htail & Hhead & Hstatuses & Hfree & Hfill)".
      (* --- CAS head *)
      wp_cas at (Vt2 ⊔ V) as "HVt2", Heqh | _ ; last first.
      (* (3b-a) case: t0 ≠ t2: CAS fails *)
      {
        (* --- close invariant *)
        iModIntro. iSplitR "AU Hmonos1". { repeat (iExists _). by iFrame. }
        (* --- return None *)
        iApply wp_fupd. wp_pures. iMod "AU" as (???) "[? [_ H]]". by iApply ("H" $! None).
      }
      (* (3b-b) case: t0 = t2 *)
      injection Heqh as ->.

      simpl.

      (* --- Eliminate the absurd case where the buffer is empty (t0 = h2). *)
      destruct (decide (t0 = h2)) as [Heq|Hineq2].
      {
        rewrite -Heq.
        set t0' := t0 -- capacity.
        rewrite [seqZ t0' _] seqZ_cons ; last lia.
        iDestruct "Hfree" as "[Hfreet0 _]".
        iAssert False%I with "[Hmonos1 Hmonos Hfreet0]" as "?" ; last done.
        assert (t0 `mod` capacity = t0' `mod` capacity) as <-.
        { subst t0'. by rewrite Zminus_mod Z_mod_same_full [_ -- 0] Z.sub_0_r Zmod_mod. }
        iDestruct "Hfreet0" as "[Hex | Hex ]".
        { iDestruct "Hex" as (? ? HsVs) "_".
          iDestruct (own_list_auth_both_le _ ((λ sV, StatusPair sV.1 sV.2) <$> sVs2) with "[$Hmonos1 Hmonos]") as %Hle ;
            [|by rewrite -list_fmap_compose|].
          - by erewrite list_lookup_fmap, list_lookup_Z_Some_to_nat.
          - exfalso. apply statuspair_le_Z_le in Hle. cbn in Hle. lia. }
        { iDestruct "Hex" as (?) "%HsVs".
          iDestruct (own_list_auth_both_le _ ((λ sV, StatusPair sV.1 sV.2) <$> sVs2) with "[$Hmonos1 Hmonos]") as %Hle ;
            [|by rewrite -list_fmap_compose|].
          - by erewrite list_lookup_fmap, list_lookup_Z_Some_to_nat.
          - exfalso. apply statuspair_le_Z_le in Hle. cbn in Hle. lia. }
      }
      (* --- Now we know that cell number t0 is in the full-list. *)
      assert (t0 < h2) by lia.
      rewrite [seqZ' t0 _]seqZ_cons ; last lia.
      assert (∃ xV xVs2', xVs2 = xV :: xVs2') as (xV & xVs2' & ->).
      { assert (length xVs2 > 0) by lia. destruct xVs2 ; by [exfalso|eauto]. }
      (* --- Eliminate the absurd case where cell number t0 is “being filled”. *)
      iDestruct "Hfill" as "[[Hex|Hex] Hfill]" ; last first.
      { iDestruct "Hex" as (?) "%HsVs".
        iDestruct (own_list_auth_both_le _ ((λ sV, StatusPair sV.1 sV.2) <$> sVs2) with "[$Hmonos1 Hmonos]") as %Hle ;
          [|by rewrite -list_fmap_compose|].
        - by erewrite list_lookup_fmap, list_lookup_Z_Some_to_nat.
        - exfalso. apply statuspair_le_Z_le in Hle. cbn in Hle. lia. }
      (* --- Now we know that cell number t0 is really full. *)
      iDestruct "Hex" as (V2 ?) "(HsVs2 & Helement & Hw)".
      (*rewrite (_ : h0 -- capacity + capacity = h0) ; last lia.
      rewrite (_ : (h0 -- capacity) `mod` capacity = h0 `mod` capacity) ; last first.
      { rewrite Zminus_mod Z.mod_same ; last lia.
        rewrite Z.sub_0_r Z.mod_mod// ; last lia. }*)
      iDestruct "HsVs2" as %HsVs2.
      (* --- The view V2 is in fact V1, it hasn’t changed since we read it. *)
      iAssert ⌜V2 ⊑ V1⌝%I with "[Hmonos Hmonos1]" as %HV2.
      {
        iDestruct (own_list_auth_both_le _ ((λ sV, StatusPair sV.1 sV.2) <$> sVs2) with "[$Hmonos1 Hmonos]") as %Hle ;
          [|by rewrite -list_fmap_compose|].
        - by erewrite list_lookup_fmap, list_lookup_Z_Some_to_nat.
        - cbn in Hle. destruct Hle as [? | [_ ?]] ; [exfalso ; lia | done].
      }
      rewrite [in _ V2] HV2.
      (* --- We “commit” the atomic Hoare triple. *)
      iMod "AU" as (Vt3 Vh3 xVs3) "[Hγ◯ [_ Hclose]]".
      (* --- Unify Vt3 with Vt2, Vh3 with Vh2, xVs3 with xVs2. *)
      iDestruct (own_valid_2 with "Hγ● Hγ◯") as %[= <- <- <-]%excl_auth_agree_L.
      (* --- Update the public state *)
      iMod (own_update_2 with "Hγ● Hγ◯") as "[Hγ● Hγ◯]" ; first apply excl_auth_update.
      (* --- Forge a token_read from the token_write. *)
      iMod (own_token_list_update_to_read with "Htoks Hw") as (xVs2'' [=<-]) "[Htoks Hr]" ;
        try lia.

      iMod ("Hclose" $! (Some xV) with "[Hγ◯]") as "HΦ".
      { iExists _. iFrame "#∗". iSplit ; [done | solve_monPred_in]. }

      (* --- close invariant *)
      iModIntro. iSplitR "Hmonos1 HΦ Hr Helement".
      {
        iModIntro. iNext. repeat (iExists _).
        rewrite (_ : Z.succ t0 = t0+1) ; last lia.
        rewrite (_ : Z.pred (h2 -- t0) = h2 -- (t0+1)) ; last lia.
        iFrame "Hγ● Htoks Hmonos Htail Hhead Hstatuses Hfill".
        cbn in Hlenx.
        repeat (iSplitL "" ; first (iPureIntro ; eauto with lia)).
        rewrite (_ : t0+1 - (h2 -- capacity) = (t0 - (h2 -- capacity)) + 1) ; last lia.
        rewrite seqZ_app ; try lia.
        iApply (big_sepL_app with "[$Hfree]").
        rewrite (_ : h2 -- capacity + (t0 -- (h2 -- capacity)) = t0) ; last lia.
        rewrite (eq_refl : seqZ t0 1 = [t0]) /= right_id.
        iRight. auto with iFrame.
      }
      iClear "HVt2 Hmonos1". clear dependent h2 Vh2 Vt2 xVs2' sVs2 V2.

      (* (44) non-atomic read to elements.[t0 % capacity] *)

      wp_pures.
      iDestruct (monPred_in_elim with "HV1 Helement") as "Helement" ; iClear (V1) "HV1".
      wp_read.

      (* (4) non-atomic write to elements.[t0 % capacity] *)

      wp_pures.
      wp_write.
      iDestruct (monPred_in_intro with "Helement") as (Ve) "[#HVe Helement]".

      (* (5) atomic write to statuses.[t0 % capacity] *)

      (* --- open invariant *)
      wp_pures. wp_bind (Write Atomic _ _ _).
      iInv queueN as (t3 h3 Vt3 Vh3 xVs3 sVs3) ">(Hγ● & %Hineq & %Hlenx & %Hlens & Htoks & Hmonos & Htail & Hhead & Hstatuses & Hfree & Hfill)".

      (* --- perform write *)
      wp_write_block at (V ⊔ Ve) as s3 V3 HsV3 "HV3".
      { rewrite fmap_length Hlens. apply Z_mod_lt. lia. }

      (* --- close invariant *)
      iSplitR "HΦ".
      {
        rewrite -embed_fupd. iModIntro. repeat (iExists _).
        assert (0 ≤ t0 `mod` capacity). { apply Z.mod_pos. lia. }
        iDestruct (own_token_list_read with "Htoks Hr") as "%Ht0" ; [lia .. |].

        (* frame Hstatuses first (so as to unify the existential list with sVs3) *)
        rewrite -(list_fmap_insert_Z _ _ _ (2*(t0+capacity), V ⊔ Ve)).
        iFrame "Hstatuses".
        (* frame trivial things *)
        rewrite insert_Z_length.
        iFrame (Hineq Hlenx Hlens) "Hγ● Htoks Htail Hhead".

        iAssert (∃ V0 : view, ⌜sVs3 !! (t0 `mod` capacity) = Some ((2*t0+1)%Z, V0)⌝)%I with "[Hr Hfree]" as (V0) "%HsVs3".
        {
          assert (seqZ' (h3 -- capacity) t3 !! ⌊t0 -- (h3--capacity)⌋ = Some t0) as HseqZ.
          { apply lookup_seqZ. lia. }
          iDestruct (big_sepL_lookup _ _ _ _ HseqZ with "Hfree") as "[Hfreei|?]" ;
            last done.
          iDestruct "Hfreei" as (??) "(_ & _ & Hr')".
          iCombine "Hr Hr'" as "Hexcl". rewrite list_singletonM_op.
          iDestruct (own_valid with "Hexcl")
            as %[]%auth_frag_valid%list_singletonM_valid.
        }

        iSplitL "Hmonos" ; last (iSplitR "Hfill" ; last first).
        {
          (* 1st goal: Hmonos with updated sVs3 *)
          set f := (λ sV : Z * view, ● to_latT (Some $ StatusPair sV.1 sV.2)).
          iMod (own_update with "Hmonos") as "$" ; last done.
          rewrite list_fmap_insert_Z. simpl.
          apply list_lookup_Z_Some_to_nat in HsVs3.
          rewrite -(take_drop_middle sVs3 ⌊t0 `mod` capacity⌋ (2*t0+1, V0))//.
          rewrite fmap_app list_insert_Z_to_nat// insert_app_r_alt ; last first.
          { rewrite fmap_length take_length. lia. }
          rewrite [x in <[x := _]>](_ : _ = 0%nat) ; last first.
          { rewrite fmap_length take_length min_l ?Hlens ; first lia.
            pose proof (Z.mod_pos_bound t0 (Z.of_nat capacity)). lia. }
          eapply list_middle_update, auth_update_auth, latT_local_unit_update.
          simpl. left. lia.
        }
        {
          (* 2nd goal: Hfill *)
          iModIntro. iNext.
          iApply (big_sepL2_mono with "Hfill").
          intros k _ xVk [-> Hk]%lookup_seqZ HxVk.
          rewrite /= list_lookup_Z_insert_Z_ne ; first done.
          clear -Hineq Ht0 Hk. set t3k := t3 + k. intros Heq.
          assert ((t3k -- t0) `mod` capacity = t3k -- t0) as Heq'.
          { apply Zmod_small. lia. }
          rewrite Zminus_mod Heq Zminus_diag Zmod_0_l in Heq'. lia.
        }
        {
          (* 3rd goal: Hfree *)
          iModIntro. iNext.
          clear dependent xVs3.
          rewrite -(take_drop_middle (seqZ' (h3--capacity) t3) ⌊t0--(h3--capacity)⌋ t0) ; last first.
          { apply lookup_seqZ. lia. }
          iDestruct (big_sepL_app with "Hfree") as "(Hfree1 & Hfreei & Hfree2)".
          iApply big_sepL_app ; iSplitL "Hfree1".
          {
            iApply (big_sepL_mono with "Hfree1").
            iIntros (k j Hj) "?".
            rewrite list_lookup_Z_insert_Z_ne//.
            destruct (decide (k < ⌊t0 -- (h3--capacity)⌋)) ; last first.
            { rewrite lookup_take_ge in Hj ; [done|lia]. }
            rewrite lookup_take in Hj ; last lia.
            apply lookup_seqZ in Hj.
            intro Hij.
            assert ((t0 -- j) `mod` capacity = 0) as Hij' by
              rewrite Zminus_mod Hij Z.sub_diag//.
            rewrite Zmod_small in Hij' ; lia.
          }
          iSplitR "Hfree2" ; last first.
          {
            iApply (big_sepL_mono with "Hfree2").
            iIntros (k j Hj) "?".
            rewrite list_lookup_Z_insert_Z_ne//.
            rewrite lookup_drop in Hj.
            apply lookup_seqZ in Hj.
            intro Hij.
            assert ((j - t0) `mod` capacity = 0) as Hij' by
              rewrite Zminus_mod Hij Z.sub_diag//.
            rewrite Zmod_small in Hij' ; lia.
          }
          rewrite list_lookup_Z_insert_Z ; last first.
          { rewrite Hlens. apply Z_mod_lt. lia. }
          iLeft.
          iDestruct "Hfreei" as "[Hfreei | Hfreei]".
          { iDestruct "Hfreei" as (??) "(_ & _ & Hr')".
            iCombine "Hr Hr'" as "Hexcl". rewrite list_singletonM_op.
            iDestruct (own_valid with "Hexcl")
              as %[]%auth_frag_valid%list_singletonM_valid. }
          simpl. iExists _, (V ⊔ Ve). by iFrame.
        }
      }
      clear dependent t3 h3 Vt3 Vh3 xVs3 sVs3.
      iModIntro.

      (* (6) return (Some xV) *)
      wp_pures. iApply "HΦ".
    Qed.

    (* ICFP21: this is the spec of “enqueue“, as presented in Figure 5 of the
       paper, along with its proof (which is a direct induction by using the
       specification of “try_enqueue“ in a modular fashion). *)
    Lemma enqueue_spec (E : coPset) q γ x V :
      E ## ↑queueN →
      ⎡queue_inv q γ⎤ -∗
      monPred_in V -∗
      <<< ∀ Vt Vh xVs, ⎡is_queue γ Vt Vh xVs⎤ >>>
          enqueue q x @ E
      <<< ⎡is_queue γ Vt (Vh ⊔ V) (xVs ++ [(x,V)])⎤ ∗ monPred_in Vh,
      RET #() >>>.
    Proof.
      iIntros (HE). iIntros "#Inv #HV" (Φ) "AU". iLöb as "IH".
      wp_lam. awp_apply (try_enqueue_spec _ _ _ _ _ HE with "[$] [$]").
      iApply (aacc_aupd with "AU") ; first done. iIntros (Vt Vh xVs) "Hq".
      iAaccIntro with "Hq" ; first by iIntros "$ !> $". iIntros ([]).
      - iIntros "HxVs". iRight. iFrame. iIntros "!> HΦ !>". by wp_pures.
      - iIntros "Hq". iLeft. iFrame. iIntros "!> AU !>". wp_pures. by iApply "IH".
    Qed.

    (* ICFP21: this is the spec of “dequeue“, as presented in Figure 5 of the
       paper, along with its proof (which is a direct induction by using the
       specification of “try_dequeue“ in a modular fashion). *)
    Lemma dequeue_spec (E : coPset) q γ V :
      E ## ↑queueN →
      ⎡queue_inv q γ⎤ -∗
      monPred_in V -∗
      <<< ∀ Vt Vh xVs, ⎡is_queue γ Vt Vh xVs⎤ >>>
          dequeue q @ E
      <<< ∃ xV xVs',
        ⌜xVs = xV :: xVs'⌝ ∗ ⎡is_queue γ (Vt ⊔ V) Vh xVs'⎤ ∗ monPred_in Vt ∗ monPred_in xV.2,
      RET
        xV.1
      >>>.
    Proof.
      iIntros (HE). iIntros "#Inv #HV" (Φ) "AU". iLöb as "IH".
      wp_lam. awp_apply (try_dequeue_spec _ _ _ _ HE with "[$] [$]").
      iApply (aacc_aupd with "AU") ; first done. iIntros (Vt Vh xVs) "Hq".
      iAaccIntro with "Hq" ; first by iIntros "$ !> $". iIntros ([xV|]).
      - iIntros "HxVs" ; iDestruct "HxVs" as (xVs' ->) "(?&?&?)". iRight.
        iExists _, _. iFrame. iSplitR ; first done. iIntros "!> HΦ !>". by wp_pures.
      - iIntros "Hq". iLeft. iFrame. iIntros "!> AU !>". wp_pures. by iApply "IH".
    Qed.
  End Spec.
End bounded_queue.
