From iris.algebra Require Import
  excl
  auth.
From iris.base_logic Require Import
  invariants.

From cosmo Require Import
  prelude.
From cosmo.language Require Export
  proofmode.

Set Default Proof Using "Type".

Open Scope Z.



(*
 * Implementation.
 *)



Definition make : val :=
  λ: <>,
    let: "turn" := ref_at #0 in
    let: "flag0" := ref_at #false in
    let: "flag1" := ref_at #false in
    (("turn", #0, "flag0", "flag1"), ("turn", #1, "flag1", "flag0")).

Definition acquire: val :=
  λ: "lk",
    let: ("turn", "tid", "my_flag", "other_flag") := "lk" in
    "my_flag" <-at #true ;;
    "turn" <-at (#1 - "tid") ;;
    while: (!at "other_flag") && (!at "turn" = (#1 - "tid")) do
      #()
    enddo.

Definition release : val :=
  λ: "lk",
    let: ("turn", "tid", "my_flag", "other_flag") := "lk" in
    "my_flag" <-at #false.



(*
 * Specification.
 *)



Inductive peterson_state : Type := Outside | Entered | Waiting | InCriticalSection.
#[local] Instance peterson_state_inhabited : Inhabited peterson_state := populate Outside.
#[local] Instance peterson_state_eq_dec : EqDecision peterson_state.
Proof. intros [][] ; first [ by right | by left ]. Qed.
Canonical peterson_stateO := leibnizO peterson_state.

Class PetersonG Σ := {
  #[local] peterson_state_inG :: inG Σ (authUR (optionUR (exclR peterson_stateO))) ;
  #[local] peterson_view_inG :: inG Σ (authUR (optionUR (exclR viewO))) ;
}.

(*
   ICFP20: This is the pair of ghost variables associated to each thread of
   Peterson’s algorithm.
     - peterson_state_gname is called γ in the paper;
     - peterson_view_gname is called ω in the paper.
 *)

Record peterson_gnames := Peterson_gnames {
  peterson_state_gname : gname ;
  peterson_view_gname : gname ;
}.

Section proof.
  Context `{!cosmoG Σ, !PetersonG Σ} (N : namespace).

  (*
     ICFP20: “peterson_inv” is the assertion “PetersonInv” from the paper in
     Figure 18 “Internal invariant of Peterson’s algorithm”.
  *)

  Definition peterson_inv_threadlocal
    (flag : location) (γ : peterson_gnames) (f : bool) (s : peterson_state) (V : view)
  : iProp Σ
  :=
    ( flag ↦at( #f, V )
    ∗ own γ.(peterson_state_gname) (● (Excl' s))
    ∗ own γ.(peterson_view_gname) (● (Excl' V))
    ∗ ⌜(s = Outside) ∨ (f = true)⌝
    )%I.

  Definition peterson_inv
    (tid : Z) (turn flag0 flag1 : location) (γ0 γ1 : peterson_gnames) (R : vProp Σ)
  : iProp Σ
  :=
    (∃ (t : Z) (f0 f1 : bool) (s0 s1 : peterson_state) (V0 V1 Vt : view),
        ⌜0 ≤ tid ≤ 1⌝
      ∗ ⌜0 ≤  t  ≤ 1⌝
      ∗ turn ↦at( #t, Vt )
      ∗ peterson_inv_threadlocal flag0 γ0 f0 s0 V0
      ∗ peterson_inv_threadlocal flag1 γ1 f1 s1 V1
      ∗ ⌜if decide (t = tid) then
          s0 = Waiting → s1 = Waiting ∧ Vt = V1
        else
          s1 = Waiting → s0 = Waiting ∧ Vt = V0
        ⌝
      ∗ (⌜s0 ≠ InCriticalSection ∧ s1 ≠ InCriticalSection⌝ -∗ R (V0 ⊔ V1))
    )%I.

  (* ICFP20: “is_peterson” corresponds to the assertion “canLock” of the paper. *)

  Definition is_peterson (lk : val) (γ0 : peterson_gnames) (R : vProp Σ) : vProp Σ :=
    (∃ (tid : Z) (turn flag0 flag1 : location) (γ1 : peterson_gnames) (V0 : view),
        ⌜lk = (#turn, #tid, #flag0, #flag1)%V⌝
      ∗ ⎡ inv N (peterson_inv tid turn flag0 flag1 γ0 γ1 R) ⎤
      ∗ ⎡ own γ0.(peterson_state_gname) (◯ (Excl' Outside)) ⎤
      ∗ ⎡ own γ0.(peterson_view_gname) (◯ (Excl' V0)) ⎤
      ∗ monPred_in V0
    )%I.

  (* ICFP20: “locked” corresponds to the assertion “locked” of the paper. *)

  Definition locked (lk : val) (γ0 : peterson_gnames) (R : vProp Σ) : vProp Σ :=
    (∃ (tid : Z) (turn flag0 flag1 : location) (γ1 : peterson_gnames) (V0 : view),
        ⌜lk = (#turn, #tid, #flag0, #flag1)%V⌝
      ∗ ⎡ inv N (peterson_inv tid turn flag0 flag1 γ0 γ1 R) ⎤
      ∗ ⎡ own γ0.(peterson_state_gname) (◯ (Excl' InCriticalSection)) ⎤
      ∗ ⎡ own γ0.(peterson_view_gname) (◯ (Excl' V0)) ⎤
    )%I.



(*
 * Proofs.
 *)



  Lemma int_is_bool (n : Z) :
    0 ≤ n ≤ 1  ↔  n = 0 ∨ n = 1.
  Proof. lia. Qed.

  Lemma peterson_inv_swap
    (tid tid' : Z) (turn flag0 flag1 : location) (γ0 γ1 : peterson_gnames) (R : vProp Σ) :
    tid' = 1 - tid →
    peterson_inv tid turn flag0 flag1 γ0 γ1 R -∗ peterson_inv tid' turn flag1 flag0 γ1 γ0 R.
  Proof.
    iIntros (->) "I". iDestruct "I" as
      (t f0 f1 s0 s1 V0 V1 Vt Btid%int_is_bool Bt%int_is_bool) "(?&?&?&Ht&HR)".
    iDestruct "Ht" as %Ht.
    rewrite Logic.and_comm (comm join) /peterson_inv.
    repeat (iExists _). iFrame. iPureIntro.
    case Bt ; case Btid ; intros -> -> ; by case_match.
  Qed.

  Lemma peterson_inv_swap_equiv
    (tid tid' : Z) (turn flag0 flag1 : location) (γ0 γ1 : peterson_gnames) (R : vProp Σ) :
    tid' = 1 - tid →
    peterson_inv tid turn flag0 flag1 γ0 γ1 R ⊣⊢ peterson_inv tid' turn flag1 flag0 γ1 γ0 R.
  Proof. intros ?. iSplit ; iApply peterson_inv_swap ; by lia. Qed.

  Lemma make_spec (R : vProp Σ) :
    {{{ R }}}
      make #()
    {{{ lk0 lk1 γ0 γ1 , RET (lk0, lk1) ;
        ⌜lk0 ≠ lk1⌝ ∗ is_peterson lk0 γ0 R ∗ is_peterson lk1 γ1 R }}}.
  Proof.
    iIntros (Φ) "HR Post".
    (* unpack R *)
    iDestruct (monPred_in_intro with "HR") as (V) "[ #? ? ]".
    (* allocate locations *)
    wp_lam.
    wp_ref turn at V.
    wp_ref flag0 at V.
    wp_ref flag1 at V.
    (* create ghost variables *)
    iMod (own_alloc (● (Excl' Outside) ⋅ ◯ (Excl' Outside))) as (γ0s) "[Hγ0s● Hγ0s◯]".
    { by apply auth_both_valid_discrete. }
    iMod (own_alloc (● (Excl' Outside) ⋅ ◯ (Excl' Outside))) as (γ1s) "[Hγ1s● Hγ1s◯]".
    { by apply auth_both_valid_discrete. }
    iMod (own_alloc (● (Excl' V) ⋅ ◯ (Excl' V))) as (γ0V) "[Hγ0V● Hγ0V◯]".
    { by apply auth_both_valid_discrete. }
    iMod (own_alloc (● (Excl' V) ⋅ ◯ (Excl' V))) as (γ1V) "[Hγ1V● Hγ1V◯]".
    { by apply auth_both_valid_discrete. }
    set γ0 := Peterson_gnames γ0s γ0V.
    set γ1 := Peterson_gnames γ1s γ1V.
    (* create invariant *)
    iMod (inv_alloc _ _ (peterson_inv 0 turn flag0 flag1 γ0 γ1 R)
          with "[- Hγ0s◯ Hγ1s◯ Hγ0V◯ Hγ1V◯ Post]")  as "#I".
    { rewrite /peterson_inv /peterson_inv_threadlocal.
      repeat (iExists _). iFrame. iPureIntro. repeat split ; by auto. }
    wp_pures.
    iApply "Post".
    (* create the two representation predicates *)
    iSplit ; first done.
    iSplitL "Hγ0s◯ Hγ0V◯" ;
      last (rewrite peterson_inv_swap_equiv ; last done) ;
      repeat (iExists _) ; by iFrame "# ∗".
  Qed.

  (* Take the name of two hypotheses of the form
   * [own γ (● Excl' x)] and [own γ (◯ Excl' y)], and replace y with x.  *)
  Tactic Notation "auth_unify" constr(Hauth) constr(Hfrag) :=
    let pat := constr:(Hauth +:+ " " +:+ Hfrag) in
    iDestruct (own_valid_2 with pat) as
      %[<-%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.

  (* Take the name of two hypotheses of the form
   * [own γ (● Excl' x)] and [own γ (◯ Excl' y)] and a third value z,
   * and updates γ to value z. *)
  Tactic Notation "auth_update" constr(Hauth) constr(Hfrag) constr(new_val) :=
    let pat := constr:(Hauth +:+ " " +:+ Hfrag) in
    let pat2 := constr:("[" +:+ pat +:+ "]") in
    let tmp_name := iFresh in
    iMod (own_update_2 with pat) as tmp_name ;
    [ by apply auth_update, option_local_update, (exclusive_local_update _ (Excl new_val))
    | iDestruct tmp_name as pat2 ].

  Lemma write_my_flag_false
    (tid : Z) (turn flag0 flag1 : location) (γ0 γ1 : peterson_gnames) (V0 V0' : view) (R : vProp Σ) :
    {{{
        ⎡ inv N (peterson_inv tid turn flag0 flag1 γ0 γ1 R) ⎤
      ∗ monPred_in V0'
      ∗ ⎡ own (peterson_state_gname γ0) (◯ Excl' InCriticalSection) ⎤
      ∗ ⎡ own (peterson_view_gname γ0) (◯ Excl' V0) ⎤
      ∗ ⎡ R V0' ⎤
    }}}
      #flag0 <-at #false
    {{{ RET #() ;
        ⎡ own (peterson_state_gname γ0) (◯ Excl' Outside) ⎤
      ∗ ⎡ own (peterson_view_gname γ0) (◯ Excl' V0') ⎤
    }}}.
  Proof.
    iIntros (Φ) "(#? & #? & Hs0◯ & HV0◯ & HR) Post".
    (* open invariant *)
    iInv N as
      (t f0 f1 ? s1 ? V1 Vt)
      "(>Btid & >Bt & Hturn & >(Hflag0 & Hs0● & HV0● & _) & Hthread1 & >Ht & _)" ;
      iDestruct "Btid" as %Btid ; iDestruct "Bt" as %Bt ; iDestruct "Ht" as %Ht.
    (* unify the thread’s and invariant’s knowledge of the ghost state *)
    auth_unify "Hs0●" "Hs0◯".
    auth_unify "HV0●" "HV0◯".
    (* update the ghost state *)
    auth_update "Hs0●" "Hs0◯" Outside.
    auth_update "HV0●" "HV0◯" V0'.
    (* perform atomic operation *)
    wp_write at V0'.
    (* close invariant *)
    iModIntro. iSplitR "Hs0◯ HV0◯ Post".
    {
      repeat (iExists _). iFrame. iPureIntro. repeat (split ; auto).
      case_match ; [ done | by intros [? _]%Ht ].
    }
    (* conclude *)
    iApply "Post". by iFrame.
  Qed.

  Lemma write_my_flag_true
    (tid : Z) (turn flag0 flag1 : location) (γ0 γ1 : peterson_gnames) (V0 : view) (R : vProp Σ) :
    {{{
        ⎡ inv N (peterson_inv tid turn flag0 flag1 γ0 γ1 R) ⎤
      ∗ monPred_in V0
      ∗ ⎡ own (peterson_state_gname γ0) (◯ Excl' Outside) ⎤
      ∗ ⎡ own (peterson_view_gname γ0) (◯ Excl' V0) ⎤
    }}}
      #flag0 <-at #true
    {{{ RET #() ;
        ⎡ own (peterson_state_gname γ0) (◯ Excl' Entered) ⎤
      ∗ ⎡ own (peterson_view_gname γ0) (◯ Excl' V0) ⎤
    }}}.
  Proof.
    iIntros (Φ) "(#? & #? & Hs0◯ & HV0◯) Post".
    (* open invariant *)
    iInv N as
      (t f0 f1 ? s1 ? V1 Vt)
      "(>Btid & >Bt & Hturn & >(Hflag0 & Hs0● & HV0● & _) & Hthread1 & >Ht & HR)" ;
      iDestruct "Btid" as %Btid ; iDestruct "Bt" as %Bt ; iDestruct "Ht" as %Ht.
    (* unify the thread’s and invariant’s knowledge of the ghost state *)
    auth_unify "Hs0●" "Hs0◯".
    auth_unify "HV0●" "HV0◯".
    (* update the ghost state *)
    auth_update "Hs0●" "Hs0◯" Entered.
    (* perform atomic operation *)
    wp_write at V0.
    (* close invariant *)
    iModIntro. iSplitR "Hs0◯ HV0◯ Post".
    {
      repeat (iExists _). iFrame. repeat (iSplit ; auto).
      - iPureIntro. case_match ; [ done | by intros [? _]%Ht ].
      - iIntros ([_ ?]). by iApply "HR".
    }
    (* conclude *)
    iApply "Post". by iFrame.
  Qed.

  Lemma write_turn
    (tid : Z) (turn flag0 flag1 : location) (γ0 γ1 : peterson_gnames) (V0 : view) (R : vProp Σ) :
    {{{
        ⎡ inv N (peterson_inv tid turn flag0 flag1 γ0 γ1 R) ⎤
      ∗ monPred_in V0
      ∗ ⎡ own (peterson_state_gname γ0) (◯ Excl' Entered) ⎤
      ∗ ⎡ own (peterson_view_gname γ0) (◯ Excl' V0) ⎤
    }}}
      #turn <-at #(1-tid)
    {{{ RET #() ;
        ⎡ own (peterson_state_gname γ0) (◯ Excl' Waiting) ⎤
      ∗ ⎡ own (peterson_view_gname γ0) (◯ Excl' V0) ⎤
    }}}.
  Proof.
    iIntros (Φ) "(#? & #? & Hs0◯ & HV0◯) Post".
    (* open invariant *)
    iInv N as
      (t f0 f1 ? s1 ? V1 Vt)
      "(>Btid & _ & Hturn & >(Hflag0 & Hs0● & HV0● & Himpl0) & Hthread1 & _ & HR)" ;
      iDestruct "Btid" as %Btid ; iDestruct "Himpl0" as %Himpl0.
    (* unify the thread’s and invariant’s knowledge of the ghost state *)
    auth_unify "Hs0●" "Hs0◯".
    auth_unify "HV0●" "HV0◯".
    (* deduce that f0 = true *)
    destruct Himpl0 as [? | ->] ; first congruence.
    (* update the ghost state *)
    auth_update "Hs0●" "Hs0◯" Waiting.
    (* perform atomic operation *)
    wp_write at V0.
    (* close invariant *)
    iModIntro. iSplitR "Hs0◯ HV0◯ Post".
    {
      repeat (iExists _). iFrame. repeat iSplit ; auto with lia.
      - iPureIntro. case_match ; [ lia | done ].
      - iIntros ([_ ?]). by iApply "HR".
    }
    (* conclude *)
    iApply "Post". by iFrame.
  Qed.

  Lemma read_other_flag
    (tid : Z) (turn flag0 flag1 : location) (γ0 γ1 : peterson_gnames) (V0 : view) (R : vProp Σ) :
    {{{
        ⎡ inv N (peterson_inv tid turn flag0 flag1 γ0 γ1 R) ⎤
      ∗ ⎡ own (peterson_state_gname γ0) (◯ Excl' Waiting) ⎤
      ∗ ⎡ own (peterson_view_gname γ0) (◯ Excl' V0) ⎤
    }}}
      !at #flag1
    {{{ (f1 : bool), RET #f1 ;
        ⎡ own (peterson_view_gname γ0) (◯ Excl' V0) ⎤
      ∗ (if f1 then
          ⎡ own (peterson_state_gname γ0) (◯ Excl' Waiting) ⎤
        else
            ⎡ own (peterson_state_gname γ0) (◯ Excl' InCriticalSection) ⎤
          ∗ ∃ (V1 : view),  monPred_in V1 ∗ ⎡ R (V0 ⊔ V1) ⎤
        )
    }}}.
  Proof.
    iIntros (Φ) "(#? & Hs0◯ & HV0◯) Post".
    (* open invariant *)
    iInv N as
      (t f0 f1 s0 s1 V0' V1 Vt)
      "(>Btid & >Bt & Hturn & >(Hflag0 & Hs0● & HV0● & #Himpl0)
                            & >(Hflag1 & Hs1● & HV1● & #Himpl1) & >Ht & HR)" ;
      iDestruct "Btid" as %Btid ; iDestruct "Bt" as %Bt ; iDestruct "Ht" as %Ht ;
      iDestruct "Himpl0" as %Himpl0 ; iDestruct "Himpl1" as %Himpl1.
    (* unify the thread’s and invariant’s knowledge of the ghost state *)
    auth_unify "Hs0●" "Hs0◯".
    auth_unify "HV0●" "HV0◯".
    (* deduce that f0 = true *)
    destruct Himpl0 as [? | ->] ; first congruence.
    (* case analysis on other_flag *)
    destruct f1.
    (* if other_flag = true: do nothing *)
    {
      (* perform atomic operation *)
      wp_read as "_".
      (* close invariant *)
      iModIntro. iSplitR "Hs0◯ HV0◯ Post".
      { repeat (iExists _). iFrame. repeat iSplit ; by auto with lia. }
      (* conclude *)
      iApply "Post". by iFrame.
    }
    (* if other_flag = false: get resource R and enter critical section *)
    {
      (* deduce that s1 = Outside *)
      destruct Himpl1 as [-> | ?] ; last congruence.
      (* update the ghost state *)
      auth_update "Hs0●" "Hs0◯" InCriticalSection.
      (* perform atomic operation *)
      wp_read.
      (* close invariant *)
      iModIntro. iSplitR "Hs0◯ HV0◯ HR Post".
      {
        repeat (iExists _). iFrame. repeat iSplit ; auto with lia.
        - by case_match.
        - by iIntros ([? _]).
      }
      (* conclude *)
      iApply "Post". iFrame. (* get R: *) iExists V1. iFrame "#". by iApply "HR".
    }
  Qed.

  Lemma read_turn
    (tid : Z) (turn flag0 flag1 : location) (γ0 γ1 : peterson_gnames) (V0 : view) (R : vProp Σ) :
    {{{
        ⎡ inv N (peterson_inv tid turn flag0 flag1 γ0 γ1 R) ⎤
      ∗ ⎡ own (peterson_state_gname γ0) (◯ Excl' Waiting) ⎤
      ∗ ⎡ own (peterson_view_gname γ0) (◯ Excl' V0) ⎤
    }}}
      !at #turn
    {{{ (t : Z), RET #t ;
        ⎡ own (peterson_view_gname γ0) (◯ Excl' V0) ⎤
      ∗ (
          ( ⌜t = 1-tid⌝
          ∗ ⎡ own (peterson_state_gname γ0) (◯ Excl' Waiting) ⎤
          )
        ∨ ( ⌜t = tid⌝
          ∗ ⎡ own (peterson_state_gname γ0) (◯ Excl' InCriticalSection) ⎤
          ∗ ∃ (V1 : view),  monPred_in V1 ∗ ⎡ R (V0 ⊔ V1) ⎤
          )
        )
    }}}.
  Proof.
    iIntros (Φ) "(#? & Hs0◯ & HV0◯) Post".
    (* open invariant *)
    iInv N as
      (t f0 f1 ? s1 ? V1 Vt)
      "(>Btid & >Bt & Hturn & >(Hflag0 & Hs0● & HV0● & Himpl0) & Hthread1 & >Ht & HR)" ;
      iDestruct "Btid" as %Btid%int_is_bool ;
      iDestruct "Bt" as %Bt%int_is_bool ;
      iDestruct "Ht" as %Ht ;
      iDestruct "Himpl0" as %Himpl0.
    (* unify the thread’s and invariant’s knowledge of the ghost state *)
    auth_unify "Hs0●" "Hs0◯".
    auth_unify "HV0●" "HV0◯".
    (* deduce that f0 = true *)
    destruct Himpl0 as [? | ->] ; first congruence.
    (* case analysis on turn *)
    assert (t = 1-tid ∨ t = tid) as [-> | ->] by lia.
    (* if turn = 1-tid: do nothing *)
    {
      (* perform atomic operation *)
      wp_read as "_".
      (* close invariant *)
      iModIntro. iSplitR "Hs0◯ HV0◯ Post".
      { repeat (iExists _). iFrame. repeat iSplit ; by auto with lia. }
      (* conclude *)
      iApply "Post". iFrame "HV0◯". iLeft. by iFrame.
    }
    (* if turn = tid: get resource R and enter critical section *)
    {
      (* deduce that s1 = Waiting and Vt = V1 *)
      destruct (decide _) as [_|?] ; last done.
      destruct Ht as [-> ->] ; first done.
      (* update the ghost state *)
      auth_update "Hs0●" "Hs0◯" InCriticalSection.
      (* perform atomic operation *)
      wp_read.
      (* close invariant *)
      iModIntro. iSplitR "Hs0◯ HV0◯ HR Post".
      {
        repeat (iExists _). iFrame. repeat iSplit ; auto with lia.
        - by case_match.
        - by iIntros ([? _]).
      }
      (* conclude *)
      iApply "Post". iFrame "HV0◯". iRight. iSplit ; first done.
      iFrame "Hs0◯". (* get R: *) iExists V1. iFrame "#". by iApply "HR".
    }
  Qed.

  Lemma release_spec (lk : val) (γ0 : peterson_gnames) (R : vProp Σ) :
    {{{ locked lk γ0 R ∗ R }}}
      release lk
    {{{ RET #() ; is_peterson lk γ0 R }}}.
  Proof.
    iIntros (Φ) "[Hlocked HR] Post".
    iDestruct "Hlocked" as (??????) "(-> & #? & Hs0◯ & HV0◯)".
    wp_lam. wp_pures.
    (* unpack R *)
    iDestruct (monPred_in_intro with "HR") as (V0') "[#? HR]".
    (* (1) write false to my_flag *)
    wp_apply (write_my_flag_false with "[$]") ; iIntros "(Hs0◯ & HV0◯)".
    (* conclude *)
    iApply "Post". repeat (iExists _). by iFrame "# ∗".
  Qed.

  Lemma acquire_spec (lk : val) (γ0 : peterson_gnames) (R : vProp Σ) :
    {{{ is_peterson lk γ0 R }}}
      acquire lk
    {{{ RET #() ; locked lk γ0 R ∗ R }}}.
  Proof.
    iIntros (Φ) "Hlk Post".
    iDestruct "Hlk" as (γ1 turn flag0 flag1 tid V0) "(-> & #? & Hs0◯ & HV0◯ & #?)".
    wp_lam. wp_pures.
    (* (1) write true to my_flag *)
    wp_apply (write_my_flag_true with "[$]") ; iIntros "[Hs0◯ HV0◯]".
    wp_pures.
    (* (2) write to turn *)
    wp_apply (write_turn with "[$]") ; iIntros "[Hs0◯ HV0◯]".
    wp_seq. wp_closure.
    (* start the waiting loop *)
    iLöb as "IH_loop".
    wp_pures.
    (* (3) read from other_flag *)
    wp_apply (read_other_flag with "[$]") ; iIntros ([]) "(HV0◯ & Hread)" ;
      [ iRename "Hread" into "Hs0◯" | iDestruct "Hread" as "(Hs0◯ & HR)" ].
    (* case of (3): if other_flag = true: continue the loop *)
    {
      wp_pures.
      (* (4) read from turn *)
      wp_apply (read_turn with "[$]") ; iIntros (t) "(HV0◯ & [(-> & Hs0◯) | (-> & Hs0◯ & HR)])".
      (* case of (4): if turn = 1-tid: loop again *)
      {
        wp_op. rewrite bool_decide_eq_true_2 ; last done. wp_if. wp_seq.
        by iApply ("IH_loop" with "[$] [$] [$]").
      }
      (* case of (4): if turn = tid: get resource R and enter critical section *)
      {
        iClear "IH_loop".
        wp_op. rewrite bool_decide_eq_false_2 ; last lia. wp_if.
        iApply "Post". iSplitR "HR".
        (* forge the “locked” token *)
        { repeat (iExists _). iFrame. by iSplit. }
        (* pack R *)
        {
          iDestruct "HR" as (V1) "[#? ?]".
          iApply monPred_in_elim ; last done.
          solve_monPred_in.
        }
      }
    }
    (* case of (3): if other_flag = false: get resource R and enter critical section *)
    {
      iClear "IH_loop".
      wp_pures. iApply "Post". iSplitR "HR".
      (* forge the “locked” token *)
      { repeat (iExists _). iFrame. by iSplit. }
      (* pack R *)
      {
        iDestruct "HR" as (V1) "[#? ?]".
        iApply monPred_in_elim ; last done.
        solve_monPred_in.
      }
    }
  Qed.

(*
   ICFP20: This is the statement and proof of the functional specification of
   the lock, as stated in Figure 15 “A specification of a lock that can be used
   by two threads”.
   It simply packs together the theorems from above (“make_spec”, “acquire_spec”
   and “release_spec”), so the actual work happens there.
 *)

  Theorem combined_spec P :
    {{{ P }}}
    make #()
    {{{ lk0 lk1 (unlocked locked : val → vProp Σ), RET (lk0, lk1) ;
      unlocked lk0 ∗ unlocked lk1 ∗
      ∀ lk,
        {{{ unlocked lk }}} acquire lk {{{ RET #() ; locked lk ∗ P }}}
      ∗ {{{ locked lk ∗ P }}} release lk {{{ RET #() ; unlocked lk }}}
    }}}.
  Proof using PetersonG0 N.
    iIntros (Φ) "HP Post".
    wp_apply (make_spec with "HP"). iIntros (lk0 lk1 γ0 γ1) "(% & Hunlk0 & Hunlk1)".
    (* because we cannot index things with respect to the thread’s ID (0 or 1),
       we need a bit of paperwork here… *)
    pose (unlocked' := λ (v : val),
      if decide (v = lk0) then
        is_peterson lk0 γ0 P
      else if decide (v = lk1) then
        is_peterson lk1 γ1 P
      else False%I
    : vProp Σ).
    pose (locked' := λ (v : val),
      if decide (v = lk0) then
        locked lk0 γ0 P
      else if decide (v = lk1) then
        locked lk1 γ1 P
      else False%I
    : vProp Σ).
    assert (unlocked' lk0 = is_peterson lk0 γ0 P) as Eunlocked0.
    { rewrite /unlocked'. by case_match. }
    assert (unlocked' lk1 = is_peterson lk1 γ1 P) as Eunlocked1.
    { rewrite /unlocked'. case_match ; first done. by case_match. }
    assert (locked' lk0 = locked lk0 γ0 P) as Elocked0.
    { rewrite /locked'. by case_match. }
    assert (locked' lk1 = locked lk1 γ1 P) as Elocked1.
    { rewrite /locked'. case_match ; first done. by case_match. }
    assert (∀ v, unlocked' v -∗ ∃ γ, is_peterson v γ P ∗ ⌜locked' v = locked v γ P⌝)
      as unlocked_valid.
    { iIntros (v) "H". rewrite /unlocked'.
      case_match ; last case_match ; last done ; subst ; iExists _ ; by iFrame. }
    assert (∀ v, locked' v -∗ ∃ γ, locked v γ P ∗ ⌜unlocked' v = is_peterson v γ P⌝)
      as locked_valid.
    { iIntros (v) "H". rewrite /locked'.
      case_match ; last case_match ; last done ; subst ; iExists _ ; by iFrame. }
    (* back to the proof of the program: *)
    iApply ("Post" $! lk0 lk1 unlocked' locked').
    rewrite Eunlocked0 Eunlocked1 ; iFrame. iIntros (v). iSplit.
    (* prove the triple for acquire: *)
    {
      iIntros (Ψ) "!# Hunlocked Post".
      iDestruct (unlocked_valid with "Hunlocked") as (γ) "[Hunlocked ->]".
      by wp_apply (acquire_spec with "[$]").
    }
    (* prove the triple for release: *)
    {
      iIntros (Ψ) "!# [Hlocked HP] Post".
      iDestruct (locked_valid with "Hlocked") as (γ) "[Hlocked ->]".
      by wp_apply (release_spec with "[$]").
    }
  Qed.
End proof.
