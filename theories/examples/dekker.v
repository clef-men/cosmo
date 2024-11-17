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
    while: !at "other_flag" do
      if: !at "turn" ≠ "tid" then (
        "my_flag" <-at #false ;;
        while: !at "turn" ≠ "tid" do #() enddo ;;
        "my_flag" <-at #true
      )
      else #()
    enddo.

Definition release : val :=
  λ: "lk",
    let: ("turn", "tid", "my_flag", "other_flag") := "lk" in
    "turn" <-at (#1 - "tid") ;;
    "my_flag" <-at #false.



(*
 * Specification.
 *)



Inductive dekker_state : Type := Outside | Waiting | InCriticalSection.
#[local] Instance dekker_state_inhabited : Inhabited dekker_state := populate Outside.
#[local] Instance dekker_state_eq_dec : EqDecision dekker_state.
Proof. intros [][] ; first [ by right | by left ]. Qed.
Canonical dekker_stateO := leibnizO dekker_state.

Class dekkerG Σ := {
  #[local] dekker_state_inG :: inG Σ (authUR (optionUR (exclR dekker_stateO))) ;
  #[local] dekker_view_inG :: inG Σ (authUR (optionUR (exclR viewO))) ;
}.

Record dekker_gnames := Dekker_gnames {
  dekker_state_gname : gname ;
  dekker_view_gname : gname ;
}.

Section proof.
  Context `{!cosmoG Σ, !dekkerG Σ} (N : namespace).

  Definition dekker_inv_threadlocal
    (flag : location) (γ : dekker_gnames) (f : bool) (s : dekker_state) (V : view)
  : iProp Σ
  :=
    ( flag ↦at( #f, V )
    ∗ own γ.(dekker_state_gname) (● (Excl' s))
    ∗ own γ.(dekker_view_gname) (● (Excl' V))
    ∗ ⌜(s = Outside) ∨ (f = true)⌝
    )%I.

  Definition dekker_inv
    (turn flag0 flag1 : location) (γ0 γ1 : dekker_gnames) (R : vProp Σ)
  : iProp Σ
  :=
    (∃ (t : Z) (f0 f1 : bool) (s0 s1 : dekker_state) (V0 V1 : view),
        turn ↦at #t
      ∗ dekker_inv_threadlocal flag0 γ0 f0 s0 V0
      ∗ dekker_inv_threadlocal flag1 γ1 f1 s1 V1
      ∗ (⌜s0 ≠ InCriticalSection ∧ s1 ≠ InCriticalSection⌝ -∗ R (V0 ⊔ V1))
    )%I.

  Definition is_dekker (lk : val) (γ0 : dekker_gnames) (R : vProp Σ) : vProp Σ :=
    (∃ (tid : Z) (turn flag0 flag1 : location) (γ1 : dekker_gnames) (V0 : view),
        ⌜lk = (#turn, #tid, #flag0, #flag1)%V⌝
      ∗ ⎡ inv N (dekker_inv turn flag0 flag1 γ0 γ1 R) ⎤
      ∗ ⎡ own γ0.(dekker_state_gname) (◯ (Excl' Outside)) ⎤
      ∗ ⎡ own γ0.(dekker_view_gname) (◯ (Excl' V0)) ⎤
      ∗ monPred_in V0
    )%I.



(*
 * Proofs.
 *)



  Lemma dekker_inv_swap (turn flag0 flag1 : location) (γ0 γ1 : dekker_gnames) (R : vProp Σ) :
    dekker_inv turn flag0 flag1 γ0 γ1 R -∗ dekker_inv turn flag1 flag0 γ1 γ0 R.
  Proof.
    iIntros "I". iDestruct "I" as (???????) "(?&?&?&?)".
    rewrite Logic.and_comm (comm join) /dekker_inv. auto 10 with iFrame.
  Qed.

  Lemma dekker_inv_swap_equiv (turn flag0 flag1 : location) (γ0 γ1 : dekker_gnames) (R : vProp Σ) :
    dekker_inv turn flag0 flag1 γ0 γ1 R ⊣⊢ dekker_inv turn flag1 flag0 γ1 γ0 R.
  Proof. iSplit ; iApply dekker_inv_swap. Qed.

  Lemma make_spec (R : vProp Σ) :
    {{{ R }}}
      make #()
    {{{ lk0 lk1 γ0 γ1 , RET (lk0, lk1) ;
        is_dekker lk0 γ0 R ∗ is_dekker lk1 γ1 R }}}.
  Proof.
    iIntros (Φ) "HR Post".
    (* unpack R *)
    iDestruct (monPred_in_intro with "HR") as (V) "[ #? ? ]".
    (* allocate locations *)
    wp_lam.
    wp_ref turn.
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
    set γ0 := Dekker_gnames γ0s γ0V.
    set γ1 := Dekker_gnames γ1s γ1V.
    (* create invariant *)
    iMod (inv_alloc _ _ (dekker_inv turn flag0 flag1 γ0 γ1 R)
          with "[- Hγ0s◯ Hγ1s◯ Hγ0V◯ Hγ1V◯ Post]")  as "#I".
    { rewrite /dekker_inv /dekker_inv_threadlocal. repeat (iExists _). iFrame. by auto. }
    wp_pures.
    iApply "Post".
    (* create the two representation predicates *)
    iSplitL "Hγ0s◯ Hγ0V◯" ;
      last (rewrite dekker_inv_swap_equiv) ;
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

  Lemma write_turn
    (turn flag0 flag1 : location) (γ0 γ1 : dekker_gnames) (z : Z) (R : vProp Σ) :
    {{{ ⎡ inv N (dekker_inv turn flag0 flag1 γ0 γ1 R) ⎤ }}}
      #turn <-at #z
    {{{ RET #() ; True }}}.
  Proof.
    iIntros (Φ) "#? Post".
    (* open invariant *)
    iInv N as (???????) "(Hturn & ?)".
    (* perform atomic operation *)
    wp_write at ∅.
    (* close invariant *)
    iModIntro. iSplitR "Post". { repeat (iExists _). by iFrame. }
    (* conclude *)
    by iApply "Post".
  Qed.

  Lemma read_turn
    (turn flag0 flag1 : location) (γ0 γ1 : dekker_gnames) (R : vProp Σ) :
    {{{ ⎡ inv N (dekker_inv turn flag0 flag1 γ0 γ1 R) ⎤ }}}
      !at #turn
    {{{ (t : Z), RET #t ; True }}}.
  Proof.
    iIntros (Φ) "#? Post".
    (* open invariant *)
    iInv N as (t??????) "(Hturn & ?)".
    (* perform atomic operation *)
    wp_read as "_".
    (* close invariant *)
    iModIntro. iSplitR "Post". { repeat (iExists _). by iFrame. }
    (* conclude *)
    by iApply "Post".
  Qed.

  Lemma write_my_flag_false_cs
    (turn flag0 flag1 : location) (γ0 γ1 : dekker_gnames) (V0 V0' : view) (R : vProp Σ) :
    {{{
        ⎡ inv N (dekker_inv turn flag0 flag1 γ0 γ1 R) ⎤
      ∗ monPred_in V0'
      ∗ ⎡ own (dekker_state_gname γ0) (◯ Excl' InCriticalSection) ⎤
      ∗ ⎡ own (dekker_view_gname γ0) (◯ Excl' V0) ⎤
      ∗ ⎡ R V0' ⎤
    }}}
      #flag0 <-at #false
    {{{ RET #() ;
        ⎡ own (dekker_state_gname γ0) (◯ Excl' Outside) ⎤
      ∗ ⎡ own (dekker_view_gname γ0) (◯ Excl' V0') ⎤
    }}}.
  Proof.
    iIntros (Φ) "(#? & #? & Hs0◯ & HV0◯ & HR) Post".
    (* open invariant *)
    iInv N as (???????) "(Hturn & >(Hflag0 & Hs0● & HV0● & _) & Hthread1 & _)".
    (* unify the thread’s and invariant’s knowledge of the ghost state *)
    auth_unify "Hs0●" "Hs0◯".
    auth_unify "HV0●" "HV0◯".
    (* update the ghost state *)
    auth_update "Hs0●" "Hs0◯" Outside.
    auth_update "HV0●" "HV0◯" V0'.
    (* perform atomic operation *)
    wp_write at V0'.
    (* close invariant *)
    iModIntro. iSplitR "Hs0◯ HV0◯ Post". { repeat (iExists _). iFrame. by auto. }
    (* conclude *)
    iApply "Post". by iFrame.
  Qed.

  Lemma write_my_flag_false_waiting
    (turn flag0 flag1 : location) (γ0 γ1 : dekker_gnames) (V0 : view) (R : vProp Σ) :
    {{{
        ⎡ inv N (dekker_inv turn flag0 flag1 γ0 γ1 R) ⎤
      ∗ monPred_in V0
      ∗ ⎡ own (dekker_state_gname γ0) (◯ Excl' Waiting) ⎤
      ∗ ⎡ own (dekker_view_gname γ0) (◯ Excl' V0) ⎤
    }}}
      #flag0 <-at #false
    {{{ RET #() ;
        ⎡ own (dekker_state_gname γ0) (◯ Excl' Outside) ⎤
      ∗ ⎡ own (dekker_view_gname γ0) (◯ Excl' V0) ⎤
    }}}.
  Proof.
    iIntros (Φ) "(#? & #? & Hs0◯ & HV0◯) Post".
    (* open invariant *)
    iInv N as (???????) "(Hturn & >(Hflag0 & Hs0● & HV0● & _) & Hthread1 & HR)".
    (* unify the thread’s and invariant’s knowledge of the ghost state *)
    auth_unify "Hs0●" "Hs0◯".
    auth_unify "HV0●" "HV0◯".
    (* update the ghost state *)
    auth_update "Hs0●" "Hs0◯" Outside.
    (* perform atomic operation *)
    wp_write at V0.
    (* close invariant *)
    iModIntro. iSplitR "Hs0◯ HV0◯ Post".
    {
      repeat (iExists _). iFrame. iSplit ; auto.
      iIntros ([_?]). by iApply "HR".
    }
    (* conclude *)
    iApply "Post". by iFrame.
  Qed.

  Lemma write_my_flag_true
    (turn flag0 flag1 : location) (γ0 γ1 : dekker_gnames) (V0 : view) (R : vProp Σ) :
    {{{
        ⎡ inv N (dekker_inv turn flag0 flag1 γ0 γ1 R) ⎤
      ∗ monPred_in V0
      ∗ ⎡ own (dekker_state_gname γ0) (◯ Excl' Outside) ⎤
      ∗ ⎡ own (dekker_view_gname γ0) (◯ Excl' V0) ⎤
    }}}
      #flag0 <-at #true
    {{{ RET #() ;
        ⎡ own (dekker_state_gname γ0) (◯ Excl' Waiting) ⎤
      ∗ ⎡ own (dekker_view_gname γ0) (◯ Excl' V0) ⎤
    }}}.
  Proof.
    iIntros (Φ) "(#? & #? & Hs0◯ & HV0◯) Post".
    (* open invariant *)
    iInv N as (???????) "(Hturn & >(Hflag0 & Hs0● & HV0● & _) & Hthread1 & HR)".
    (* unify the thread’s and invariant’s knowledge of the ghost state *)
    auth_unify "Hs0●" "Hs0◯".
    auth_unify "HV0●" "HV0◯".
    (* update the ghost state *)
    auth_update "Hs0●" "Hs0◯" Waiting.
    (* perform atomic operation *)
    wp_write at V0.
    (* close invariant *)
    iModIntro. iSplitR "Hs0◯ HV0◯ Post".
    {
      repeat (iExists _). iFrame. iSplit ; auto.
      iIntros ([_?]). by iApply "HR".
    }
    (* conclude *)
    iApply "Post". by iFrame.
  Qed.

  Lemma read_other_flag
    (turn flag0 flag1 : location) (γ0 γ1 : dekker_gnames) (V0 : view) (R : vProp Σ) :
    {{{
        ⎡ inv N (dekker_inv turn flag0 flag1 γ0 γ1 R) ⎤
      ∗ ⎡ own (dekker_state_gname γ0) (◯ Excl' Waiting) ⎤
      ∗ ⎡ own (dekker_view_gname γ0) (◯ Excl' V0) ⎤
    }}}
      !at #flag1
    {{{ (f1 : bool), RET #f1 ;
        ⎡ own (dekker_view_gname γ0) (◯ Excl' V0) ⎤
      ∗ (if f1 then
          ⎡ own (dekker_state_gname γ0) (◯ Excl' Waiting) ⎤
        else
            ⎡ own (dekker_state_gname γ0) (◯ Excl' InCriticalSection) ⎤
          ∗ ∃ (V1 : view),  monPred_in V1 ∗ ⎡ R (V0 ⊔ V1) ⎤
        )
    }}}.
  Proof.
    iIntros (Φ) "(#? & Hs0◯ & HV0◯) Post".
    (* open invariant *)
    iInv N as
      (t f0 f1 s0 s1 V0' V1)
        "(Hturn & >(Hflag0 & Hs0● & HV0● & #Himpl0)
                & >(Hflag1 & Hs1● & HV1● & #Himpl1) & HR)" ;
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
      iModIntro. iSplitR "Hs0◯ HV0◯ Post". { repeat (iExists _). iFrame. by auto. }
      (* conclude *)
      iApply "Post". by iFrame.
    }
    (* if other_flag = false: get resource R and enter critical section *)
    {
      (* deduce that s1 = Outside *)
      assert (s1 = Outside) as -> by (by destruct Himpl1).
      (* update the ghost state *)
      auth_update "Hs0●" "Hs0◯" InCriticalSection.
      (* perform atomic operation *)
      wp_read.
      (* close invariant *)
      iModIntro. iSplitR "Hs0◯ HV0◯ HR Post".
      { repeat (iExists _). iFrame. (repeat iSplit) ; auto. by iIntros ([]). }
      (* conclude *)
      iApply "Post". iFrame. (* get R: *) iExists V1. iFrame "#". by iApply "HR".
    }
  Qed.

  Lemma release_spec_internal
    (lk : val) (tid : Z) (turn flag0 flag1 : location) (γ0 γ1 : dekker_gnames)
    (V0 : view) (R : vProp Σ) :
    lk = (#turn, #tid, #flag0, #flag1)%V →
    ⎡ inv N (dekker_inv turn flag0 flag1 γ0 γ1 R) ⎤ -∗
    ⎡ own γ0.(dekker_state_gname) (◯ (Excl' InCriticalSection)) ⎤ -∗
    ⎡ own γ0.(dekker_view_gname) (◯ (Excl' V0)) ⎤ -∗
    ∀ Φ, R -∗ (is_dekker lk γ0 R -∗ Φ #()) -∗ WP release lk {{ Φ }}.
  Proof.
    iIntros (->) "#? Hs0◯ HV0◯".
    iIntros (Φ) "HR Post".
    wp_lam. wp_pures.
    (* (1) write to turn *)
    wp_apply (write_turn with "[$]") ; iIntros "_".
    wp_pures.
    (* unpack R *)
    iDestruct (monPred_in_intro with "HR") as (V0') "[#? HR]".
    (* (2) write false to my_flag *)
    wp_apply (write_my_flag_false_cs with "[$]") ; iIntros "(Hs0◯ & HV0◯)".
    (* conclude *)
    iApply "Post". repeat (iExists _). by iFrame "# ∗".
  Qed.

  Lemma acquire_spec (lk : val) (γ0 : dekker_gnames) (R : vProp Σ) :
    {{{ is_dekker lk γ0 R }}}
      acquire lk
    {{{ RET #() ;
      R ∗ ∀ Φ, R -∗ (is_dekker lk γ0 R -∗ Φ #()) -∗ WP release lk {{ Φ }}
    }}}.
  Proof.
    iIntros (Φ) "Hlk Post".
    iDestruct "Hlk" as (tid turn flag0 flag1 γ1 V0) "(-> & #? & Hs0◯ & HV0◯ & #?)".
    wp_lam. wp_pures.
    (* (1) write true to my_flag *)
    wp_apply (write_my_flag_true with "[$]") ; iIntros "(Hs0◯ & HV0◯)".
    wp_seq. wp_closure.
    (* start the outer loop *)
    iLöb as "IH_outer_loop".
    wp_pures.
    (* (2) read from other_flag *)
    wp_apply (read_other_flag with "[$]") ; iIntros ([]) "(HV0◯ & Hread)" ;
      [ iRename "Hread" into "Hs0◯" | iDestruct "Hread" as "(Hs0◯ & HR)" ].
    (* case of (2): if other_flag = true: *)
    {
      wp_if.
      (* (3) read from turn *)
      wp_apply (read_turn with "[$]") ; iIntros (t) "_".
      wp_pures.
      (* case analysis on whether turn = tid *)
      destruct (bool_decide (t = tid)) ; clear t.
      (* case of (3): if turn = tid: skip the if block and loop again *)
      { wp_if. wp_seq. by iApply ("IH_outer_loop" with "[$] [$] [$]"). }
      (* case of (3): if turn ≠ tid: proceed to the if block *)
      {
        wp_pures.
        (* (4) write false to my_flag *)
        wp_apply (write_my_flag_false_waiting with "[$]") ; iIntros "(Hs0◯ & HV0◯)".
        wp_seq. wp_closure.
        (* start the inner loop *)
        iLöb as "IH_inner_loop".
        wp_pures.
        (* (5) read from turn *)
        wp_apply (read_turn with "[$]") ; iIntros (t) "_".
        wp_pures.
        (* case analysis on whether turn = tid *)
        destruct (bool_decide (t = tid)) ; last first.
        (* case of (5): if turn ≠ tid: run the inner loop again *)
        { wp_if. wp_seq. by iApply ("IH_inner_loop" with "[$] [$] [$]"). }
        (* case of (5): if turn = tid: stop the inner loop *)
        {
          iClear "IH_inner_loop".
          wp_pures.
          (* (6) write true to my_flag *)
          wp_apply (write_my_flag_true with "[$]") ; iIntros "(Hs0◯ & HV0◯)".
          wp_seq.
          (* run the outer loop again *)
          by iApply ("IH_outer_loop" with "[$] [$] [$]").
        }
      }
    }
    (* case of (2): if other_flag = false: get resource R and enter critical section *)
    {
      iClear "IH_outer_loop".
      wp_pures. iApply "Post". iSplitL "HR".
      (* pack R *)
      {
        iDestruct "HR" as (V1) "[#? ?]".
        iApply monPred_in_elim ; last done.
        solve_monPred_in.
      }
      (* prove spec of release *)
      by iApply (release_spec_internal with "[$] [$] [$]").
    }
  Qed.
End proof.
