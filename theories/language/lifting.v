From iris.algebra Require Import
  gmap
  excl
  auth
  frac
  agree
  csum.
From iris.base_logic.lib Require Import
  own.
From iris.program_logic Require Import
  weakestpre
  ectx_lifting.
From iris.bi Require Import
  fractional.
From iris.proofmode Require Export
  tactics.
From iris.proofmode Require Import
  string_ident.

From cosmo Require Import
  prelude.
From cosmo.common Require Import
  list.
From cosmo.iris.base_logic Require Import
  lib.lattice.
From cosmo.language Require Import
  store
  weakestpre
  notations.

Implicit Types v : val.
Implicit Types l : lit.
Implicit Types ℓ : location.
Implicit Types i : offset.
Implicit Types e : expr.
Implicit Types efs : list expr.

Class cosmoG Σ := CosmoG {
  cosmoG_invG : invGS Σ ;
  #[global] cosmoG_storeG :: storeG Σ ;
  #[global] cosmoG_seenG :: seenG Σ ;
}.

#[global] Program Instance cosmoG_irisG `{!cosmoG Σ} : irisGS view_lang Σ := {
  iris_invGS := cosmoG_invG ;
  state_interp σ _ _ _ := (store_interp σ ∗ seen_interp σ)%I ;
  fork_post _ := True%I ;
  num_laters_per_step _ := 0%nat ;
  state_interp_mono _ _ _ _ := fupd_intro _ _ ;
}.
#[global] Opaque iris_invGS.

Class AsRecV v (f x : binder) (erec : expr) :=
  as_recv : v = RecV f x erec.
#[global] Hint Mode AsRecV ! - - - : typeclass_instances.

Definition AsRecV_recv f x e : AsRecV (RecV f x e) f x e :=
  eq_refl.
#[global] Hint Extern 0 (
  AsRecV (RecV _ _ _) _ _ _
) =>
  apply AsRecV_recv
: typeclass_instances.

Ltac inv_head_step :=
  repeat match goal with
  | _ =>
      progress (simplify_list_eq; decompose_Forall)
  | H : to_val _ = Some _ |- _ =>
      apply of_to_val in H
  | H : view_lang.head_step ?e _ _ _ _ _ |- _ =>
      try (is_var e; fail 1);
      inversion H; subst; clear H
  | H : head_step ?e _ _ _ |- _ =>
      try (is_var e; fail 1);
      inversion H; subst; clear H
  | H : mem_step _ _ _ _ _ |- _ =>
      inversion H; subst; clear H
  end.

#[local] Hint Extern 0 (
  head_reducible _ _
) =>
  unfold head_reducible; simpl; eexists _, _, _, _
: core.

#[local] Hint Extern 1 (
  view_lang.head_step _ _ _ _ _ _
) =>
  eapply view_lang.pure_step with (efs := []); simpl
: core.
#[local] Hint Extern 1 (
  view_lang.head_step _ _ _ _ _ _
) =>
  eapply view_lang.impure_step; simpl
: core.
#[local] Hint Extern 0 (
  view_lang.head_step (Fork _ at _) _ _ _ _ _
) =>
  eapply view_lang.pure_step with (efs := [(_ at _)%E]); simpl
: core.

#[local] Hint Constructors head_step : core.
#[local] Hint Constructors mem_step : core.
#[local] Hint Constructors Forall : core.

#[local] Ltac solve_exec_safe :=
  intros; subst; do 3 eexists;
  apply view_lang.pure_step with (efs := []); econstructor; eauto.
#[local] Ltac solve_exec_puredet :=
  simpl; intros; by inv_head_step.
#[local] Ltac solve_pure_exec :=
  subst; intros ??; apply nsteps_once, (pure_head_step_pure_step (Λ := view_ectx_lang));
  constructor; [solve_exec_safe | solve_exec_puredet].

Notation PureExecBase P nsteps e1 e2 :=
  (∀ V, PureExec P nsteps (e1 at V) (e2 at V)).

#[global] Instance pure_recc f x (erec : expr) :
  PureExecBase True 1 (rec: f x := erec) (rec: f x := erec)%V.
Proof.
  solve_pure_exec.
Qed.
#[global] Instance pure_pairc v1 v2 :
  PureExecBase True 1 (v1, v2) (v1, v2)%V.
Proof.
  solve_pure_exec.
Qed.
#[global] Instance pure_injlc v :
  PureExecBase True 1 (InjL v) (InjLV v).
Proof.
  solve_pure_exec.
Qed.
#[global] Instance pure_injrc v :
  PureExecBase True 1 (InjR v) (InjRV v).
Proof.
  solve_pure_exec.
Qed.

#[global] Instance pure_beta f x (erec : expr) v1 v2 `{!AsRecV v1 f x erec} :
  PureExecBase True 1 (v1 v2) (subst' x v2 (subst' f v1 erec)).
Proof.
  unfold AsRecV in *. solve_pure_exec.
Qed.

#[global] Instance pure_unop (op : un_op) l l' :
  PureExecBase (un_op_eval op l = Some l') 1 (UnOp op #l) #l'.
Proof.
  solve_pure_exec.
Qed.
#[global] Instance pure_binop (op : bin_op) l1 l2 l' :
  PureExecBase (bin_op_eval op l1 l2 = Some l') 1 (BinOp op #l1 #l2) #l'
  | 10.
Proof.
  solve_pure_exec.
Qed.

Definition lit_compare_safe l1 l2 : Prop :=
  match l1, l2 with
  | LitLoc _, LitLoc _ | LitInt _, LitInt _ | LitBool _, LitBool _
  | LitUnit, LitUnit =>
      True
  | _, _ =>
      False
  end.
#[global] Instance pure_eqop l1 l2 :
  PureExecBase (lit_compare_safe l1 l2) 1 (#l1 = #l2) #(lit_eq l1 l2)
  | 1.
Proof.
  intros V Hcompare. destruct l1, l2=>//;
  apply pure_binop=>/=; try (repeat case_bool_decide; congruence).
Qed.

#[global] Instance pure_if_true e1 e2 :
  PureExecBase True 1 (If #true e1 e2) e1.
Proof.
  solve_pure_exec.
Qed.
#[global] Instance pure_if_false e1 e2 :
  PureExecBase True 1 (If #false e1 e2) e2.
Proof.
  solve_pure_exec.
Qed.

#[global] Instance pure_fst v1 v2 :
  PureExecBase True 1 (Fst (v1, v2)%V) v1.
Proof.
  solve_pure_exec.
Qed.
#[global] Instance pure_snd v1 v2 :
  PureExecBase True 1 (Snd (v1, v2)%V) v2.
Proof.
  solve_pure_exec.
Qed.

#[global] Instance pure_case_inl v e1 e2 :
  PureExecBase True 1 (Case (InjLV v) e1 e2) (e1 v).
Proof.
  solve_pure_exec.
Qed.
#[global] Instance pure_case_inr v e1 e2 :
  PureExecBase True 1 (Case (InjRV v) e1 e2) (e2 v).
Proof.
  solve_pure_exec.
Qed.

#[global] Instance pure_exec_base_fill K φ n e1 e2 :
  PureExecBase φ n e1 e2 →
  PureExecBase φ n (fill K e1) (fill K e2).
Proof.
  intros ? V ?. rewrite !fill_base_view.
  eapply (pure_exec_fill (Λ:=view_ectx_lang))=>//.
Qed.

Section lifting_view_lang.
  Context `{!cosmoG Σ}.

  Implicit Types Φ : view_lang.val → iProp Σ.
  Implicit Types V Vℓ : view.
  Implicit Types q : Qp.

  Lemma wp_fork_view_lang E e Φ V :
    ▷ WP e at V @ ⊤ {{ _, True }} -∗
    ▷ Φ (#() at V)%V -∗
    WP Fork e at V @ E {{ Φ }}.
  Proof.
    iIntros "He HΦ". iApply (wp_lift_atomic_head_step (Fork e at V)); [done|].
    iIntros (σ1 ns κ κs n) "Hσ !>"; iSplit; first by eauto.
    iNext; iIntros (v2 σ2 [|[ef V'] []] Hstep) "H£"; inv_head_step. by iFrame.
  Qed.

  Lemma store_alloc_update σ ℓ v (n : nat) s :
    σ !! ℓ = None →
    ● store_to_cmra σ ~~>
      ● store_to_cmra (<[ℓ:=replicate n s]> σ) ⋅
      ◯ ([^op list] i ∈ seq 0 n, {[ℓ.[Z.of_nat i] := elt_to_cmra s]}).
  Proof.
    intros Hσ.
    apply auth_update_alloc. rewrite store_to_cmra_insert_block //.
    rewrite (_:([^op list] i ∈ seq 0 n, _) ≡ _).
    - apply op_local_update_discrete => Hσ1.
      rewrite -store_to_cmra_insert_block //. intros [ℓ' i'].
      rewrite lookup_store_to_cmra /lookup /store_lookup.
      destruct (decide(ℓ' = ℓ)) as [->|Hℓℓ'].
      + rewrite lookup_insert /=. case_bool_decide; last done.
        destruct (decide (n ≤ Z.to_nat i')%nat) as [Hni'|].
        * apply (lookup_replicate_None n s) in Hni'. by rewrite Hni'.
        * rewrite lookup_replicate_2; [by destruct s|lia].
      + rewrite lookup_insert_ne //. specialize (Hσ1 (ℓ'.[i'])).
          by rewrite lookup_store_to_cmra /lookup /store_lookup in Hσ1.
    - rewrite right_id. intros [ℓ' i'].
      rewrite lookup_store_to_cmra [ {[_:=_]} !! _]/lookup /store_lookup.
      destruct (decide(ℓ' = ℓ)) as [->|Hℓℓ'].
      + rewrite lookup_insert. induction n as [|n IH].
        * rewrite lookup_empty. by case_bool_decide.
        * rewrite seq_S replicate_S_end /=. etrans.
          { apply lookup_proper. rewrite big_opL_app /= right_id //. }
          rewrite lookup_op IH.
          destruct (decide (i' = n)) as [->|Hi'n].
          -- rewrite lookup_app_r replicate_length Nat2Z.id // Nat.sub_diag /=
                     lookup_insert.
             destruct (lookup_replicate_None n s n) as [EQ _]. rewrite EQ //.
             case_bool_decide ; [done | lia].
          -- rewrite lookup_singleton_ne; last congruence.
             rewrite right_id /=. case_bool_decide; last done.
             destruct (decide (i' > n)).
             ++ rewrite !lookup_ge_None_2 // ?app_length
                        replicate_length /=; lia.
             ++ rewrite lookup_app_l // replicate_length. lia.
      + rewrite (big_opL_commute (o1:=op) (o2:=op) (lookup _))
                lookup_singleton_ne //= (big_opL_proper _ (λ _ _, None)).
        { case_bool_decide ; by rewrite big_opL_unit //. }
        intros. rewrite lookup_singleton_ne //. congruence.
  Qed.

  Lemma lenstore_alloc_update σ ℓ v (n : Z) s :
    σ !! ℓ = None →
    (0 ≤ n)%Z →
    ● store_to_lenstore_cmra σ ~~>
      ● store_to_lenstore_cmra (<[ℓ:=replicate (Z.to_nat n) s]> σ) ⋅
      ◯ {[ℓ := to_agree n]}.
  Proof.
    intros Hσ Hn.
    rewrite /store_to_lenstore_cmra fmap_insert replicate_length Z2Nat.id//.
    apply auth_update_alloc, alloc_singleton_local_update=>//.
    rewrite lookup_fmap. by destruct lookup.
  Qed.

  Lemma wp_alloc_na_view_lang E (n : Z) v Φ V :
    (0 ≤ n)%Z →
    ▷ (∀ ℓ, hist_na_block ℓ (replicate (Z.to_nat n) {[ None := v ]}) 1 -∗ Φ (#ℓ at V)%V) -∗
    WP Alloc NonAtomic #n v at V @ E {{ Φ }}.
  Proof.
    iIntros (Hn) "HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Alloc NonAtomic #n v at V)); auto.
    iIntros (σ1 ? κ κs k) "[Hσst Hσse] !>"; iSplit.
    - assert (FRESH := is_fresh (dom σ1)).
      apply (not_elem_of_dom (A := list store_elt)) in FRESH. by eauto 10.
    - iNext; iIntros (e2 σ2 efs Hstep) "_"; inv_head_step. iSplitR=>//.
      iDestruct "Hσst" as "[Hσst Hσlen]". rewrite /store_interp.
      (* update the value store with the new block *)
      iMod (own_update with "Hσst") as "[$ Hhist]".
      { by apply store_alloc_update. }
      (* update the length store with the length of the new block *)
      iMod (own_update with "Hσlen") as "[$ Hlen]".
      { by apply lenstore_alloc_update. }
      (* establish the new resource mapsto_na_view_block *)
      rewrite hist_na_block_eq. iDestruct ("HΦ" $! ℓ with "[Hhist Hlen]") as "$".
      { rewrite /hist_na_block_def replicate_length has_length_eq.
        rewrite Z2Nat.id ; last done. iFrame.
        iInduction (Z.to_nat n) as [ | n' ] "IH".
        - done.
        - rewrite seq_S replicate_S_end 2!big_opL_app /=.
          iDestruct "Hhist" as "(Hhist' & ? & _)".
          iSplitL "Hhist'" ; [|iSplit ; last done].
          + by iApply "IH".
          + by rewrite replicate_length Nat.add_0_r hist_na_eq. }
      iDestruct "Hσse" as (Vseen) "[HVseen Hseen]".
      iDestruct "Hseen" as %(Hseen_at & Hseen_na & Hseen_none).
      iExists Vseen. iFrame. iPureIntro. split ; last split.
      + intros [ℓ' i'] v' Vℓ' Hℓ'. destruct (decide (ℓ = ℓ')) as [<-|].
        * rewrite store_lookup_eq lookup_insert /= in Hℓ'.
          case_bool_decide; last done.
          apply lookup_replicate in Hℓ' as [Hℓ' _]. congruence.
        * rewrite store_lookup_eq lookup_insert_ne // -store_lookup_eq in Hℓ'. eauto.
      + intros [ℓ' i'] h Hℓ'. destruct (decide (ℓ = ℓ')) as [<-|].
        * rewrite store_lookup_eq lookup_insert /= in Hℓ'.
          case_bool_decide; last done.
          apply lookup_replicate in Hℓ' as [Hℓ' _]. inversion Hℓ'; subst; clear Hℓ'.
          rewrite Hseen_none.
          -- rewrite (lookup_singleton (M := gmap _)). eauto.
          -- rewrite store_lookup_eq (_ : σ1 !! ℓ = None) ; last done.
             case_bool_decide; done.
        * rewrite store_lookup_eq lookup_insert_ne // -store_lookup_eq in Hℓ'. auto.
      + intros [ℓ' i'] Hℓ'. destruct (decide (ℓ = ℓ')) as [<-|].
        * rewrite Hseen_none // store_lookup_eq (_ : σ1 !! ℓ = None); last done.
          case_bool_decide; done.
        * rewrite store_lookup_eq lookup_insert_ne // -store_lookup_eq in Hℓ'. auto.
  Qed.

  Lemma wp_alloc_at_view_lang E (n : Z) v V :
    (0 ≤ n)%Z →
    {{{
      seen V
    }}}
      Alloc Atomic #n v at V @ E
    {{{ ℓ,
      RET #ℓ at V;
      mapsto_at_view_block ℓ (replicate (Z.to_nat n) (v, V)) 1%Qp
    }}}.
  Proof.
    iIntros (Hn Φ) "Hseen HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Alloc Atomic #n v at V)); auto.
    iIntros (σ1 ? κ κs k) "[Hσst Hσse] !>"; iSplit.
    - assert (FRESH := is_fresh (dom σ1)).
      apply (not_elem_of_dom (A := list store_elt)) in FRESH. by eauto 10.
    - iNext; iIntros (e2 σ2 efs Hstep) "_"; inv_head_step. iSplitR=>//.
      iDestruct "Hσst" as "[Hσst Hσlen]". rewrite /store_interp.
      (* update the value store with the new block *)
      iMod (own_update with "Hσst") as "[$ Hat]".
      { by apply store_alloc_update. }
      (* update the length store with the length of the new block *)
      iMod (own_update with "Hσlen") as "[$ Hlen]".
      { by apply lenstore_alloc_update. }
      (* establish the new resource mapsto_at_view_block *)
      rewrite mapsto_at_view_block_eq. iDestruct ("HΦ" $! ℓ with "[Hat Hlen]") as "$".
      {
        rewrite /mapsto_at_view_block_def replicate_length has_length_eq Z2Nat.id//.
        iFrame "Hlen".
        rewrite big_opL_auth_frag. iDestruct (big_opL_own_1 with "Hat") as "Hat".
        iInduction (Z.to_nat n) as [ | n' ] "IH".
        - done.
        - rewrite seq_S replicate_S_end 2!big_opL_app /=.
          iDestruct "Hat" as "(Hat' & ? & _)".
          iSplitL "Hat'" ; [|iSplit ; [|done]].
          + by iApply "IH".
          + rewrite replicate_length Nat.add_0_r mapsto_at_view_eq.
            iExists _. auto with iFrame.
      }
      iDestruct "Hσse" as (Vseen) "[HVseen Hσseen]".
      iDestruct "Hσseen" as %(Hseen_at & Hseen_na & Hseen_none).
      iAssert ⌜V' ⊑ Vseen⌝%I with "[Hseen HVseen]" as %?.
      { iApply (own_lat_auth_max (LAT:=view_Lat)). iFrame. by rewrite seen_eq. }
      iExists Vseen. iFrame. iPureIntro. split ; last split.
      + intros [ℓ' i'] v' Vℓ' Hℓ'. destruct (decide (ℓ = ℓ')) as [<-|].
        * rewrite store_lookup_eq lookup_insert /= in Hℓ'.
          case_bool_decide; last done.
          apply lookup_replicate in Hℓ' as [Hℓ' _]. by inversion Hℓ'.
        * rewrite store_lookup_eq lookup_insert_ne // -store_lookup_eq in Hℓ'. eauto.
      + intros [ℓ' i'] h Hℓ'. destruct (decide (ℓ = ℓ')) as [<-|].
        * rewrite store_lookup_eq lookup_insert /= in Hℓ'.
          case_bool_decide; last done.
          apply lookup_replicate in Hℓ' as [Hℓ' _]. congruence.
        * rewrite store_lookup_eq lookup_insert_ne // -store_lookup_eq in Hℓ'. auto.
      + intros [ℓ' i'] Hℓ'. destruct (decide (ℓ = ℓ')) as [<-|].
        * rewrite Hseen_none // store_lookup_eq (_ : σ1 !! ℓ = None) ; last done.
          case_bool_decide; done.
        * rewrite store_lookup_eq lookup_insert_ne // -store_lookup_eq in Hℓ'. auto.
  Qed.

  Lemma wp_length_view_lang E ℓ (n : Z) V Φ :
    has_length ℓ n -∗
    ▷ Φ (#n at V)%V -∗
    WP Length #ℓ at V @ E {{ Φ }}.
  Proof.
    iIntros "Hlen HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Length #ℓ at V)); auto.
    iIntros (σ1 ? κ κs k) "[Hσst Hσse] !>".
    iDestruct (store_interp_has_length with "Hσst Hlen") as %(blk & ? & <-). iSplit.
    - iPureIntro. repeat eexists _. eapply view_lang.impure_step ; by econstructor.
    - iNext; iIntros (e2 σ2 efs Hstep) "_ !>". inv_head_step. iSplit=>//. by iFrame.
  Qed.

  Lemma wp_read_na_view_lang E ℓ i h V q :
    {{{
      ▷ hist_na (ℓ.[i]) h q ∗
      seen V
    }}}
      Read NonAtomic #ℓ #i at V @ E
    {{{ v t,
      RET v at V;
      ⌜V !! ℓ.[i] ⊑ t ∧ h !! t = Some v⌝ ∗
      hist_na (ℓ.[i]) h q
    }}}.
  Proof.
    iIntros (Φ) "[>Hℓ Hseen] HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Read NonAtomic #ℓ #i at V)); auto.
    iIntros (σ1 ? κ κs k) "[Hσst Hσse] !>".
    iDestruct (store_interp_hist_na with "Hσst Hℓ") as %Hℓ. iSplit.
    - iDestruct "Hσse" as (V') "(Hσse & _ & Hseen_na & _)". rewrite seen_eq.
      iDestruct (own_valid_2 with "Hσse Hseen") as
          %[HVV'%latT_included _]%auth_both_valid_discrete.
      iDestruct "Hseen_na" as %Hseen_na. destruct (Hseen_na _ _ Hℓ). eauto.
    - iNext; iIntros (e2 σ2 efs Hstep) "_"; inv_head_step. iSplitR=>//.
      iFrame. iApply "HΦ". iFrame. iPureIntro. split=>//.
      by match goal with H : σ2 !! _ = _ |- _ => rewrite H in Hℓ; inversion Hℓ; subst end.
  Qed.

  Lemma wp_read_at_view_view_lang E ℓ i v Vℓ V q :
    {{{
      ▷ ℓ.[i] ↦at{q}(v, Vℓ) ∗
      seen V
    }}}
      Read Atomic #ℓ #i at V @ E
    {{{ V',
      RET v at V';
      ⌜Vℓ ⊑ V' ∧ V ⊑ V'⌝ ∗
      ℓ.[i] ↦at{q}(v, Vℓ) ∗
      seen V'
    }}}.
  Proof.
    iIntros (Φ) "[>Hℓ #Hseen] HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Read Atomic #ℓ #i at V)); auto.
    iIntros (σ1 ? κ κs k) "[Hσst Hσse] !>".
    iDestruct (store_interp_mapsto_at_view with "Hσst Hℓ") as %(Vℓ' & HVℓ' & Hℓ).
    iSplit; [by eauto|]. iNext; iIntros (e2 σ2 efs Hstep) "_"; inv_head_step.
    iSplitR=>//.
    iAssert (seen Vℓ' ∗ seen_interp σ2)%I with "[> Hσse]" as "[#Hseenℓ' Hσse]".
    { iDestruct "Hσse" as (W) "(HW & Hseen_at & %)".
      iDestruct "Hseen_at" as %Hseen_at. pose proof (Hseen_at ℓ.[i] v Vℓ' Hℓ).
      iMod (own_lat_auth_update_fork with "HW") as "[HW #HW◯]".
      iDestruct (own_lat_auth_downclosed with "HW◯") as "HVℓ'"=>//.
      rewrite seen_eq /seen_interp. eauto. }
    iFrame. iApply "HΦ". iFrame. iSplitL.
    - iPureIntro. split; solve_lat.
    - by iApply seen_join.
  Qed.

  Lemma wp_read_at_view_lang E ℓ i v V q :
    {{{
      ▷ ℓ.[i] ↦at{q} v ∗
      seen V
    }}}
      Read Atomic #ℓ #i at V @ E
    {{{ V',
      RET v at V';
      ⌜V ⊑ V'⌝ ∗
      ℓ.[i] ↦at{q} v ∗
      seen V'
    }}}.
  Proof.
    iIntros (Φ) "[>Hℓ Hseen] HΦ".
    iApply (wp_read_at_view_view_lang with "[$Hℓ $Hseen]").
    iIntros "!> % ([_ %] & Hℓ & Hseen)". iApply "HΦ". by iFrame.
  Qed.

  Lemma store_write_update σ ℓi (elt0 elt elt' : store_elt) :
    σ !! ℓi = Some elt0 →
    ● store_to_cmra σ ⋅ ◯ {[ ℓi := elt_to_cmra elt ]} ~~>
    ● store_to_cmra (<[ℓi := elt']> σ) ⋅ ◯ {[ ℓi := elt_to_cmra elt' ]}.
  Proof.
    intros Hσ. rewrite store_to_cmra_insert //.
    eapply auth_update, singleton_local_update, exclusive_local_update.
    - by rewrite lookup_store_to_cmra Hσ.
    - by destruct elt'.
  Qed.

  Lemma wp_write_na_view_lang E ℓ i v h V :
    {{{
      ▷ hist_na (ℓ.[i]) h 1 ∗ seen V
    }}}
      Write NonAtomic #ℓ #i v at V @ E
    {{{ t,
      RET #() at (<[ℓ.[i] := t]> V);
      ⌜V !! ℓ.[i] ⊑ Some t ∧ h !! (Some t) = None⌝ ∗
      hist_na (ℓ.[i]) (<[Some t := v]>h) 1 ∗
      seen (<[ℓ.[i] := t]> V)
    }}}.
  Proof.
    iIntros (Φ) "[>Hℓ Hseen] HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Write NonAtomic #ℓ #i v at V)); auto.
    iIntros (σ1 ? κ κs k) "[Hσst Hσse] !>".
    iDestruct (store_interp_hist_na with "Hσst Hℓ") as %Hℓ. iSplit.
    - assert (Hinf : pred_infinite (λ t, V !! ℓ.[i] ⊔ Some 1%Qp ⊑ t)).
      { clear. intros ts.
        exists (foldr (λ t a, a ⊔ (Some (from_option (Qp.add 1) 1%Qp t)))
                      (V !! ℓ.[i] ⊔ Some 1%Qp) ts). split.
        - induction ts as [|t ts IH]; solve_lat.
        - assert (Hts : ∀ t, (∀ t', t' ∈ ts → strict (⊑) t' t) → t ∉ ts)
            by naive_solver.
          apply Hts. clear. induction 1 as [t ts|t t' ts _ IH]=>/=.
          + eapply strict_transitive_l, lat_join_sqsubseteq_r.
            apply total_not_strict. destruct t; [|by intro].
            apply Qp.lt_nge, Qp.lt_add_r.
          + by eapply strict_transitive_l, lat_join_sqsubseteq_l. }
      rewrite ->(pred_infinite_set (C:=gset timestamp)) in Hinf.
      destruct (Hinf (dom h))
        as (tw & ? & Hdom%(not_elem_of_dom (M := gmap _))).
      assert (V !! ℓ.[i] ⊑ tw ∧ Some 1%Qp ⊑ tw) as [??] by (split ; solve_lat).
      destruct tw as [tw|]=>//. by eauto.
    - iNext; iIntros (e2 σ2 efs Hstep) "_"; inv_head_step. iSplitR=>//.
      match goal with H : σ1 !! _ = Some _ |- _ => rewrite H in Hℓ; inversion Hℓ; subst; clear Hℓ end.
      rewrite hist_na_eq /store_interp.
      iDestruct "Hσst" as "[Hσst Hσlen]".
      iMod (own_update_2 with "Hσst Hℓ") as "[$ Hhist]".
      { by apply (store_write_update _ _ (store_elt_na h) (store_elt_na h)). }
      iAssert (hist_na_def (ℓ.[i]) (<[Some _ := v]>h) 1) with "Hhist" as "Hhist".
      rewrite store_to_lenstore_cmra_insert. iFrame "Hσlen".
      iDestruct "Hσse" as (Vseen) "[Hσse Hseenσ]".
      iDestruct "Hseenσ" as %(Hseen_at & Hseen_na & Hseen_none).
      iMod (own_update with "Hσse") as "[Hσse Hseen']".
      { by eapply auth_update_alloc,
                  (op_local_update_discrete _ _ (to_latT {[ ℓ.[i] := _ ]})). }
      iDestruct ("HΦ" with "[Hhist Hseen Hseen']") as "$".
      { iSplitR=>//. iFrame. rewrite right_id seen_eq.
        iCombine "Hseen' Hseen" as "Hseen". iApply own_mono; [|done].
        apply auth_frag_mono, latT_included=>/= ℓ'.
        match goal with |- context [<[?ℓ:=_]>] => edestruct (decide (ℓ' = ℓ)) as [<-|] end.
        - rewrite lookup_insert lookup_join.
          etrans; [|by apply lat_join_sqsubseteq_l]. apply reflexive_eq.
          symmetry. apply lookup_singleton.
        - rewrite lookup_insert_ne // lookup_join lookup_singleton_ne //. }
      iExists _. iFrame. iPureIntro. split ; last split.
      + intros ℓi' vℓ' Vℓ' Hℓ'. destruct (decide (ℓ.[i] = ℓi')) as [<-|].
        * erewrite store_lookup_insert in Hℓ' ; last done. congruence.
        * rewrite store_lookup_insert_ne // in Hℓ'. solve_lat.
      + intros ℓi' h' Hℓ'. destruct (decide (ℓ.[i] = ℓi')) as [<-|].
        * erewrite store_lookup_insert in Hℓ' ; last done. inversion Hℓ'; subst ; clear Hℓ'.
          rewrite lookup_join lookup_singleton /=.
          match goal with |- context [<[Some ?t':=_]> h !! (_ ⊔ ?tℓ)] =>
            destruct (decide (Some t' = Some t' ⊔ tℓ)) as [<-|Hne];
              [|destruct (total (⊑) (Some t') tℓ)]
          end.
          -- rewrite /history lookup_insert. eauto.
          -- rewrite /history lookup_insert_ne // lat_le_join_r_L //. auto.
          -- destruct Hne. solve_lat.
        * rewrite store_lookup_insert_ne // in Hℓ'.
          rewrite lookup_join lookup_singleton_ne //. by apply Hseen_na.
      + intros ℓi' Hℓ'. destruct (decide (ℓ.[i] = ℓi')) as [<-|].
        * erewrite store_lookup_insert in Hℓ' ; last done. congruence.
        * rewrite store_lookup_insert_ne // in Hℓ'.
          rewrite lookup_join lookup_singleton_ne // Hseen_none //.
  Qed.

  Lemma wp_write_at_view_view_lang E ℓ i v Vℓ v' V :
    {{{
      ▷ ℓ.[i] ↦at(v, Vℓ) ∗
      seen V
    }}}
      Write Atomic #ℓ #i v' at V @ E
    {{{ V',
      RET #() at V';
      ⌜Vℓ ⊑ V' ∧ V ⊑ V'⌝ ∗
      ℓ.[i] ↦at(v', Vℓ ⊔ V) ∗
      seen V'
    }}}.
  Proof.
    iIntros (Φ) "[>Hℓ #Hseen] HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Write Atomic #ℓ #i v' at V)); auto.
    iIntros (σ1 ? κ κs k) "[Hσst Hσse] !>".
    iDestruct (store_interp_mapsto_at_view with "Hσst Hℓ") as %(Vℓ' & HVℓ' & Hℓ).
    iSplit; [by eauto|]. iNext; iIntros (e2 σ2 efs Hstep) "_"; inv_head_step. iSplitR=>//.
    rewrite mapsto_at_view_eq. iDestruct "Hℓ" as (Vℓ'') "[% Hℓ]".
    iDestruct "Hσst" as "[Hσst Hσlen]".
    iMod (own_update_2 with "Hσst Hℓ") as "[$ Hℓ]".
    { by eapply (store_write_update _ _ _ (store_elt_at _ _)). }
    clear dependent Vℓ''.
    rewrite store_to_lenstore_cmra_insert. iFrame "Hσlen".
    iAssert (seen (Vℓ' ⊔ V) ∗ seen_interp σ1)%I with "[> Hσse]" as "[#Hseen' Hσse]".
    { iDestruct "Hσse" as (W) "(HW & Hseen_at & %)".
      iDestruct "Hseen_at" as %Hseen_at. pose proof (Hseen_at ℓ.[i] v Vℓ' Hℓ).
      iMod (own_lat_auth_update_fork with "HW") as "[HW HW◯]".
      iDestruct (own_lat_auth_downclosed with "HW◯") as "HVℓ'"=>//.
      iSplitR "HW" ; last by (rewrite /seen_interp ;auto).
      iApply (seen_join with "[-] [$]"). by rewrite seen_eq. }
    iClear "Hseen".
    iDestruct ("HΦ" with "[Hℓ $Hseen']") as "$".
    { iSplit; [iPureIntro;split;solve_lat|]. iExists _. iIntros "{$∗} !%". solve_lat. }
    iDestruct "Hσse" as (Vseen) "[Hσse Hseenσ]".
    iDestruct "Hseenσ" as %(Hseen_at & Hseen_na & Hseen_none).
    iAssert ⌜Vℓ' ⊔ V ⊑ Vseen⌝%I with "[Hσse Hseen']" as %?.
    { iApply (own_lat_auth_max (LAT:=view_Lat)). iFrame. by rewrite seen_eq. }
    iExists _. iFrame. iPureIntro. split ; last split.
    + intros ℓi1 v1 Vℓ1 Hℓ1. destruct (decide (ℓ.[i] = ℓi1)) as [<-|].
      * erewrite store_lookup_insert in Hℓ1 ; last done. inversion Hℓ1; subst; done.
      * rewrite store_lookup_insert_ne // in Hℓ1. eauto.
    + intros ℓi' h'. destruct (decide (ℓ.[i] = ℓi')) as [<-|].
      * erewrite store_lookup_insert ; last done. congruence.
      * rewrite store_lookup_insert_ne //. auto.
    + intros ℓi'. destruct (decide (ℓ.[i] = ℓi')) as [<-|].
      * erewrite store_lookup_insert ; last done. congruence.
      * rewrite store_lookup_insert_ne //. auto.
  Qed.

  Lemma wp_write_at_view_lang E ℓ i v v' V :
    {{{
      ▷ ℓ.[i] ↦at v ∗ seen V
    }}}
      Write Atomic #ℓ #i v' at V @ E
    {{{ V',
      RET #() at V';
      ⌜V ⊑ V'⌝ ∗
      ℓ.[i] ↦at v' ∗
      seen V'
    }}}.
  Proof.
    iIntros (Φ) "[>Hℓ Hseen] HΦ".
    iApply (wp_write_at_view_view_lang with "[$Hℓ $Hseen]").
    iIntros "!> % ([_ %] & Hℓ & Hseen)". rewrite -(_ : ∅ ⊑ ∅ ⊔ V); [|solve_lat].
    iApply "HΦ". by iFrame.
  Qed.

  Lemma wp_cas_fail_view_view_lang E ℓ i q l Vℓ V l1 v2 :
    l ≠ l1 → lit_compare_safe l l1 →
    {{{
      ▷ ℓ.[i] ↦at{q}(#l, Vℓ) ∗
      seen V
    }}}
      CAS #ℓ #i #l1 v2 at V @ E
    {{{ V',
      RET #false at V';
      ⌜Vℓ ⊑ V' ∧ V ⊑ V'⌝ ∗
      ℓ.[i] ↦at{q}(#l, Vℓ) ∗
      seen V'
    }}}.
  Proof.
    iIntros (Hll1 Hsafe Φ) "[>Hℓ Hseen] HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (CAS #ℓ #i #l1 v2 at V)); auto.
    iIntros (σ1 ? κ κs k) "[Hσst Hσse] !>".
    iDestruct (store_interp_mapsto_at_view with "Hσst Hℓ") as %(Vℓ' & HVℓ' & Hℓ).
    assert (lit_neq l1 l). { destruct l, l1=>//=; naive_solver. }
    iSplit; [by eauto 10|].
    iNext; iIntros (e2 σ2 efs Hstep) "_"; inv_head_step;
    last (destruct l1, l; naive_solver).
    iSplitR=>//.
    iAssert (seen Vℓ' ∗ seen_interp σ2)%I with "[> Hσse]" as "[#Hseenℓ' Hσse]".
    { iDestruct "Hσse" as (W) "(HW & Hseen_at & %)".
      iDestruct "Hseen_at" as %Hseen_at. pose proof (Hseen_at ℓ.[i] _ Vℓ' Hℓ).
      iMod (own_lat_auth_update_fork with "HW") as "[HW HW◯]".
      iDestruct (own_lat_auth_downclosed with "HW◯") as "HVℓ'"=>//.
      rewrite seen_eq /seen_interp. eauto. }
    iFrame. iApply "HΦ". iFrame. iSplitR.
    - iPureIntro. split; solve_lat.
    - by iApply seen_join.
  Qed.

  Lemma wp_cas_fail_view_lang E ℓ i q l V l1 v2 :
    l ≠ l1 → lit_compare_safe l l1 →
    {{{
      ▷ ℓ.[i] ↦at{q} #l ∗
      seen V
    }}}
      CAS #ℓ #i #l1 v2 at V @ E
    {{{ V',
      RET #false at V';
      ⌜V ⊑ V'⌝ ∗
      ℓ.[i] ↦at{q} #l ∗
      seen V'
    }}}.
  Proof.
    iIntros (Hll1 Hsafe Φ) "[Hℓ Hseen] HΦ".
    iApply (wp_cas_fail_view_view_lang with "[$Hℓ $Hseen]")=>//.
    iIntros "!> % ([_ %] & Hℓ & Hseen)". iApply "HΦ". by iFrame.
  Qed.

  Lemma wp_cas_suc_view_view_lang E ℓ i l Vℓ V l1 v2 :
    l = l1 → lit_compare_safe l l1 →
    {{{
      ▷ ℓ.[i] ↦at(#l, Vℓ) ∗
      seen V
    }}}
      CAS #ℓ #i #l1 v2 at V @ E
    {{{ V',
      RET #true at V';
      ⌜Vℓ ⊑ V' ∧ V ⊑ V'⌝ ∗
      ℓ.[i] ↦at(v2, Vℓ ⊔ V) ∗
      seen V'
    }}}.
  Proof.
    iIntros (Hll1 Hsafe Φ) "[> Hℓ #Hseen] HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (CAS #ℓ #i #l1 v2 at V)); auto.
    iIntros (σ1 ? κ κs k) "[Hσst Hσse] !>".
    iDestruct (store_interp_mapsto_at_view with "Hσst Hℓ") as %(Vℓ' & HVℓ' & Hℓ).
    assert (lit_eq l1 l). { destruct l, l1=>//=; naive_solver. }
    iSplit; [by eauto 10|].
    iNext; iIntros (e2 σ2 efs Hstep) "_"; inv_head_step;
    first (destruct l1; naive_solver).
    iSplitR=>//. rewrite mapsto_at_view_eq. iDestruct "Hℓ" as (Vℓ'') "[% Hℓ]".
    (**)
    iDestruct "Hσst" as "[Hσst Hσlen]".
    iMod (own_update_2 with "Hσst Hℓ") as "[$ Hℓ]".
    { by eapply (store_write_update _ _ _ (store_elt_at _ _)). }
    clear dependent Vℓ''.
    rewrite store_to_lenstore_cmra_insert. iFrame "Hσlen".
    iAssert (seen (Vℓ' ⊔ V) ∗ seen_interp σ1)%I with "[> Hσse]" as "[#Hseen' Hσse]".
    { iDestruct "Hσse" as (W) "(HW & Hseen_at & %)".
      iDestruct "Hseen_at" as %Hseen_at. pose proof (Hseen_at ℓ.[i] _ Vℓ' Hℓ).
      iMod (own_lat_auth_update_fork with "HW") as "[HW HW◯]".
      iDestruct (own_lat_auth_downclosed with "HW◯") as "HVℓ'"=>//.
      iSplitR "HW" ; last by (rewrite /seen_interp ;auto).
      iApply (seen_join with "[-] [$]"). by rewrite seen_eq. }
    iClear "Hseen".
    iDestruct ("HΦ" with "[Hℓ $Hseen']") as "$".
    { iSplit; [iPureIntro;split;solve_lat|]. iExists _. iFrame. iPureIntro;solve_lat. }
    iDestruct "Hσse" as (Vseen) "[Hσse Hseenσ]".
    iDestruct "Hseenσ" as %(Hseen_at & Hseen_na & Hseen_none).
    iAssert ⌜Vℓ' ⊔ V ⊑ Vseen⌝%I with "[Hσse Hseen']" as %?.
    { iApply (own_lat_auth_max (LAT:=view_Lat)). iFrame. by rewrite seen_eq. }
    iExists _. iFrame. iPureIntro. split ; last split.
    + intros ℓi1 v1 Vℓ1 Hℓ1. destruct (decide (ℓ.[i] = ℓi1)) as [<-|].
      * erewrite store_lookup_insert in Hℓ1 ; last done. inversion Hℓ1; subst; done.
      * rewrite store_lookup_insert_ne // in Hℓ1. eauto.
    + intros ℓi' h'. destruct (decide (ℓ.[i] = ℓi')) as [<-|].
      * erewrite store_lookup_insert ; last done. congruence.
      * rewrite store_lookup_insert_ne //. auto.
    + intros ℓi'. destruct (decide (ℓ.[i] = ℓi')) as [<-|].
      * erewrite store_lookup_insert ; last done. congruence.
      * rewrite store_lookup_insert_ne //. auto.
  Qed.

  Lemma wp_cas_suc_view_lang E ℓ i l V l1 v2 :
    l = l1 → lit_compare_safe l l1 →
    {{{
      ▷ ℓ.[i] ↦at #l ∗
      seen V
    }}}
      CAS #ℓ #i #l1 v2 at V @ E
    {{{ V',
      RET #true at V';
      ⌜V ⊑ V'⌝ ∗
      ℓ.[i] ↦at v2 ∗
      seen V'
    }}}.
  Proof.
    iIntros (Hll1 Hsafe Φ) "[>Hℓ Hseen] HΦ".
    iApply (wp_cas_suc_view_view_lang with "[$Hℓ $Hseen]")=>//.
    iIntros "!> % ([_ %] & Hℓ & Hseen)". iApply "HΦ".
    rewrite -(_ : ∅ ⊑ ∅ ⊔ V); [|solve_lat]. by iFrame.
  Qed.
End lifting_view_lang.

Section lifting_vprop.
  Context `{!cosmoG Σ}.

  Implicit Types Φ : val → vProp Σ.
  Implicit Types Vℓ : view.
  Implicit Types q : Qp.

  Notation wp_wand := iris.program_logic.weakestpre.wp_wand.

  Lemma wp_pure_step_fupd E E' e1 e2 φ n Φ :
    PureExecBase φ n e1 e2 →
    φ →
    (|={E}[E']▷=>^n WP e2 @ E {{ Φ }}) ⊢
    WP e1 @ E {{ Φ }}.
  Proof.
    rewrite wp_eq=>Hexec Hφ. iStartProof (iProp _).
    iIntros "% Hwp" (V ->) "Hseen". iApply (wp_pure_step_fupd _ E E')=>//.
    clear Hexec. iInduction n as [|n] "IH" => /=.
    - iIntros "_". by iApply "Hwp".
    - iMod "Hwp". iModIntro. iModIntro. iMod "Hwp". iModIntro.
      iApply (step_fupdN_wand with "(IH Hwp Hseen)"). iIntros "Hwp (_ & H£)".
      iApply ("Hwp" with "H£").
  Qed.

  Lemma wp_pure_step_later E e1 e2 φ n Φ :
    PureExecBase φ n e1 e2 →
    φ →
    ▷^n WP e2 @ E {{ Φ }} ⊢
    WP e1 @ E {{ Φ }}.
  Proof.
    intros Hexec ?. rewrite -wp_pure_step_fupd //. clear Hexec.
    induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
  Qed.

  Lemma wp_fork E e Φ :
    ▷ WP e @ ⊤ {{ _, True }} -∗
    ▷ Φ #() -∗
    WP Fork e @ E {{ Φ }}.
  Proof.
    rewrite wp_eq. iStartProof (iProp _). iIntros "% Hwp % -> HΦ" (V ->) "#Hseen".
    iApply (wp_fork_view_lang with "[Hwp] [-]").
    - iNext. iSpecialize ("Hwp" $! _ with "[//] Hseen").
      iApply (wp_wand with "Hwp"). auto.
    - by iFrame.
  Qed.

  Lemma wp_alloc_na E n v Φ :
    (0 ≤ n)%Z →
    ▷ (∀ ℓ, ℓ *↦ replicate (Z.to_nat n) v -∗ Φ #ℓ) -∗
    WP Alloc NonAtomic #n v @ E {{ Φ }}.
  Proof.
    rewrite wp_eq. iStartProof (iProp _). iIntros (_V1 _V2) "HΦ".
    iIntros (V HV) "Hseen". iApply wp_alloc_na_view_lang ; first done.
    iNext. iFrame. iIntros (ℓ) "Hhist". setoid_rewrite mapsto_na_block_equiv.
    iApply "HΦ". iExists ∅, (replicate _ _). iFrame "Hhist".
    rewrite big_sepL2_alt big_sepL_forall. iPureIntro.
    split ; first done.
    split ; first by rewrite !replicate_length.
    intros i (v1, h) Hi =>/= ;
      setoid_rewrite lookup_zip_with_Some in Hi;
      setoid_rewrite lookup_replicate in Hi ;
      destruct Hi as (v2 & h2 & [=] & [[=] _] & [[=] _]) ; subst.
    split ; first by auto.
    intros [t|].
    - rewrite lookup_insert_ne // lookup_empty. auto.
    - rewrite lookup_insert lookup_empty. auto.
  Qed.

  Lemma wp_alloc_at_view E n v V :
    (0 ≤ n)%Z →
    {{{
      monPred_in V
    }}}
      Alloc Atomic #n v @ E
    {{{ ℓ,
      RET #ℓ;
      ⎡ℓ *↦at() replicate (Z.to_nat n) (v, V)⎤
    }}}.
  Proof.
    rewrite wp_eq. iStartProof (iProp _). iIntros (Hn Φ W HW X HX) "HΦ %% #Hseen".
    iApply wp_alloc_at_view_lang=>//. iNext. iFrame "Hseen". iIntros (ℓ) "Hℓ".
    iApply "HΦ". rewrite mapsto_at_view_block_eq /mapsto_at_view_block_def.
    rewrite !replicate_length. iDestruct "Hℓ" as "[$ Hℓ]".
    iApply (big_opL_gen_proper_2 (⊢) with "Hℓ") ; first done.
    intros k. destruct (decide (k < n)%Z).
    - rewrite !lookup_replicate_2; [|lia|lia]. rewrite (_:V⊑_) //. solve_lat.
    - rewrite !(proj1 (lookup_replicate_None _ _ _)) // ; lia.
  Qed.

  Lemma wp_alloc_at E n v Φ :
    (0 ≤ n)%Z →
    ▷ (∀ ℓ, ⎡ℓ *↦at replicate (Z.to_nat n) v⎤ -∗ Φ #ℓ) -∗
    WP Alloc Atomic #n v @ E {{ Φ }}.
  Proof.
    iIntros (?) "HΦ". iApply (wp_alloc_at_view _ _ _ ∅); [done | | by rewrite fmap_replicate].
    iDestruct (monPred_in_intro emp%I with "[//]") as (V) "[HV _]".
    by rewrite -(lat_bottom_sqsubseteq V).
  Qed.

  Lemma wp_length E ℓ (n : Z) Φ :
    ⎡has_length ℓ n⎤ -∗
    ▷ Φ #n -∗
    WP Length #ℓ @ E {{ Φ }}.
  Proof.
    rewrite wp_eq. iStartProof (iProp _). iIntros "% Hlen % _ HΦ % -> Hseen".
    iApply (wp_length_view_lang with "Hlen"). by iFrame.
  Qed.

  Lemma na_block_accessor ℓ i vs q :
    0 ≤ i < length vs →
    ℓ *↦{q} vs -∗
      ∃ v,
      ⌜vs !! i = Some v⌝ ∗
      ℓ.[i] ↦{q} v ∗
        ∀ v',
        ℓ.[i] ↦{q} v' -∗
        ℓ *↦{q} (<[i := v']> vs).
  Proof.
    iIntros (Hineq) "Hℓ".
    destruct (vs !! i) as [v|] eqn:Hlookup.
    { iExists v. iSplit ; first done.
      rewrite /mapsto_na_block. iDestruct "Hℓ" as "(Hlen & Hlist)".
      apply list_lookup_Z_Some_to_nat in Hlookup.
      iDestruct (big_sepL_insert_acc _ _ _ _ Hlookup with "Hlist") as "[Hℓi Hclose]".
      rewrite Z2Nat.id ; last lia.
      iFrame "Hℓi". iIntros (v').
      rewrite list_insert_Z_to_nat ; last lia. rewrite insert_length ; iFrame "Hlen".
      by iApply "Hclose". }
    { exfalso. rewrite ->list_lookup_Z_to_nat, lookup_ge_None in Hlookup ; lia. }
  Qed.

  Lemma at_block_accessor ℓ i vVs q :
    0 ≤ i < length vVs →
    ℓ *↦at{q}() vVs -∗
      ∃ v Vℓ,
      ⌜vVs !! i = Some (v, Vℓ)⌝ ∗
      ℓ.[i] ↦at{q}(v, Vℓ) ∗
        ∀ v' Vℓ',
        ℓ.[i] ↦at{q}(v', Vℓ') -∗
        ℓ *↦at{q}() (<[i := (v', Vℓ')]> vVs).
  Proof.
    iIntros (Hineq) "Hℓ".
    destruct (vVs !! i) as [[v Vℓ]|] eqn:Hlookup.
    { iExists v, Vℓ. iSplit ; first done.
      rewrite mapsto_at_view_block_eq /mapsto_at_view_block_def.
      iDestruct "Hℓ" as "(Hlen & Hlist)".
      apply list_lookup_Z_Some_to_nat in Hlookup.
      iDestruct (big_sepL_insert_acc _ _ _ _ Hlookup with "Hlist") as "[Hℓi Hclose]".
      rewrite Z2Nat.id ; last lia.
      iFrame "Hℓi". iIntros (v' Vℓ').
      rewrite list_insert_Z_to_nat ; last lia. rewrite insert_length ; iFrame "Hlen".
      by iApply ("Hclose" $! (_, _)). }
    { exfalso. rewrite ->list_lookup_Z_to_nat, lookup_ge_None in Hlookup ; lia. }
  Qed.

  Lemma wp_read_na E ℓ i v q :
    {{{
      ▷ ℓ.[i] ↦{q} v
    }}}
      Read NonAtomic #ℓ #i @ E
    {{{
      RET v;
      ℓ.[i] ↦{q} v
    }}}.
  Proof.
    rewrite wp_eq. iStartProof (iProp _). iIntros (Φ ?) "H % -> HΦ %_V -> #Hseen".
    iMod "H". iDestruct "H" as (V h HV) "(Hhist & Hv & Ht)".
    iDestruct "Ht" as %Ht. iDestruct "Hv" as %Hv.
    iApply (wp_read_na_view_lang with "[$Hhist //]").
    iIntros "!>" (v' t) "[[% Hv'] Hhist]". iDestruct "Hv'" as %Hv'. iFrame "Hseen".
    assert (t = V !! ℓ.[i]) as ->.
    { apply (anti_symm (⊑)); last (specialize (HV ℓ.[i]); solve_lat).
      destruct (Ht t) as [EQ|]=>//. by rewrite EQ in Hv'. }
    rewrite Hv' in Hv. injection Hv=>?. subst. iApply "HΦ".
    iExists _, _. auto.
  Qed.

  Lemma wp_read_na_block E ℓ i v vs q :
    {{{
      ▷ ⌜vs !! i = Some v⌝ ∗
      ▷ ℓ *↦{q} vs
    }}}
      Read NonAtomic #ℓ #i @ E
    {{{
      RET v;
      ℓ *↦{q} vs
    }}}.
  Proof.
    iIntros (Φ) "[>Hlookup >Hℓ] HΦ" ; iDestruct "Hlookup" as %Hlookup.
    apply list_lookup_Z_lt_Some in Hlookup as Hi.
    iDestruct (na_block_accessor _ _ _ _ Hi with "Hℓ") as "Hacc".
    iDestruct "Hacc" as (?) "(Hlookup & Hℓi & Hclose)" ;
      iDestruct "Hlookup" as %Hlookup0 ;
      rewrite Hlookup in Hlookup0 ; injection Hlookup0 as <-.
    iApply (wp_read_na with "Hℓi"). iIntros "!> ?". iApply "HΦ".
    iSpecialize ("Hclose" $! v). rewrite list_insert_Z_id//.
    by iApply "Hclose".
  Qed.

  Lemma wp_read_at_view E ℓ i v Vℓ q :
    {{{
      ▷ ⎡ℓ.[i] ↦at{q}(v, Vℓ)⎤
    }}}
      Read Atomic #ℓ #i @ E
    {{{
      RET v;
      monPred_in Vℓ ∗
      ⎡ℓ.[i] ↦at{q}(v, Vℓ)⎤
    }}}.
  Proof.
    rewrite wp_eq. iStartProof (iProp _). iIntros (Φ ?) "H % _ HΦ %_V -> #Hseen".
    iApply (wp_read_at_view_view_lang with "[$H $Hseen]").
    iIntros "!>" (V) "([%%] & ? & $)". iApply "HΦ". auto.
  Qed.

  Lemma wp_read_at_block_view E ℓ i v Vℓ vVs q :
    {{{
      ▷ ⌜vVs !! i = Some (v, Vℓ)⌝ ∗
      ▷ ⎡ℓ *↦at{q}() vVs⎤
    }}}
      Read Atomic #ℓ #i @ E
    {{{
      RET v;
      monPred_in Vℓ ∗
      ⎡ℓ *↦at{q}() vVs⎤
    }}}.
  Proof.
    iIntros (Φ) "[>Hlookup >Hℓ] HΦ" ; iDestruct "Hlookup" as %Hlookup.
    apply list_lookup_Z_lt_Some in Hlookup as Hi.
    iDestruct (at_block_accessor _ _ _ _ Hi with "Hℓ") as "Hacc".
    iDestruct "Hacc" as (? ?) "(Hlookup & Hℓi & Hclose)" ;
      iDestruct "Hlookup" as %Hlookup0 ;
      rewrite Hlookup in Hlookup0 ; injection Hlookup0 as <- <-.
    iApply (wp_read_at_view with "Hℓi"). iIntros "!> [??]". iApply "HΦ". iFrame.
    iSpecialize ("Hclose" $! v Vℓ). rewrite list_insert_Z_id//.
    by iApply "Hclose".
  Qed.

(*
  (* ICFP20: This is the rule AT-READ-SC of the paper. *)
  Lemma wp_read_at E ℓ i v q :
    {{{ ▷ ⎡ℓ.[i] ↦at{q}v⎤ }}} Read Atomic #ℓ #i @ E {{{ RET v; ⎡ℓ.[i] ↦at{q}v⎤ }}}.
  Proof.
    iIntros (Φ) "H HΦ". iApply (wp_read_at_view with "[$]").
    iIntros "!> [_ ?]". by iApply "HΦ".
  Qed.
*)

  Lemma wp_write_na E ℓ i v v' :
    {{{
      ▷ ℓ.[i] ↦ v
    }}}
      Write NonAtomic #ℓ #i v' @ E
    {{{
      RET #();
      ℓ.[i] ↦ v'
    }}}.
  Proof.
    rewrite wp_eq. iStartProof (iProp _). iIntros (Φ ?) "H % -> HΦ".
    iIntros (V0) "-> #Hseen".
    iMod "H". iDestruct "H" as (V h HV) "(Hhist & Hv & Ht)".
    iDestruct "Ht" as %Ht. iDestruct "Hv" as %Hv.
    iApply (wp_write_na_view_lang with "[$Hhist //]").
    iIntros "!>" (t) "[[% Hv0] [Hhist $]]". iDestruct "Hv0" as %Hv0.
    assert (V0 ⊑ <[ℓ.[i]:=t]> V0) as HV0.
    { intros ℓi'. destruct (decide (ℓ.[i] = ℓi')) as [<-|].
      - by rewrite lookup_insert.
      - by rewrite lookup_insert_ne. }
    iApply "HΦ". iExists (<[ℓ.[i]:=t]> V0), (<[Some t:=v']> h). iFrame.
    iPureIntro. split; [|split]=>//.
    - by rewrite lookup_insert (lookup_insert (M := gmap _)).
    - intros t'. rewrite lookup_insert.
      destruct (decide (Some t = t')) as [<-|]; [by auto|].
      rewrite (lookup_insert_ne (M := gmap _)) //.
      destruct (Ht t'); [by auto|]. right. etrans; [done|].
      rewrite HV HV0 lookup_insert //.
  Qed.

  Lemma wp_write_na_block E ℓ i v vs v' :
    {{{
      ▷ ⌜vs !! i = Some v⌝ ∗
      ▷ ℓ *↦ vs
    }}}
      Write NonAtomic #ℓ #i v' @ E
    {{{
      RET #();
      ℓ *↦ <[i := v']> vs
    }}}.
  Proof.
    iIntros (Φ) "[>Hlookup >Hℓ] HΦ" ; iDestruct "Hlookup" as %Hlookup.
    apply list_lookup_Z_lt_Some in Hlookup as Hi.
    iDestruct (na_block_accessor _ _ _ _ Hi with "Hℓ") as "Hacc".
    iDestruct "Hacc" as (?) "(Hlookup & Hℓi & Hclose)" ;
      iDestruct "Hlookup" as %Hlookup0 ;
      rewrite Hlookup in Hlookup0 ; injection Hlookup0 as <-.
    iApply (wp_write_na with "Hℓi"). iIntros "!> ?". iApply "HΦ".
    by iApply "Hclose".
  Qed.

  Lemma wp_write_at_view E ℓ i v V1 V2 v' :
    {{{
      monPred_in V1 ∗
      ▷ ⎡ℓ.[i] ↦at(v, V2)⎤
    }}}
      Write Atomic #ℓ #i v' @ E
    {{{
      RET #();
      monPred_in V2 ∗
      ⎡ℓ.[i] ↦at(v', V2 ⊔ V1)⎤
    }}}.
  Proof.
    rewrite wp_eq. iStartProof (iProp _). iIntros (Φ ?) "H % -> HΦ".
    iIntros (V0) "-> #Hseen". iDestruct "H" as (->) "H". clear V1.
    iApply (wp_write_at_view_view_lang with "[$H $Hseen]").
    iNext. iIntros (V) "[[%%] [H $]]". iApply "HΦ". auto.
  Qed.

  Lemma wp_write_at_block_view E ℓ i v V1 V2 vVs v' :
    {{{
      monPred_in V1 ∗
      ▷ ⌜vVs !! i = Some (v, V2)⌝ ∗
      ▷ ⎡ℓ *↦at() vVs⎤
    }}}
      Write Atomic #ℓ #i v' @ E
    {{{
      RET #();
      monPred_in V2 ∗
      ⎡ℓ *↦at() <[i := (v', V2 ⊔ V1)]> vVs⎤
    }}}.
  Proof.
    iIntros (Φ) "(#HV1 & >Hlookup & >Hℓ) HΦ" ; iDestruct "Hlookup" as %Hlookup.
    apply list_lookup_Z_lt_Some in Hlookup as Hi.
    iDestruct (at_block_accessor _ _ _ _ Hi with "Hℓ") as "Hacc".
    iDestruct "Hacc" as (??) "(Hlookup & Hℓi & Hclose)" ;
      iDestruct "Hlookup" as %Hlookup0 ;
      rewrite Hlookup in Hlookup0 ; injection Hlookup0 as <- <-.
    iApply (wp_write_at_view with "[$]"). iIntros "!> [??]". iApply "HΦ". iFrame.
    by iApply "Hclose".
  Qed.

(*
  (* ICFP20: This is the rule AT-WRITE-SC of the paper. *)
  Lemma wp_write_at E ℓ i v v' :
    {{{ ▷ ⎡ℓ.[i] ↦at v⎤ }}} Write Atomic #ℓ #i v' @ E {{{ RET #(); ⎡ℓ.[i] ↦at v'⎤ }}}.
  Proof.
    iIntros (Φ) "H HΦ".
    iDestruct (monPred_in_intro True%I with "[//]") as (V) "[Hin _]".
    iApply (wp_write_at_view with "[$H $Hin]").
    iIntros "!> [_ ?]". iApply "HΦ". by rewrite -(_:∅⊑∅⊔V).
  Qed.
*)

  Lemma wp_cas_fail_view E ℓ i q l Vℓ l1 v2 :
    l ≠ l1 →
    lit_compare_safe l l1 →
    {{{
      ▷ ⎡ℓ.[i] ↦at{q}(#l, Vℓ)⎤
    }}}
    CAS #ℓ #i #l1 v2 @ E
    {{{
      RET #false;
      monPred_in Vℓ ∗
      ⎡ℓ.[i]↦at{q}(#l, Vℓ)⎤
    }}}.
  Proof.
    rewrite wp_eq. iStartProof (iProp _). iIntros (?? Φ ?) "H % _ HΦ %_V -> #Hseen".
    iApply (wp_cas_fail_view_view_lang with "[$H $Hseen]")=>//.
    iIntros "!>" (V) "([%%] & ? & $)". iApply "HΦ". auto.
  Qed.

  Lemma wp_cas_fail_block_view E ℓ i q l Vℓ l1 v2 vVs :
    l ≠ l1 →
    lit_compare_safe l l1 →
    {{{
      ▷ ⌜vVs !! i = Some (#l, Vℓ)⌝ ∗
      ▷ ⎡ℓ *↦at{q}() vVs⎤
    }}}
      CAS #ℓ #i #l1 v2 @ E
    {{{
      RET #false;
      monPred_in Vℓ ∗
      ⎡ℓ *↦at{q}() vVs⎤
    }}}.
  Proof.
    iIntros (?? Φ) "[>Hlookup >Hℓ] HΦ" ; iDestruct "Hlookup" as %Hlookup.
    apply list_lookup_Z_lt_Some in Hlookup as Hi.
    iDestruct (at_block_accessor _ _ _ _ Hi with "Hℓ") as "Hacc".
    iDestruct "Hacc" as (??) "(Hlookup & Hℓi & Hclose)" ;
      iDestruct "Hlookup" as %Hlookup0 ;
      rewrite Hlookup in Hlookup0 ; injection Hlookup0 as <- <-.
    iApply (wp_cas_fail_view with "Hℓi");[done|done|]. iIntros "!> [??]". iApply "HΦ". iFrame.
    iSpecialize ("Hclose" $! #l Vℓ). rewrite list_insert_Z_id//.
    by iApply "Hclose".
  Qed.

(*
  (* ICFP20: This is the rule CAS-FAILURE-SC of the paper. *)
  Lemma wp_cas_fail E ℓ i q l l1 v2 :
    l ≠ l1 → lit_compare_safe l l1 →
    {{{ ▷ ⎡ℓ.[i]↦at{q}#l⎤ }}} CAS #ℓ #i #l1 v2 @ E {{{ RET #false; ⎡ℓ.[i]↦at{q}#l⎤ }}}.
  Proof.
    iIntros (?? Φ) "H HΦ". iApply (wp_cas_fail_view with "[$]")=>//.
    iIntros "!> [_ ?]". by iApply "HΦ".
  Qed.
*)

  Lemma wp_cas_suc_view E ℓ i l V1 V2 l1 v2 :
    l = l1 →
    lit_compare_safe l l1 →
    {{{
      monPred_in V1 ∗
      ▷ ⎡ℓ.[i]↦at(#l, V2)⎤
    }}}
      CAS #ℓ #i #l1 v2 @ E
    {{{
      RET #true;
      monPred_in V2 ∗
      ⎡ℓ.[i]↦at(v2, V2 ⊔ V1)⎤
    }}}.
  Proof.
    rewrite wp_eq. iStartProof (iProp _). iIntros (?? Φ ?) "H % -> HΦ".
    iIntros (V0) "-> #Hseen". iDestruct "H" as (->) "H". clear V1.
    iApply (wp_cas_suc_view_view_lang with "[$H $Hseen]")=>//.
    iNext. iIntros (V) "[[%%] [H $]]". iApply "HΦ". auto.
  Qed.

  Lemma wp_cas_suc_block_view E ℓ i l V1 V2 l1 v2 vVs :
    l = l1 →
    lit_compare_safe l l1 →
    {{{
      monPred_in V1 ∗
      ▷ ⌜vVs !! i = Some (#l, V2)⌝ ∗
      ▷ ⎡ℓ *↦at() vVs⎤
    }}}
      CAS #ℓ #i #l1 v2 @ E
    {{{
      RET #true;
      monPred_in V2 ∗
      ⎡ℓ *↦at() <[i := (v2, V2 ⊔ V1)]> vVs⎤
    }}}.
  Proof.
    iIntros (?? Φ) "(#? & >Hlookup & >Hℓ) HΦ" ; iDestruct "Hlookup" as %Hlookup.
    apply list_lookup_Z_lt_Some in Hlookup as Hi.
    iDestruct (at_block_accessor _ _ _ _ Hi with "Hℓ") as "Hacc".
    iDestruct "Hacc" as (??) "(Hlookup & Hℓi & Hclose)" ;
      iDestruct "Hlookup" as %Hlookup0 ;
      rewrite Hlookup in Hlookup0 ; injection Hlookup0 as <- <-.
    iApply (wp_cas_suc_view with "[$]");[done|done|]. iIntros "!> [??]". iApply "HΦ". iFrame.
    by iApply "Hclose".
  Qed.

(*
  (* ICFP20: This is the rule CAS-SUCCESS-SC of the paper. *)
  Lemma wp_cas_suc E ℓ i l l1 v2 :
    l = l1 → lit_compare_safe l l1 →
    {{{ ▷ ⎡ℓ.[i]↦at #l⎤ }}} CAS #ℓ #i #l1 v2 @ E {{{ RET #true; ⎡ℓ.[i]↦at v2⎤ }}}.
  Proof.
    iIntros (?? Φ) "H HΦ".
    iDestruct (monPred_in_intro True%I with "[//]") as (V) "[Hin _]".
    iApply (wp_cas_suc_view with "[$H $Hin]")=>//.
    iIntros "!> [_ ?]". iApply "HΦ". by rewrite -(_:∅⊑∅⊔V).
  Qed.
*)
End lifting_vprop.
