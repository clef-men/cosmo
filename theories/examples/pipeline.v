From iris.algebra Require Import
  excl_auth
  csum
  numbers
  list.
From iris.base_logic Require Import
  invariants.

From cosmo Require Import
  prelude.
From cosmo.common Require Import
  list.
From cosmo.language Require Export
  proofmode
  atomic.
From cosmo.examples Require
  bounded_queue.

Set Default Proof Using "Type".

Open Scope Z.

(** Implementation **)

Section pipeline.
  Context (capacity : nat) (capacity_min : capacity ≥ 1).

  (*
     ICFP21: Here is a simple client code that makes use of the data structure
     defined in bounded_queue.v. It corresponds to the code listings in Figure 11
     of the paper (except that functions `pipef` and `pipeg` have been inlined).
   *)

  Definition pipeline : val := λ: "f" "g" "xs",
    let: "q" := (bounded_queue.make capacity) #() in
    let: "n" := Length "xs" in
    Fork (
      for: "i" from #0 to "n" - #1 do
        let: "x" := Read NonAtomic "xs" "i" in
        let: "y" := "f" "x" in
        (bounded_queue.enqueue capacity) "q" "y"
      enddo
    ) ;;
    let: "zs" := Alloc NonAtomic "n" #() in
    for: "i" from #0 to "n" - #1 do
      let: "y" := (bounded_queue.dequeue capacity) "q" in
      let: "z" := "g" "y" in
      Write NonAtomic "zs" "i" "z"
    enddo ;;
    "zs".

  (** Specification **)

  Class pipelineG Σ := {
    (* the shared queue: *)
    #[local] pipelineG_queue :: (bounded_queue.queueG capacity capacity_min) Σ ;
    (* both cursors: *)
    #[local] pipelineG_cur :: inG Σ (excl_authR natO) ;
  }.

  Section Spec.
    Context `{!cosmoG Σ, !pipelineG Σ}.

    Implicit Types (γqueue γcur_f γcur_g : gname) (q : val) (i cur_f cur_g : nat).
    Implicit Types (f g : val).
    Implicit Types (R : nat → val → vProp Σ).
    Implicit Types (xs_array zs_array : location).
    Implicit Types (x y z : val) (xs zs : list val).
    Implicit Types (V : view) (yV : val * view) (yVs : list (val * view)).

    Open Scope Z.

    Definition pipelineN : namespace :=
      nroot .@ "pipeline".

    Notation seq' a b := (seq a%nat (b - a)%nat).

    (*
      ICFP21: Here is the internal invariant of the pipeline, as described in
      Figure 13 of the paper.

      “pipeline_proto” is what the paper calls “PipeInvInner”.
      “f_thread” is what the paper calls “PipeF”.
      “g_thread” is what the paper calls “PipeG”.
      “cur_f” is what the paper calls “n<sub>f</sub>”.
      “cur_g” is what the paper calls “n<sub>g</sub>”.
     *)

    Definition pipeline_proto f g R xs γqueue γcur_f γcur_g : iProp Σ := (
      ∃ yVs cur_f cur_g Vt Vh,
          (bounded_queue.is_queue capacity capacity_min) γqueue Vt Vh yVs
        ∗ own γcur_f (●E cur_f)
        ∗ own γcur_g (●E cur_g)
        ∗ ⌜cur_g ≤ cur_f⌝
        ∗ ⌜length yVs = (cur_f - cur_g)%nat⌝
        ∗ [∗ list] i↦yV ∈ yVs, let '(y, V) := yV in
            WP g (Val y) {{ λ z, R (i + cur_g)%nat z }} V
    )%I.

    Definition f_thread f g R xs xs_array γcur_f cur_f : vProp Σ := (
        ⎡own γcur_f (◯E cur_f)⎤
      ∗ xs_array *↦ xs
      ∗ ⌜cur_f ≤ length xs⌝
      ∗ [∗ list] i↦x ∈ drop cur_f xs,
          WP f (Val x) {{ λ y, WP g y {{ λ z, R (i + cur_f)%nat z }} }}
    )%I.

    Definition g_thread f g R xs zs_array zs γcur_g cur_g : vProp Σ := (
        ⎡own γcur_g (◯E cur_g)⎤
      ∗ ⌜cur_g ≤ length xs⌝
      ∗ zs_array *↦ zs
      ∗ ⌜length zs = length xs⌝
      ∗ [∗ list] i↦z ∈ take cur_g zs, R i z
    )%I.

    (*
      ICFP21: Here is the spec of the pipeline, as shown in Figure 12 of the paper,
      along with its proof.
    *)

    Theorem pipeline_spec f g R xs xs_array :
      {{{
          xs_array *↦ xs
        ∗ ⎡has_length xs_array (length xs)⎤
        ∗ [∗ list] i↦x ∈ xs,
            WP f (Val x) {{ λ y, WP g y {{ λ z, R i z }} }}
      }}}
          pipeline f g #xs_array
      {{{ zs_array zs, RET #zs_array ;
          zs_array *↦ zs
        ∗ ⌜length zs = length xs⌝
        ∗ [∗ list] i↦z ∈ zs, R i z
      }}}.
    Proof using All.
      iIntros (Φ) "(Hxs & Hlen & HR) HΦ".
      wp_lam; wp_let.
      wp_apply (bounded_queue.make_spec capacity capacity_min) ; first solve_monPred_in.
      iIntros (q γqueue) "[#Hqueue_inv Hqueue]".
      (* create ghost variables *)
      iMod (own_alloc (●E 0%nat ⋅ ◯E 0%nat)) as (γcur_f) "[Hγcur_f● Hγcur_f◯]".
      { by apply auth_both_valid_discrete. }
      iMod (own_alloc (●E 0%nat ⋅ ◯E 0%nat)) as (γcur_g) "[Hγcur_g● Hγcur_g◯]".
      { by apply auth_both_valid_discrete. }
      (* create invariant *)
      iMod (inv_alloc pipelineN _ (pipeline_proto f g R xs γqueue γcur_f γcur_g)
            with "[Hqueue Hγcur_f● Hγcur_g●]")  as "#I".
      { rewrite /pipeline_proto. repeat (iExists _). iFrame. by cbn. }
      (* fork *)
      wp_apply (wp_length with "Hlen").
      wp_apply (wp_fork with "[Hxs HR Hγcur_f◯]").
      {
        iAssert (f_thread f g R _ _ _ _) with "[$Hγcur_f◯ $Hxs HR]" as "F".
        { setoid_rewrite Nat.add_0_r. iFrame "HR". iPureIntro ; lia. }
        rewrite (_ : #0 = #0%nat) // ; set cur_f := 0%nat ; clearbody cur_f.
        iIntros "!>". wp_pures. iLöb as "IH" forall (cur_f).
        wp_pures. case_bool_decide; wp_pures; [|done].
        iDestruct "F" as "(Hγcur_f◯ & Hxs & _ & Hfwps)".
        wp_read_na_block as xs_cur_f EQxs. wp_pures.
        apply list_lookup_Z_Some_to_nat in EQxs. rewrite Nat2Z.id in EQxs.
        erewrite drop_S; [|done]. iDestruct "Hfwps" as "[Hfwp Hfwps]".
        wp_bind (f xs_cur_f). iApply (wp_wand with "Hfwp"). iIntros (y) "Hgwp". wp_pures.
        iDestruct (monPred_in_intro with "Hgwp") as (Vgwp) "[#HVgwp Hgwp]".
        iDestruct (bi.later_intro with "Hgwp") as "Hgwp". (* Make laterable. *)
        awp_apply (bounded_queue.enqueue_spec _ _ (↑pipelineN) with "Hqueue_inv HVgwp")
          without "Hfwps"; [solve_ndisj|] .
        iInv "I" as (yVs cur_f' cur_g Vt Vh) "(>Hq & >Hγcur_f● & >Hγcur_g● & >% & >% & Hgwps)".
        iDestruct (own_valid_2 with "Hγcur_f● Hγcur_f◯") as %->%excl_auth_agree_L.
        iAaccIntro with "Hq".
        { (* Abort *) iIntros "Hq !>". iFrame. iExists _, _, _, _, _. iFrame. auto. }
        (* Commit *)
        iIntros "[Hq _]".
        iMod (own_update_2 with "Hγcur_f● Hγcur_f◯") as "[Hγcur_f● Hγcur_f◯]".
        { apply (excl_auth_update _ _ (S cur_f)). }
        iSplitR "Hxs Hγcur_f◯".
        - iExists _, _, _, _, _. iFrame "Hγcur_f● Hγcur_g● Hq".
          rewrite big_sepL_app app_length /=
                  (_ : (length yVs + 0 + cur_g = cur_f)%nat); [|lia].
          rewrite -embed_later /=. iFrame. auto with lia.
        - iIntros "!> Hfwps". wp_pures. rewrite (_ : cur_f + 1 = S cur_f); [|lia].
          iApply "IH". iFrame. iSplitR; [auto with lia|].
          by setoid_rewrite Nat.add_succ_comm.
      }
      {
        wp_alloc zs_array as "Hzs". iSpecialize ("HΦ" $! zs_array).
        iAssert (g_thread f g R xs _ _ _ _) with "[$Hγcur_g◯ $Hzs]" as "G".
        { rewrite /take/= replicate_length. iPureIntro ; lia. }
        generalize (replicate (Z.to_nat (length xs)) #())=>zs. wp_let.
        rewrite (_ : #0 = #0%nat) // ; set cur_g := 0%nat ; clearbody cur_g.
        wp_pures. iLöb as "IH" forall (cur_g zs).
        case_bool_decide; wp_pures; last first.
        { iApply "HΦ". iDestruct "G" as "(_ & % & $ & % & HR)". iFrame "%".
          rewrite take_ge //. lia. }
        iDestruct "G" as "(Hγcur_g◯ & _ & Hzs & % & HR)".
        awp_apply (bounded_queue.dequeue_spec _ _ (↑pipelineN) with "Hqueue_inv []")
          without "HR HΦ"; [solve_ndisj|by iApply monPred_in_bot|].
        iInv "I" as (yVs cur_f cur_g' Vt Vh) "(>Hq & >Hγcur_f● & >Hγcur_g● & >% & >% & Hgwps)".
        iDestruct (own_valid_2 with "Hγcur_g● Hγcur_g◯") as %->%excl_auth_agree_L.
        iAaccIntro with "Hq".
        { (* Abort *) iIntros "Hq". iFrame. iExists _, _, _, _, _. iFrame. auto. }
        (* Commit *)
        iIntros ([y Vy] yVs') "(-> & Hq & _ & #HVy) /=".
        iMod (own_update_2 with "Hγcur_g● Hγcur_g◯") as "[Hγcur_g● Hγcur_g◯]".
        { apply (excl_auth_update _ _ (S cur_g)). }
        iDestruct "Hgwps" as "[Hgwp Hgwps]".
        iModIntro. iSplitR "Hzs Hγcur_g◯ Hgwp".
        - iExists _, _, _, _, _. iFrame "Hq Hγcur_f● Hγcur_g●".
          do 2 (iSplitR; [iPureIntro; simpl in *; lia|]).
          do 2 iModIntro. iApply (big_sepL_impl with "Hgwps").
          iIntros "!>" (k [??] ?). rewrite Nat.add_succ_r. auto.
        - iIntros "[HR HΦ]". wp_pures. iDestruct (monPred_in_elim with "HVy Hgwp") as "Hgwp".
          wp_bind (g y). iApply (wp_wand with "Hgwp"). iIntros (z) "Hz". wp_pures.
          wp_write_na_block. wp_pures.
          rewrite (_ : cur_g + 1 = S cur_g); [|lia].
          iApply ("IH" with "HΦ"). iFrame.
          rewrite list_insert_Z_to_nat; [|lia]. rewrite Nat2Z.id.
          iSplitR; [iPureIntro; lia|]. iSplitR; [by rewrite insert_length|].
          erewrite take_S_r; [|apply list_lookup_insert; lia].
          rewrite big_sepL_app /= take_insert; [|done]. iFrame.
          rewrite take_length Nat.min_l; [|lia]. by rewrite 2!right_id. }
    Qed.
  End Spec.
End pipeline.
