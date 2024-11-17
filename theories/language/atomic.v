From stdpp Require Import
  namespaces.

From iris.bi Require Import
  telescopes.
From iris.bi Require Export
  weakestpre.
From iris.bi.lib Require Export
  atomic.
From iris.proofmode Require Import
  tactics
  classes.
From iris.base_logic Require Import
  invariants.
From iris.proofmode Require Export
  string_ident.

From cosmo Require Import
  prelude.
From cosmo.language Require Export
  lifting
  weakestpre.

Definition atomic_wp `{!cosmoG Σ} {TA TB : tele}
  (e: expr) (* expression *)
  (Eo : coPset) (* (outer) mask *)
  (α: TA → vProp Σ) (* atomic pre-condition *)
  (β: TA → TB → vProp Σ) (* atomic post-condition *)
  (f: TA → TB → val) (* Turn the return data into the return value *)
  : vProp Σ :=
    (∀ (Φ : val → vProp Σ),
             atomic_update Eo ∅ α β (λ.. x y, Φ (f x y)) -∗
             WP e {{ Φ }})%I.
(* Note: To add a private postcondition, use
   atomic_update Eo Ei α β (λ x y, POST x y -∗ Φ (f x y)) *)

Notation "'<<<' ∀ x1 .. xn , α '>>>' e @ Eo '<<<' ∃ y1 .. yn , β , 'RET' v '>>>'" :=
  (atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             e%E
             Eo
             (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, α%I) ..)
             (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn,
                         tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                         (λ y1, .. (λ yn, β%I) .. )
                        ) .. )
             (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn,
                         tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                         (λ y1, .. (λ yn, v%V) .. )
                        ) .. )
  )
  (at level 20, Eo, α, β, v at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[hv' '<<<'  ∀  x1  ..  xn ,  α  '>>>'  '/  ' e  @  Eo  '/' '[    ' '<<<'  ∃  y1  ..  yn ,  β ,  '/' 'RET'  v  '>>>' ']' ']'")
  : bi_scope.

Notation "'<<<' ∀ x1 .. xn , α '>>>' e @ Eo '<<<' β , 'RET' v '>>>'" :=
  (atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleO)
             e%E
             Eo
             (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, α%I) ..)
             (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn,
                         tele_app (TT:=TeleO) β%I
                        ) .. )
             (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn,
                         tele_app (TT:=TeleO) v%V
                        ) .. )
  )
  (at level 20, Eo, α, β, v at level 200, x1 binder, xn binder,
   format "'[hv' '<<<'  ∀  x1  ..  xn ,  α  '>>>'  '/  ' e  @  Eo  '/' '[    ' '<<<'  β ,  '/' 'RET'  v  '>>>' ']' ']'")
  : bi_scope.

Notation "'<<<' α '>>>' e @ Eo '<<<' ∃ y1 .. yn , β , 'RET' v '>>>'" :=
  (atomic_wp (TA:=TeleO)
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             e%E
             Eo
             (tele_app (TT:=TeleO) α%I)
             (tele_app (TT:=TeleO) $
                       tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                         (λ y1, .. (λ yn, β%I) .. ))
             (tele_app (TT:=TeleO) $
                       tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                         (λ y1, .. (λ yn, v%V) .. ))
  )
  (at level 20, Eo, α, β, v at level 200, y1 binder, yn binder,
   format "'[hv' '<<<'  α  '>>>'  '/  ' e  @  Eo  '/' '[    ' '<<<'  ∃  y1  ..  yn ,  β ,  '/' 'RET'  v  '>>>' ']' ']'")
  : bi_scope.

Notation "'<<<' α '>>>' e @ Eo '<<<' β , 'RET' v '>>>'" :=
  (atomic_wp (TA:=TeleO)
             (TB:=TeleO)
             e%E
             Eo
             (tele_app (TT:=TeleO) α%I)
             (tele_app (TT:=TeleO) $ tele_app (TT:=TeleO) β%I)
             (tele_app (TT:=TeleO) $ tele_app (TT:=TeleO) v%V)
  )
  (at level 20, Eo, α, β, v at level 200,
   format "'[hv' '<<<' α '>>>' '/ ' e @ Eo '/' '[ ' '<<<' β , '/' 'RET' v '>>>' ']' ']'")
  : bi_scope.

Section lemmas.
  Context `{!cosmoG Σ} {TA TB : tele}.

  Notation vProp := (vProp Σ).

  Implicit Types (α : TA → vProp) (β : TA → TB → vProp) (f : TA → TB → val).

  Lemma atomic_wp_mask_weaken e Eo1 Eo2 α β f :
    Eo2 ⊆ Eo1 → atomic_wp e Eo1 α β f -∗ atomic_wp e Eo2 α β f.
  Proof.
    iIntros (HEo) "Hwp". iIntros (Φ) "AU". iApply "Hwp".
    iApply (atomic_update_mask_weaken with "AU"); last done.
  Qed.

  (*(1* Atomic triples imply sequential triples if the precondition is laterable. *1) *)
  (*Lemma atomic_wp_seq e Eo α β f {HL : ∀.. x, Laterable (α x)} : *)
  (*  atomic_wp e Eo α β f -∗ *)
  (*  ∀ Φ, ∀.. x, α x -∗ (∀.. y, β x y -∗ Φ (f x y)) -∗ WP e {{ Φ }}. *)
  (*Proof. *)
  (*  rewrite ->tforall_forall in HL. iIntros "Hwp" (Φ x) "Hα HΦ". *)
  (*  iApply wp_frame_wand_l. iSplitL "HΦ"; first iAccu. iApply "Hwp". *)
  (*  iAuIntro. iAaccIntro with "Hα"; first by eauto. iIntros (y) "Hβ !>". *)
  (*  (1* FIXME: Using ssreflect rewrite does not work, see Coq bug #7773. *1) *)
  (*  rewrite ->!tele_app_bind. iIntros "HΦ". iApply "HΦ". done. *)
  (*Qed. *)

  (*(1** This version matches the Texan triple, i.e., with a later in front of the *)
  (*[(∀.. y, β x y -∗ Φ (f x y))]. *1) *)
  (*Lemma atomic_wp_seq_step e Eo α β f {HL : ∀.. x, Laterable (α x)} : *)
  (*  TCEq (to_val e) None → *)
  (*  atomic_wp e Eo α β f -∗ *)
  (*  ∀ Φ, ∀.. x, α x -∗ ▷ (∀.. y, β x y -∗ Φ (f x y)) -∗ WP e {{ Φ }}. *)
  (*Proof. *)
  (*  iIntros (?) "H"; iIntros (Φ x) "Hα HΦ". *)
  (*  iApply (wp_step_fupd _ ⊤ _ (∀.. y : TB, β x y -∗ Φ (f x y))%I *)
  (*    with "[$HΦ //]"); try done; first by apply TCEq_eq. *)
  (*  (1* FIXME: use TCEq instead of eq *1) *)
  (*  iApply (atomic_wp_seq with "H Hα"); first done. *)
  (*  iIntros (y) "Hβ HΦ". by iApply "HΦ". *)
  (*Qed. *)

  (* Sequential triples with the empty mask for a physically atomic [e] are atomic. *)
  Lemma atomic_seq_wp_atomic e Eo α β f `{!AtomicExpr e} :
    (∀ Φ, ∀.. x, α x -∗ (∀.. y, β x y -∗ Φ (f x y)) -∗ WP e @ ∅ {{ Φ }}) -∗
    atomic_wp e Eo α β f.
  Proof.
    iIntros "Hwp" (Φ) "AU". iMod "AU" as (x) "[Hα [_ Hclose]]".
    iApply ("Hwp" with "Hα"). iIntros (y) "Hβ".
    iMod ("Hclose" with "Hβ") as "HΦ".
    rewrite ->!tele_app_bind. iApply "HΦ".
  Qed.

  (* Sequential triples with a persistent precondition and no initial quantifier
  are atomic. *)
  Lemma persistent_seq_wp_atomic e Eo (α : [tele] → vProp) (β : [tele] → TB → vProp)
        (f : [tele] → TB → val) {HP : Persistent (α [tele_arg])} :
    (∀ Φ, α [tele_arg] -∗ (∀.. y, β [tele_arg] y -∗ Φ (f [tele_arg] y)) -∗ WP e {{ Φ }}) -∗
    atomic_wp e Eo α β f.
  Proof.
    simpl in HP. iIntros "Hwp" (Φ) "HΦ". iApply fupd_wp.
    iMod ("HΦ") as "[#Hα [Hclose _]]". iMod ("Hclose" with "Hα") as "HΦ".
    iApply wp_fupd. iApply ("Hwp" with "Hα"). iIntros "!>" (y) "Hβ".
    iMod ("HΦ") as "[_ [_ Hclose]]". iMod ("Hclose" with "Hβ") as "HΦ".
    (* FIXME: Using ssreflect rewrite does not work, see Coq bug #7773. *)
    rewrite ->!tele_app_bind. done.
  Qed.

  (* We can open invariants around atomic triples.
     (Just for demonstration purposes; we always use [iInv] in proofs.) *)
  Lemma wp_atomic_inv_iProp e Eo α β f N (I : iProp Σ) :
    ↑N ⊆ Eo →
    atomic_wp e Eo (λ.. x, ⎡▷ I⎤ ∗ α x) (λ.. x y, ⎡▷ I⎤ ∗ β x y) f -∗
    ⎡inv N I⎤ -∗ atomic_wp e (Eo ∖ ↑N) α β f.
  Proof.
    intros ?. iIntros "Hwp #Hinv" (Φ) "AU". iApply "Hwp". iAuIntro.
    iInv N as "HI". iApply (aacc_aupd with "AU"); first done.
    iIntros (x) "Hα". iAaccIntro with "[HI Hα]"; rewrite ->!tele_app_bind; first by iFrame.
    - (* abort *)
      iIntros "[HI $]". by eauto with iFrame.
    - (* commit *)
      iIntros (y). rewrite ->!tele_app_bind. iIntros "[HI Hβ]". iRight.
      iExists y. rewrite ->!tele_app_bind. by eauto with iFrame.
  Qed.
End lemmas.
