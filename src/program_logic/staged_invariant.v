From iris.algebra Require Import gmap auth agree gset coPset excl csum.
From iris.base_logic.lib Require Export fancy_updates.
From stdpp Require Export namespaces.
From iris.base_logic.lib Require Import wsat invariants saved_prop gen_heap.
From iris.proofmode Require Import tactics.
From Perennial.program_logic Require Export step_fupd_extra crash_token ghost_var.
From Perennial.algebra Require Import partition gen_heap big_op.
Set Default Proof Using "Type".
Import uPred.

Class stagedG (Σ : gFunctors) : Set := WsatG {
  staging_saved_inG :> savedPropG Σ;
  staging_auth_inG :> inG Σ (authR (optionUR (exclR (prodO (boolO) (prodO gnameO gnameO)))));
  staging_shot_inG :> inG Σ (csumR (exclR unitO) (agreeR unitO));
  staging_gnames_inG :> gen_heapPreG nat () Σ;
  staging_bunches_inG :> partition_preG nat nat Σ
}.

Definition staged_pending `{stagedG Σ} (γ: gname) : iProp Σ :=
  own γ (Cinl (Excl ())).
Definition staged_done `{stagedG Σ} (γ: gname) : iProp Σ :=
  own γ (Cinr (to_agree ())).

Record staged_names :=
  { staging_gnames_names : gen_heap_names;
    staging_bunches_names : gen_heap_names }.

Section definitions.
Context `{!invG Σ, !stagedG Σ, !crashG Σ}.

Context (Γ: staged_names).

Instance sghG : gen_heapG nat () Σ :=
  gen_heapG_update_pre (staging_gnames_inG) (staging_gnames_names Γ).

Instance staged_bunches_partitionG : partitionG nat nat Σ :=
  {| partition_heap_inG := gen_heapG_update_pre (partition_heap_preG) (staging_gnames_names Γ) |}.

Notation sphG := (@partition_heap_inG _ _ _ _ _ _ _ _ _ staged_bunches_partitionG).

Definition pN := nroot.@"pending".
Definition cN := nroot.@"crash".
Definition bN := nroot.@"bunchstore".

Definition crash_prop_wf (σdom: gmap nat unit) Qc :=
  ([∗ map] i↦_ ∈ σdom, ∃ (γ: gname), meta (hG := sghG) i cN γ ∗ saved_prop_own γ (Qc i))%I.

Definition bunch_wf k E E' (Ps Pr Qc: nat → iProp Σ) i bunch :=
  (∃ (γ: gname) (b: bool) γprop_stored γprop_remainder, meta (hG := sphG) i bN γ ∗
     own γ (● Excl' (b, (γprop_stored, γprop_remainder))) ∗
     saved_prop_own γprop_stored (Ps i) ∗
     saved_prop_own γprop_remainder (Pr i) ∗
     □ (C -∗ (Ps i) -∗ if b then |={E, E'}_k=> ([∗ set] j∈bunch, (Qc j)) ∗ (Pr i)
                            else ([∗ set] j∈bunch, (Qc j)) ∗ (Pr i)))%I.

Definition bunches_wf k E E' σ (Ps Pr Qc: nat → iProp Σ) :=
  ([∗ map] i↦bunch ∈ σ, bunch_wf k E E' Ps Pr Qc i bunch)%I.

Definition inv_live (σ: gmap nat (gset nat)) (Ps: nat → iProp Σ) :=
  ([∗ map] i↦_∈ σ, Ps i)%I.

Definition inv_crashed (σ: gmap nat (gset nat)) (σdom: gmap nat unit) (Ps Pr Qc: nat → iProp Σ) :=
  (C ∗ [∗ map] i↦bunch∈ σ, Pr i ∗ ([∗ set] j ∈ bunch, ∃ γ, meta (hG := sghG) j pN γ ∗ (Qc j ∨ staged_done γ)))%I.

Definition staged_inv (N: namespace) (k: nat) (E E': coPset) : iProp Σ :=
  (inv N (∃ σ σdom  (Ps Pr Qc: nat → iProp Σ),
             ⌜ dom (gset nat) σdom = union_partition σ ⌝ ∗
             partition_ctx σ ∗
             gen_heap_ctx σdom ∗
             crash_prop_wf σdom Qc ∗
             bunches_wf k E E' σ Ps Pr Qc ∗
             (inv_live σ Ps ∨ inv_crashed σ σdom Ps Pr Qc)))%I.

(*
Definition staged_inv `{!invG Σ, !crashG Σ, !stagedG Σ} (N: namespace)(L: Type) `{Countable L}
           k E E' (γ γ': gname) (Qc: L → iProp Σ) : iProp Σ :=
  (inv N (∃ γprop_stored γprop_remainder Ps Pr,
             own γ (● Excl' (γprop_stored, γprop_remainder)) ∗
             saved_prop_own γprop_stored Ps ∗
             saved_prop_own γprop_remainder Pr ∗
             □ (C -∗ Ps -∗ |={E, E'}_k=> Qc ∗ Pr) ∗
             (Ps ∨ (Pr ∗ C ∗ staged_done γ'))))%I.
*)

Definition staged_bundle (Q Q': iProp Σ) b (bundle: gset nat) : iProp Σ :=
  (∃ i γ γprop γprop' Qalt Qalt',
      mapsto (hG := sphG) i 1 bundle ∗
      meta (hG := sphG) i bN γ ∗
      own γ (◯ Excl' (b, (γprop, γprop'))) ∗
      ▷ (Q ≡ Qalt) ∗ ▷ (Q' ≡ Qalt') ∗
      saved_prop_own γprop Qalt ∗
      saved_prop_own γprop' Qalt').

Definition staged_crash (i: nat) (P: iProp Σ) : iProp Σ :=
  (∃ γ, meta (hG := sghG) i cN γ ∗ saved_prop_own γ P).

Definition staged_crash_pending (i: nat) : iProp Σ :=
  (∃ γ, meta (hG := sghG) i pN γ ∗ staged_pending γ).

Definition bunch_wf_later k E E' (Ps Pr Qc: nat → iProp Σ) i bunch :=
  (∃ (γ: gname) (b: bool) γprop_stored γprop_remainder, meta (hG := sphG) i bN γ ∗
     own γ (● Excl' (b, (γprop_stored, γprop_remainder))) ∗
     ▷ saved_prop_own γprop_stored (Ps i) ∗
     ▷ saved_prop_own γprop_remainder (Pr i) ∗
     ▷ □ (C -∗ (Ps i) -∗ if b then |={E, E'}_k=> ([∗ set] j∈bunch, (Qc j)) ∗ (Pr i)
                         else ([∗ set] j ∈ bunch, Qc j) ∗ (Pr i)))%I.

Definition bunches_wf_later k E E' σ (Ps Pr Qc: nat → iProp Σ) :=
  ([∗ map] i↦bunch ∈ σ, bunch_wf_later k E E' Ps Pr Qc i bunch)%I.

Lemma bunches_wf_to_later k E E' σ Ps Pr Qc Em:
  ▷ bunches_wf k E E' σ Ps Pr Qc ={Em}=∗
  bunches_wf_later k E E' σ Ps Pr Qc.
Proof.
  iIntros "Hb". rewrite /bunches_wf.
  iDestruct (big_sepM_later with "Hb") as "Hb".
  iApply big_sepM_fupd.
  iApply (big_sepM_mono with "Hb").
  iIntros (???) "H".
  iDestruct "H" as (????) "H".
  iDestruct "H" as "(>Hm&>Hown&Hsaved1&Hsaved2&Hwand)".
  iModIntro. iExists _, _, _, _. iFrame.
Qed.

Implicit Types N : namespace.
Implicit Types P Q R : iProp Σ.

Global Instance staged_persistent N k E E': Persistent (staged_inv N k E E').
Proof. rewrite /staged_inv. apply _. Qed.

Lemma pending_done γ: staged_pending γ -∗ staged_done γ -∗ False.
Proof.
  rewrite /staged_pending/staged_done.
  iIntros "H H'".
  { by iDestruct (own_valid_2 with "H H'") as %?. }
Qed.

Lemma pending_upd_done γ: staged_pending γ ==∗ staged_done γ.
Proof.
  rewrite /staged_pending/staged_done.
  iIntros "H". iMod (own_update with "H") as "$".
  { by apply cmra_update_exclusive. }
  done.
Qed.

Lemma pending_alloc:
  (|==> ∃ γ, staged_pending γ)%I.
Proof.
  iApply (own_alloc (Cinl (Excl ()))).
  { econstructor. }
Qed.

(*
Lemma staged_inv_alloc N k E E':
  (|={E}=> staged_inv N k E' E')%I.
Proof.
  iMod (saved_prop_alloc Q) as (γprop) "#Hsaved".
  iMod (saved_prop_alloc Qr) as (γprop') "#Hsaved'".
  iMod (own_alloc (● (Excl' (γprop, γprop')) ⋅ ◯ (Excl' (γprop, γprop')))) as (γ) "[H1 H2]".
  { apply auth_both_valid_2; [econstructor | reflexivity]. }
  iMod (pending_alloc) as (γ') "H".
  iIntros "(HQ&#HQP)".
  iMod (inv_alloc N E _ with "[HQ H1]") as "HI"; last first.
  { iModIntro. iExists γ, γ'. iFrame "H". iSplitL "HI".
    - iApply "HI".
    - iExists γprop, γprop'. iFrame. iFrame "#".
  }
  iNext. iExists γprop, γprop', Q, Qr. iFrame. iFrame "#".
  iAlways. iIntros. iApply step_fupdN_inner_later; auto; iNext.
  iApply "HQP"; by iFrame.
Qed.
*)

Lemma staged_inv_alloc N k E E' P Q Qr:
  ↑N ⊆ E →
  staged_inv N k E' E' ∗
  ▷ Q ∗ □ (C -∗ Q -∗ P ∗ Qr) ={E}=∗
  ∃ i, staged_bundle Q Qr false {[i]} ∗ staged_crash i P ∗ staged_crash_pending i.
Proof.
  iIntros (?) "(Hinv&HQ&#HQP)".
  iInv "Hinv" as "H" "Hclo".
  iDestruct "H" as (σ σdom Qs Qsr Pc) "(>Hdom&>Hpart&>Hheap&Hcrash_wf&Hbunch_wf&Hstatus)".
  iDestruct "Hdom" as %Hdom.
  iMod (partition_alloc with "Hpart") as (bid i Hnotin1 Hnotin2) "(Hpart&Hbundle&Hbundle_meta)".
  iMod (saved_prop_alloc Q) as (γprop) "#Hsaved".
  iMod (saved_prop_alloc Qr) as (γprop') "#Hsaved_rem".
  iMod (own_alloc (● (Excl' (false, (γprop, γprop'))) ⋅ ◯ (Excl' (false, (γprop, γprop'))))) as (γ) "[H1 H2]".
  { apply auth_both_valid_2; [econstructor | reflexivity]. }
  iMod (meta_set ⊤ bid γ bN with "Hbundle_meta") as "#HbidN"; first by set_solver.
  rewrite -Hdom in Hnotin2.
  assert (σdom !! i = None) as Hin3.
  { by eapply not_elem_of_dom in Hnotin2. }
  iMod (gen_heap_alloc σdom i () with "Hheap") as "(Hheap&_&Hi_meta)"; first auto.
  iMod (pending_alloc) as (γp) "Hpend".
  iDestruct (meta_token_difference i (↑pN) ⊤ with "Hi_meta") as "(HipN&Hi_meta)".
  { set_solver. }
  iMod (meta_set _ i γp pN with "HipN") as "#HipN"; first by set_solver.
  iMod (saved_prop_alloc P) as (γcrash) "#Hsaved_crash".
  iMod (meta_set _ i γcrash cN with "Hi_meta") as "#HicN"; first by solve_ndisj.
  iMod ("Hclo" with "[-Hbundle H2 Hpend]").
  { iNext.
    iExists _, _, (λ k, if decide (k = bid) then Q else (Qs k)),
                  (λ k, if decide (k = bid) then Qr else (Qsr k)),
                  (λ k, if decide (k = i) then P else (Pc k)).
    iFrame.
    iSplitL "".
    { iPureIntro. rewrite dom_insert_L /union_partition.
      rewrite Hdom map_fold_insert; [ auto | set_solver |].
      eauto.
    }
    iSplitL "Hcrash_wf".
    {
      rewrite /crash_prop_wf.
      iApply (big_sepM_insert); first auto.
      iSplitL "".
      { iExists _. destruct (decide (i = i)) => //=. iFrame "#". }
      iApply (big_sepM_mono with "Hcrash_wf").
      { iIntros (k' [] ?) "H". destruct (decide (k' = i)); first by congruence.
        eauto. }
    }
    iSplitL "Hbunch_wf H1".
    { iApply (big_sepM_insert); first auto.
      iSplitL "H1".
      { iExists _, _, _, _. iFrame.
        rewrite ?decide_True //.
        iFrame "#".
        iAlways. iIntros.
        rewrite big_opS_singleton.
        rewrite decide_True //. by iApply "HQP".
      }
      iApply (big_sepM_mono with "Hbunch_wf").
      { iIntros (k' [] ?) "H".
        iDestruct "H" as (? b ??) "(?&?&?&?&#Hwand)".
        iExists _, _, _, _. iFrame.
        destruct (decide (k' = bid)); first by congruence.
        iFrame; iAlways. iIntros "? ?". iSpecialize ("Hwand" with "[$] [$]").
        destruct b.
        * iApply (step_fupdN_inner_wand with "Hwand"); auto.
         iApply sep_mono_l.
         iApply big_sepS_mono.
         iIntros (i' Hin') "HPc".
         destruct (decide (i' = i)); try iFrame.
         subst.
         exfalso. eapply not_elem_of_union_partition in Hin'; auto.
         { erewrite <-Hdom. eauto. }
         { eauto. }
        * iDestruct "Hwand" as "(Hwand&$)".
         iApply (big_sepS_mono with "Hwand").
         iIntros (i' Hin') "HPc".
         destruct (decide (i' = i)); try iFrame.
         subst.
         exfalso. eapply not_elem_of_union_partition in Hin'; auto.
         { erewrite <-Hdom. eauto. }
         { eauto. }
      }
    }
    iDestruct "Hstatus" as "[Hlive|(#HC&Hcrashed)]".
    - iLeft. rewrite /inv_live.
      iApply big_sepM_insert; auto.
      rewrite decide_True //; iFrame.
      iApply (big_sepM_mono with "Hlive").
      iIntros (k' x' Hin') "HQ".
      rewrite decide_False; last by congruence.
      eauto.
    - iRight. rewrite /inv_crashed.
      iFrame "HC".
      iApply big_sepM_insert; auto.
      rewrite decide_True //; iFrame.
      iSplitL "HQ".
      {
        rewrite big_opS_singleton. iDestruct ("HQP" with "[$] [$]") as "(HP&$)".
        iExists _. iFrame "#". rewrite decide_True //. by iLeft.
      }
      iApply (big_sepM_mono with "Hcrashed").
      iIntros (k' x' Hin') "(?&HQ)".
      rewrite decide_False; last by congruence.
      iFrame.
      iApply (big_sepS_mono with "HQ").
      iIntros (i' Hin'') "HPc".
      destruct (decide (i' = i)); try iFrame.
      subst.
      exfalso. eapply not_elem_of_union_partition in Hin'; eauto.
      { erewrite <-Hdom. eauto. }
  }
  iModIntro. iExists _.
  iSplitL "Hbundle H2".
  { iExists _, _, _, _, Q, Qr. iFrame. iFrame "#". eauto. }
  iSplitL "".
  { iExists _. iFrame "#". }
  iExists _. iFrame. iFrame "#".
Qed.

Lemma staged_inv_join N k E E' Q1 Qr1 Q2 Qr2 s1 s2:
  ↑N ⊆ E →
  staged_inv N k E' E' ∗
  staged_bundle Q1 Qr1 false s1 ∗
  staged_bundle Q1 Qr2 false s2
  ={E}=∗
  staged_bundle (Q1 ∗ Q2) (Qr1 ∗ Qr2) false (s1 ∪ s2).
Proof.
  iIntros (?) "(Hinv&Hb1&Hb2)".
  rewrite /staged_bundle.
  iDestruct "Hb1" as (bid1 γ1 γprop1 γprop1' Q1alt Qr1alt)
                       "(Hbid1&#Hb_meta1&Hown1&#Hequiv1&#Hequiv1_alt&#Hsaved1&#Hsavedr1)".
  iDestruct "Hb2" as (bid2 γ2 γprop2 γprop2' Q2alt Qr2alt)
                       "(Hbid2&#Hb_meta2&Hown2&#Hequiv2&#Hequiv2_alt&#Hsaved2&#Hsavedr2)".
  iInv "Hinv" as "H" "Hclo".
  iDestruct "H" as (σ σdom Qs Qsr Pc) "(>Hdom&>Hpart&>Hheap&Hcrash_wf&Hbunch_wf&Hstatus)".
  iDestruct "Hdom" as %Hdom.
  iDestruct (gen_heap_valid with "[Hpart] Hbid1") as %Hin1.
  { iDestruct "Hpart" as "(?&$)". }
  iDestruct (gen_heap_valid with "[Hpart] Hbid2") as %Hin2.
  { iDestruct "Hpart" as "(?&$)". }
  iDestruct (partition_valid_disj with "Hpart Hbid1 Hbid2") as %[Hdisj Hneq].
  iMod (partition_join with "Hpart Hbid2 Hbid1") as "(Hpart&Hbid2&Hbid1)".

  iMod (saved_prop_alloc (Qs bid1 ∗ Qs bid2)) as (γprop1_new) "#Hsaved1_new".
  iMod (saved_prop_alloc (Qsr bid1 ∗ Qsr bid2)) as (γprop1'_new) "#Hsavedr1_new".
  iMod (saved_prop_alloc True) as (γprop2_new) "#Hsaved2_new".
  iMod (saved_prop_alloc True) as (γprop2'_new) "#Hsavedr2_new".

  iMod (bunches_wf_to_later with "Hbunch_wf") as "Hbunch_wf".

  set (Qs' := (λ k, if decide (k = bid1) then (Qs bid1 ∗ Qs bid2)%I else
                    if decide (k = bid2) then True%I else
                    Qs k)).
  set (Qsr' := (λ k, if decide (k = bid1) then (Qsr bid1 ∗ Qsr bid2)%I else
                    if decide (k = bid2) then True%I else
                    Qsr k)).
  iAssert (|==> bunches_wf_later k E' E' (<[bid2:=∅]> (<[bid1:=s1 ∪ s2]> σ)) Qs' Qsr' Pc ∗
                ▷ saved_prop_own γprop1 (Qs bid1) ∗
                ▷ saved_prop_own γprop1' (Qsr bid1) ∗
                ▷ saved_prop_own γprop2 (Qs bid2) ∗
                ▷ saved_prop_own γprop2' (Qsr bid2) ∗
                own γ1 (◯ Excl' (false, (γprop1_new, γprop1'_new))) ∗
                own γ2 (◯ Excl' (false, (γprop2_new, γprop2'_new))))%I with "[Hbunch_wf Hown1 Hown2]"
         as ">(Hbunches&#Hsaved1'&#Hsavedr1'&#Hsaved2'&#Hsavedr2'&Hown1&Hown2)".
  { rewrite /bunches_wf_later big_sepM_insert_delete.
    iDestruct (big_sepM_delete with "Hbunch_wf") as "(Hbid2_bunch&Hbunch_wf)"; first eapply Hin2.
    iAssert (|==> bunch_wf_later k E' E' Qs' Qsr' Pc bid2 ∅ ∗
                  ▷ saved_prop_own γprop2 (Qs bid2) ∗
                  ▷ saved_prop_own γprop2' (Qsr bid2) ∗
                  own γ2 (◯ Excl' (false, (γprop2_new, γprop2'_new))) ∗
                  ▷ □ (C -∗ Qs bid2 -∗ ([∗ set] j ∈ s2, Pc j) ∗ Qsr bid2))%I
      with "[Hbid2_bunch Hown2]" as ">($&$&$&$&#Hwand2)".
    {
      iDestruct "Hbid2_bunch" as (????) "(Hm2&Hown_auth2&Hs2&Hsr2&#Hwand2)".
      iDestruct (meta_agree with "Hb_meta2 Hm2") as %<-.
      unify_ghost.
      iMod (ghost_var_update γ2 (false, (γprop2_new, γprop2'_new)) with "[$] [$]") as "(Hown_auth2&$)".
      iModIntro. rewrite /bunch_wf_later. iFrame "#". iFrame. iExists _, _, _, _. iFrame.
      rewrite /Qs'/Qsr'.
      destruct (decide (bid2 = bid1)) => //=.
      rewrite ?decide_True //. iFrame "#".
      iNext. iAlways. iIntros "#HC _".
      rewrite big_sepS_empty //=.
    }

    iDestruct (big_sepM_delete _ _ bid1 with "Hbunch_wf") as "(Hbid1_bunch&Hbunch_wf)".
    { rewrite lookup_delete_ne //. }
    iAssert (|==> bunch_wf_later k E' E' Qs' Qsr' Pc bid1 (s1 ∪ s2) ∗
                  ▷ saved_prop_own γprop1 (Qs bid1) ∗
                  ▷ saved_prop_own γprop1' (Qsr bid1) ∗
                  own γ1 (◯ Excl' (false ,(γprop1_new, γprop1'_new))) ∗
                  ▷ □ (C -∗ Qs bid1 -∗ ([∗ set] j ∈ s1, Pc j) ∗ Qsr bid1))%I
      with "[Hbid1_bunch Hown1]" as ">(?&$&$&$&Hwand1)".
    {
      iDestruct "Hbid1_bunch" as (????) "(Hm1&Hown_auth1&Hs1&Hsr1&#Hwand1)".
      iDestruct (meta_agree with "Hb_meta1 Hm1") as %<-.
      unify_ghost.
      iMod (ghost_var_update γ1 (false, (γprop1_new, γprop1'_new)) with "[$] [$]") as "(Hown_auth1&$)".
      iModIntro. rewrite /bunch_wf_later. iFrame "#". iFrame. iExists _, _, _, _. iFrame.
      rewrite /Qs'/Qsr'.
      rewrite ?decide_True //. iFrame "#".
      destruct (decide (bid2 = bid1)) => //=.
      iNext. iAlways. iIntros "#HC (HQ1&HQ2)". rewrite big_sepS_union //.
      iDestruct ("Hwand1" with "HC [$]") as "($&$)".
      iDestruct ("Hwand2" with "HC [$]") as "($&$)".
    }
    rewrite delete_insert_ne //.
    rewrite big_sepM_insert_delete.
    iFrame.
    admit.
  }
  iMod ("Hclo" with "[-Hbid1 Hown1]").
  { admit. }
  iMod (saved_prop_agree with "Hsaved1 H
  iModIntro. iExists _, _, _, _, _, _. iFrame. iFrame "#".
  rewrite -later_sep. iNext.

    iDestruct (big_sepM_insert_acc _ _ bid1 with "Hbunch_wf") as "(Hbid1_bunch&H)"; first eauto.
    iDestruct "Hbid1_bunch" as (???) "(Hm1&Hown_auth1&Hs1&Hsr1&Hwand1)".
    iDestruct (meta_agree with "Hb_meta1 Hm1") as %<-.
    unify_ghost.
    iMod (ghost_var_update γ1 (γprop1_new, γprop1'_new) with "[$] [$]") as "(Hown_auth1&Hown1)".
    iFrame "Hown1".



Lemma staged_inv_open E N k E1 E2 γ γ' P Q Qr:
  ↑N ⊆ E →
  E2 ⊆ E1 →
  staged_inv N k E1 E2 γ γ' P ∗
  staged_value N γ Q Qr ={E,E∖↑N}=∗
  (▷ ▷ Q ∗ (∀ Q' Qr', ▷ Q' ∗ □ (C -∗ Q' -∗ |={E1, E2}_k=> P ∗ Qr') ={E∖↑N,E}=∗ staged_value N γ Q' Qr')) ∨
  (▷ ▷ Qr ∗ C ∗ |={E∖↑N, E}=> staged_value N γ Q True).
Proof.
  iIntros (??) "(#Hinv&Hval)".
  iDestruct "Hval" as (γprop γprop') "(Hγ&#Hsaved&#Hsaved')".
  iInv N as (γprop_alt γprop'_alt Qsaved Qrsaved) "H" "Hclose".
  iDestruct "H" as "(>Hγ'&#Hsaved_alt&#Hsaved'_alt&#HQ0&Hcase)".
  iDestruct (own_valid_2 with "Hγ' Hγ") as "#H".
  iDestruct "H" as %[Heq%Excl_included%leibniz_equiv _]%auth_both_valid.
  inversion Heq; subst.
  iDestruct "Hcase" as "[HQ|Hdone]".
  {
    iModIntro. iLeft.
    iSplitL "HQ".
    - iModIntro.
      iDestruct (saved_prop_agree with "Hsaved Hsaved_alt") as "Hequiv".
      iNext. by iRewrite "Hequiv".
    - iIntros (Q' Qr'). iIntros "(HQ'&#HQ'impl)".
      iMod (saved_prop_alloc Q') as (γprop_new) "#Hsaved_new".
      iMod (saved_prop_alloc Qr') as (γprop'_new) "#Hsaved'_new".
      iMod (own_update_2 _ _ _ (● Excl' (γprop_new, γprop'_new) ⋅
                                ◯ Excl' (γprop_new, γprop'_new)) with "Hγ' Hγ") as "[Hγ' Hγ]".
      { by apply auth_update, option_local_update, exclusive_local_update. }
      iMod ("Hclose" with "[HQ' Hγ']").
      * iNext. iExists γprop_new, γprop'_new, _, _. iFrame "#". iFrame.
      * iModIntro. iExists γprop_new, γprop'_new. iFrame "#". iFrame.
  }
  {
    iDestruct "Hdone" as "(HQ&>#HC&>#Hdone)".
    iModIntro. iRight.
    iSplitL "HQ".
    - iModIntro.
      iDestruct (saved_prop_agree with "Hsaved' Hsaved'_alt") as "Hequiv".
      iNext. by iRewrite "Hequiv".
    - iFrame "HC".
      iMod (saved_prop_alloc True) as (γprop'_new) "#Hsaved'_new".
      iMod (own_update_2 _ _ _ (● Excl' (γprop_alt, γprop'_new) ⋅
                                ◯ Excl' (γprop_alt, γprop'_new)) with "Hγ' Hγ") as "[Hγ' Hγ]".
      { by apply auth_update, option_local_update, exclusive_local_update. }
      iMod ("Hclose" with "[Hγ']").
      * iNext. iExists γprop_alt, γprop'_new, _, _. iFrame "#". iFrame.
        iAlways. iIntros. iSpecialize ("HQ0" with "[$] [$]").
        iApply (step_fupdN_inner_wand' with "HQ0"); auto. iIntros "($&?)".
      * iModIntro. iExists _, _. iFrame. iFrame. eauto.
  }
Qed.

Lemma staged_inv_NC_open E N k E1 E2 γ γ' P Q Qr:
  ↑N ⊆ E →
  E2 ⊆ E1 →
  NC ∗
  staged_inv N k E1 E2 γ γ' P ∗
  staged_value N γ Q Qr ={E,E∖↑N}=∗
  (▷ ▷ Q ∗ (∀ Q' Qr', ▷ Q' ∗ □ (C -∗ Q' -∗ |={E1, E2}_k=> P ∗ Qr') ={E∖↑N,E}=∗ staged_value N γ Q' Qr')).
Proof.
  iIntros (??) "(HNC&Hinv&Hval)".
  iMod (staged_inv_open with "[$]") as "[H|(_&HC&_)]"; auto.
  iDestruct (NC_C with "[$] [$]") as %[].
Qed.

Lemma staged_inv_weak_open E N k E1 γ γ' P:
  ↑N ⊆ E →
  E1 ⊆ E ∖ ↑N →
  staged_inv N k E1 E1 γ γ' P ∗
  staged_pending γ' ∗
  C -∗ |={E,E}_(S k)=> P.
Proof.
  iIntros (??) "(#Hinv&Hpending&#HC)".
  iInv N as (γprop_alt γprop'_alt Qsaved Qrsaved) "H" "Hclose".
  iDestruct "H" as "(>Hγ'&#Hsaved_alt&#Hsaved'_alt&#HQ0&Hcase)".
  iDestruct "Hcase" as "[HQ|Hfalse]"; last first.
  { iDestruct "Hfalse" as "(?&?&>H)".
    iDestruct (pending_done with "[$] [$]") as "[]".
  }
  iMod (fupd_intro_mask' _ E1) as "Hclo_E"; first auto.
  iMod (fupd_intro_mask' _ (∅)) as "Hclo_E1"; first by set_solver.
  iModIntro. rewrite Nat_iter_S. iModIntro. iNext.
  iMod "Hclo_E1" as "_".
  iMod ("HQ0" with "[$] [$]") as "H".
  iApply (step_fupdN_wand with "H"). iIntros "!> H".
  iMod "H" as "(HP&HQr)".
  iMod (pending_upd_done with "[$]") as "#Hdone".
  iMod "Hclo_E" as "_".
  iMod ("Hclose" with "[HQr Hγ']").
  { iNext. iExists _, _, _, _. iFrame "Hγ'". iFrame "#". by iRight. }
  iModIntro. eauto.
Qed.


End inv.
