From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl.
From iris.base_logic Require Export invariants.
From iris.program_logic Require Export weakestpre.
From Perennial.program_logic Require Import staged_invariant crash_weakestpre.
Set Default Proof Using "Type".
Import uPred.

Section ci.
Context `{!irisG Λ Σ}.
Context `{!stagedG Σ}.
Context `{!crashG Σ}.
Context `{inG Σ (exclR unitO)}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φc : iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Definition Tok (γ: gname) :=
  own γ (Excl ()).

Lemma Tok_Tok γ: Tok γ ∗ Tok γ -∗ False.
Proof. iIntros "(H1&H2)". by iDestruct (own_valid_2 with "H1 H2") as %?. Qed.

Instance timeless_Tok γ: Timeless (Tok γ).
Proof. rewrite /Tok. apply _. Qed.

Lemma wpc_ci_inv s k N E1 e Φ Φc P γ γ' :
  ↑N ⊆ E1 →
  staged_inv N k (E1 ∖ ↑N) (E1 ∖ ↑N) γ γ' P ∗
  staged_pending γ' ∗
  WPC e @ s; ((S k)); E1; ∅ {{ Φ }} {{ Φc }} ⊢
  WPC e @ s; (2 * (S k)); E1; ∅ {{ Φ }} {{ Φc ∗ P }}.
Proof.
  iIntros (Hin) "(#Hinv&Hpending&H)".
  iApply (wpc_strong_crash_frame s s _ _ E1 _ _ with "H"); try auto.
  { lia. }
  iIntros "HΦc".
  replace (2 * S k - S k) with (S k) by lia.
  iApply (staged_inv_weak_open); eauto.
Qed.

(*
Lemma wpc_staged_invariant_aux s k E1 e Φ Φc P Q1 R1 Q2 R2 N γ' :
  ↑N ⊆ E1 →
  □ (Q1 -∗ R1) ∗
  □ (Q2 -∗ R2) ∗
  staged_inv N γ' (ci_staged (2 * ((S (S k)))) ∅ ∅ P) ∗
  staged_value N γ' (Q1 ∗ WPC e @ k; E1 ∖ ↑N;∅ {{ v, (Φ v ∧ Φc) ∗ P }}{{Φc ∗ P}} ∗ Q2) ⊢
  |={E1,E1}_(S (2 * S (S k)))=> R1 ∗ WPC e @ s; (2 * S (S k)); E1; ↑N {{ v, Φ v }} {{Φc}} ∗ R2.
Proof.
  iIntros (?) "(#HQR1&#HQR2&#Hsi&Hwp)".
  iLöb as "IH" forall (Q1 Q2 R1 R2 e) "HQR1 HQR2".
  destruct (to_val e) as [v|] eqn:Hval.
  {
    rewrite Nat_iter_S.
    iMod (staged_inv_open with "[$]") as "(H&Hclo')".
    { set_solver. }
    iMod (fupd_intro_mask' _ ∅) as "Hclo"; first by set_solver+.
    iModIntro. rewrite Nat_iter_add. iModIntro. iNext. iModIntro.
    rewrite Nat_iter_S.
    iModIntro. iNext.
    iMod "Hclo" as "_".
    rewrite Nat_iter_S.
    iMod (fupd_intro_mask' _ ∅) as "Hclo"; first by set_solver+.
    iModIntro. iModIntro. iNext.


    iModIntro.
    iApply step_fupdN_later; first reflexivity. iNext.
    iApply step_fupdN_later; first reflexivity. iNext.
    iMod "Hclo".
    rewrite wpc_unfold /wpc_pre.
    rewrite wpc_unfold /wpc_pre.
    rewrite Hval. iDestruct "H" as "(HQ1&(H&_)&HQ2)".
    iMod "H" as "(HΦ&HP)".
    iMod ("Hclo'" with "[HP]").
    { iSplitL. iApply "HP". iAlways.
      iIntros. rewrite /ci_staged.
      iApply step_fupdN_inner_later; first auto.
      iNext. eauto.
    }
    iModIntro.
    iSplitL "HQ1".
    { by iApply "HQR1". }
    iSplitR "HQ2"; last first.
    { by iApply "HQR2". }
    iSplit.
    - iDestruct "HΦ" as "($&_)". eauto.
    - iDestruct "HΦ" as "(_&HΦ)".
      iApply step_fupdN_inner_later; first by set_solver.
      repeat iNext. by iFrame.
  }
  iEval (rewrite (Nat_iter_S _)).
  iMod (staged_inv_open with "[$]") as "(H&Hclo')".
  { set_solver. }
  iMod (fupd_intro_mask' _ ∅) as "Hclo"; first by set_solver+.
  rewrite Nat_iter_add.
  rewrite (Nat_iter_S (S k)).
  iModIntro. iModIntro. iNext. iModIntro.
  iModIntro. iNext.
  iMod "Hclo" as "_".
  iDestruct "H" as "(HQ1&H&HQ2)".
  iSpecialize ("Hclo'" $! _ with "[H]").
  { iSplitL "H". iApply "H".
    iAlways.
    iIntros "H".
    rewrite wpc_unfold /wpc_pre.
    rewrite Hval. iDestruct "H" as "(_&HP)".
    rewrite /ci_staged.
    iMod (fupd_intro_mask') as "Hclo"; [| iMod "HP"].
    { set_solver. }
    iModIntro.
    iApply (step_fupdN_le (S k)).
    { reflexivity. }
    { lia. }
    iApply (step_fupdN_wand with "HP").
    iIntros "HP". iMod "HP". iDestruct "HP" as "(_&HP)".
    by iFrame.
  }
  iMod "Hclo'".
  rewrite -Nat_iter_add. iApply step_fupdN_inner_later; first reflexivity.
  iNext.
  iSplitL "HQ1".
  { iApply "HQR1". eauto. }
  iSplitR "HQ2"; last first.
  { iApply "HQR2". eauto. }
  iEval (rewrite wpc_unfold /wpc_pre). rewrite Hval.
  iSplit.
  - iIntros.
    iMod (staged_inv_open with "[$]") as "(H&Hclo')".
    { set_solver. }
    iMod (fupd_intro_mask' _ ∅) as "Hclo''".
    { set_solver. }
    iModIntro. rewrite Nat_iter_S. 
    iModIntro. iNext. rewrite Nat_iter_add.
    rewrite Nat_iter_S.
    iModIntro. iModIntro. iNext.
    iMod "Hclo''" as "_".
    rewrite wpc_unfold /wpc_pre.
    rewrite Hval. iDestruct "H" as "(H&_)".
    iMod (fupd_intro_mask' _ (E1 ∖ ↑N)) as "Hclo''".
    { set_solver. }
    iMod ("H" with "[$]") as "H".
    iModIntro.
    iApply (step_fupdN_wand with "H").
    iIntros "H".
    rewrite right_id Nat_iter_S.
    iMod "H". iModIntro. iNext.
    iDestruct "H" as "(%&H)".
    iApply step_fupdN_inner_later; first reflexivity. do 2 iNext.
    iSplitL "".
    { destruct s; eauto. }
    iIntros.
    iMod ("H" with "[//]") as "H".
  iEval rewrite Nat_iter_S.
  iModIntro. iModIntro. iNext.
  rewrite Nat_iter_add.
  iModIntro. iApply (step_fupdN_le (S k)); [ reflexivity | lia |].
  iApply (step_fupdN_wand with "H"). iIntros "H".
  rewrite right_id.
  iEval rewrite Nat_iter_S.
  do 2 iMod "H". iModIntro. iNext.
  iMod "H".
  iMod "H".
  iModIntro.
  iApply (step_fupdN_wand with "H"). iIntros "H".
  iMod "H".
  iSpecialize ("Hclo'" $! _ with "[H]").
  { iSplitL "H". iApply "H".
    iAlways.
    iIntros "H".

    replace (2 * ((S (S k)))) with (S k + (S (S (S k)))) by lia.
    iApply step_fupdN_inner_plus.
    iDestruct "H" as "(_&H&_)".
    iPoseProof (wpc_crash with "H") as "H".
    iApply (step_fupdN_wand with "H").
    iIntros "HP". iMod "HP". iModIntro. iApply step_fupdN_inner_later; auto.
    do 4 iNext. iDestruct "HP" as "(_&$)".
  }
  iMod "Hclo'". iClear "Hclo''".
  iMod (fupd_intro_mask' _ ∅) as "Hclo''"; first by set_solver+.
  iModIntro. iModIntro. iNext. iMod "Hclo''" as "_".
  iModIntro.
    iApply ("IH" with "Hclo' [] []").
    { iAlways. iIntros "H". eauto. }
    { iAlways. iIntros "H". iApply (big_sepL_mono with "H").
      iIntros. iApply (wpc_strong_mono' with "[$]"); eauto.
      lia.
      rewrite difference_diag_L; auto.
    }
  - iIntros.
    iMod (staged_inv_open with "[$]") as "(H&Hclo')".
    { set_solver. }
    rewrite diag_
    iMod (fupd_intro_mask' _ ∅) as "Hclo''".
    { set_solver. }
    iModIntro. rewrite Nat_iter_S. rewrite Nat_iter_S.
    iModIntro. iNext. iModIntro. iModIntro. iNext.
    iMod "Hclo''" as "_".
    rewrite wpc_unfold /wpc_pre.
    rewrite Hval. iDestruct "H" as "(_&H)".
    iMod (fupd_intro_mask' _ (E1 ∖ ↑N)) as "Hclo''".
    { set_solver. }
    iMod ("H") as "H".
    iModIntro.
    iApply (step_fupdN_wand with "H").
    iIntros "H".
    iMod "H" as "(($&HP)&$)".
    eauto.
Qed.
*)



Lemma wpc_staged_invariant_aux s k E1 E1' e Φ Φc P N γ γ' :
  E1 ⊆ E1' →
  ↑N ⊆ E1 →
  staged_inv N (2 * (S k)) (E1' ∖ ↑N) (E1' ∖ ↑N) γ γ' P ∗
  staged_value N γ (WPC e @ k; E1 ∖ ↑N;∅ {{ v, (Φ v ∧ Φc) ∗ P }}{{Φc ∗ P}}) Φc
  ⊢ |={E1,E1}_(S (2 * S (S k)))=>
     WPC e @ s; 2 * S (S k); E1; ∅ {{ v, Φ v }} {{Φc}}.
Proof.
  iIntros (??) "(#Hsi&Hwp)".
  iLöb as "IH" forall (e).
  destruct (to_val e) as [v|] eqn:Hval.
  {
    rewrite Nat_iter_S.
    iMod (staged_inv_open with "[$]") as "[(H&Hclo')|Hcrash]"; auto.
    {
      iMod (fupd_intro_mask' _ ∅) as "Hclo"; first by set_solver+.
      iModIntro. rewrite Nat_iter_add. iModIntro. iNext. iModIntro.
      rewrite Nat_iter_S.
      iModIntro. iNext.
      iMod "Hclo" as "_".
      rewrite Nat_iter_S.
      iMod (fupd_intro_mask' _ ∅) as "Hclo"; first by set_solver+.
      iModIntro. iModIntro. iNext.


      iModIntro.
      iApply step_fupdN_later; first reflexivity. iNext.
      iApply step_fupdN_later; first reflexivity. iNext.
      iMod "Hclo".
      rewrite wpc_unfold /wpc_pre.
      rewrite wpc_unfold /wpc_pre.
      rewrite Hval.
      iDestruct "H" as "(H&_)".
      iMod "H" as "(HΦ&HP)".
      iMod ("Hclo'" $! _ True%I with "[HP]").
      { iSplitL. iApply "HP". iAlways.
        iIntros. iApply step_fupdN_inner_later; first auto.
        iNext. eauto.
      }
      iModIntro. iFrame.
      iSplit.
      - iDestruct "HΦ" as "($&_)". eauto.
      - iDestruct "HΦ" as "(_&HΦ)".
        iIntros "HC".
        iApply step_fupdN_inner_later; first by set_solver.
        repeat iNext.
        iApply step_fupdN_inner_later; first by set_solver.
        repeat iNext.
        by iFrame.
    }
    {
      iMod (fupd_intro_mask' _ ∅) as "Hclo"; first by set_solver+.
      iModIntro. rewrite Nat_iter_add. iModIntro. iNext. iModIntro.
      rewrite Nat_iter_S.
      iModIntro. iNext.
      iMod "Hclo" as "_".
      rewrite Nat_iter_S.
      iMod (fupd_intro_mask' _ ∅) as "Hclo"; first by set_solver+.
      iModIntro. iModIntro. iNext.


      iModIntro.
      iApply step_fupdN_later; first reflexivity. iNext.
      iApply step_fupdN_later; first reflexivity. iNext.
      iMod "Hclo".
      iDestruct "Hcrash" as "(HΦc&HC&Hclo')".
      iMod "Hclo'".
      rewrite wpc_unfold /wpc_pre.
      rewrite wpc_unfold /wpc_pre.
      rewrite Hval.
      iDestruct "H" as "(H&_)".
      iMod "H" as "(HΦ&HP)".
      iMod ("Hclo'" $! _ True%I with "[HP]").
      { iSplitL. iApply "HP". iAlways.
        iIntros. iApply step_fupdN_inner_later; first auto.
        iNext. eauto.
      }
      iModIntro. iFrame.
      iSplit.
      - iDestruct "HΦ" as "($&_)". eauto.
      - iDestruct "HΦ" as "(_&HΦ)".
        iIntros "HC".
        iApply step_fupdN_inner_later; first by set_solver.
        repeat iNext.
        iApply step_fupdN_inner_later; first by set_solver.
        repeat iNext.
        by iFrame.
    }
    -
  }
  iEval (rewrite (Nat_iter_S _)).
  iMod (staged_inv_open with "[$]") as "(H&Hclo')".
  { set_solver. }
  iMod (fupd_intro_mask' _ ∅) as "Hclo"; first by set_solver+.
  rewrite Nat_iter_add.
  rewrite (Nat_iter_S (S k)).
  iModIntro. iModIntro. iNext. iModIntro.
  iModIntro. iNext.
  iMod "Hclo" as "_".
  iDestruct "H" as "(HQ1&H&HQ2)".
  iSpecialize ("Hclo'" $! _ with "[H]").
  { iSplitL "H". iApply "H".
    iAlways.
    iIntros "H".
    rewrite wpc_unfold /wpc_pre.
    rewrite Hval. iDestruct "H" as "(_&HP)".
    rewrite /ci_staged.
    iMod (fupd_intro_mask') as "Hclo"; [| iMod "HP"].
    { set_solver. }
    iModIntro.
    iApply (step_fupdN_le (S k)).
    { reflexivity. }
    { lia. }
    iApply (step_fupdN_wand with "HP").
    iIntros "HP". iMod "HP". iDestruct "HP" as "(_&HP)".
    by iFrame.
  }
  iMod "Hclo'".
  rewrite -Nat_iter_add. iApply step_fupdN_inner_later; first reflexivity.
  iNext.
  iSplitL "HQ1".
  { iApply "HQR1". eauto. }
  iSplitR "HQ2"; last first.
  { iApply "HQR2". eauto. }
  iEval (rewrite wpc_unfold /wpc_pre). rewrite Hval.
  iSplit.
  - iIntros.
    iMod (staged_inv_open with "[$]") as "(H&Hclo')".
    { set_solver. }
    iMod (fupd_intro_mask' _ ∅) as "Hclo''".
    { set_solver. }
    iModIntro. rewrite Nat_iter_S. 
    iModIntro. iNext. rewrite Nat_iter_add.
    rewrite Nat_iter_S.
    iModIntro. iModIntro. iNext.
    iMod "Hclo''" as "_".
    rewrite wpc_unfold /wpc_pre.
    rewrite Hval. iDestruct "H" as "(H&_)".
    iMod (fupd_intro_mask' _ (E1 ∖ ↑N)) as "Hclo''".
    { set_solver. }
    iMod ("H" with "[$]") as "H".
    iModIntro.
    iApply (step_fupdN_wand with "H").
    iIntros "H".
    rewrite right_id Nat_iter_S.
    iMod "H". iModIntro. iNext.
    iDestruct "H" as "(%&H)".
    iApply step_fupdN_inner_later; first reflexivity. do 2 iNext.
    iSplitL "".
    { destruct s; eauto. }
    iIntros.
    iMod ("H" with "[//]") as "H".
  iEval rewrite Nat_iter_S.
  iModIntro. iModIntro. iNext.
  rewrite Nat_iter_add.
  iModIntro. iApply (step_fupdN_le (S k)); [ reflexivity | lia |].
  iApply (step_fupdN_wand with "H"). iIntros "H".
  rewrite right_id.
  iEval rewrite Nat_iter_S.
  do 2 iMod "H". iModIntro. iNext.
  iMod "H".
  iMod "H".
  iModIntro.
  iApply (step_fupdN_wand with "H"). iIntros "H".
  iMod "H".
  iSpecialize ("Hclo'" $! _ with "[H]").
  { iSplitL "H". iApply "H".
    iAlways.
    iIntros "H".

    replace (2 * ((S (S k)))) with (S k + (S (S (S k)))) by lia.
    iApply step_fupdN_inner_plus.
    iDestruct "H" as "(_&H&_)".
    iPoseProof (wpc_crash with "H") as "H".
    iApply (step_fupdN_wand with "H").
    iIntros "HP". iMod "HP". iModIntro. iApply step_fupdN_inner_later; auto.
    do 4 iNext. iDestruct "HP" as "(_&$)".
  }
  iMod "Hclo'". iClear "Hclo''".
  iMod (fupd_intro_mask' _ ∅) as "Hclo''"; first by set_solver+.
  iModIntro. iModIntro. iNext. iMod "Hclo''" as "_".
  iModIntro.
    iApply ("IH" with "Hclo' [] []").
    { iAlways. iIntros "H". eauto. }
    { iAlways. iIntros "H". iApply (big_sepL_mono with "H").
      iIntros. iApply (wpc_strong_mono' with "[$]"); eauto.
      lia.
      rewrite difference_diag_L; auto.
    }
  - iIntros.
    iMod (staged_inv_open with "[$]") as "(H&Hclo')".
    { set_solver. }
    iMod (fupd_intro_mask' _ ∅) as "Hclo''".
    { set_solver. }
    iModIntro. rewrite Nat_iter_S. rewrite Nat_iter_S.
    iModIntro. iNext. iModIntro. iModIntro. iNext.
    iMod "Hclo''" as "_".
    rewrite wpc_unfold /wpc_pre.
    rewrite Hval. iDestruct "H" as "(_&H)".
    iMod (fupd_intro_mask' _ (E1 ∖ ↑N)) as "Hclo''".
    { set_solver. }
    iMod ("H") as "H".
    iModIntro.
    iApply (step_fupdN_wand with "H").
    iIntros "H".
    iMod "H" as "(($&HP)&$)".
    eauto.
Qed.
*)

Lemma NC_C: NC -∗ C -∗ False.
Proof.
 rewrite /C C_aux.(seal_eq).
 rewrite /NC NC_aux.(seal_eq).
  iIntros "H H'".
  { by iDestruct (own_valid_2 with "H H'") as %?. }
Qed.

Lemma wpc_staged_invariant s k E1 E1' e Φ Φc Q Qrest P N γ γ' :
  E1 ⊆ E1' →
  ↑N ⊆ E1 →
  to_val e = None →
  staged_inv N (2 * (S k)) (E1' ∖ ↑N) (E1' ∖ ↑N) γ γ' P ∗
  staged_value N γ Q Qrest ∗
  (Φc ∧ (▷ (Q) -∗ WPC e @ NotStuck; k; (E1 ∖ ↑N); ∅ {{ λ v, Φ v ∗ P}} {{ Φc ∗ P }})) ⊢
  WPC e @ s; (2 * S (S k)); E1; ∅ {{ Φ }} {{ Φc }}.
Proof.
  iIntros (?? Hval) "(#Hinv&Hval&Hwp)".
  rewrite !wpc_unfold /wpc_pre.
  iSplit; last first.
  {
    iDestruct "Hwp" as "(Hwp&_)". iIntros "HC".
    iApply step_fupdN_inner_later; try reflexivity.
    repeat iNext.
    iApply step_fupdN_inner_later; try reflexivity.
    eauto.
  }
  rewrite Hval.
  iIntros (????) "Hstate HNC".
  iMod (staged_inv_open with "[$]") as "[(H&Hclo)|Hfalse]"; [ auto | auto | |];
    last first.
  { iDestruct "Hfalse" as "(_&HC&_)".
    iDestruct (NC_C with "[$] [$]") as "[]".
  }
  iMod (fupd_intro_mask' _ ∅) as "Hclo'"; first set_solver+.
  iModIntro.
  iEval (rewrite Nat_iter_S). iModIntro. iNext.
  iDestruct ("Hwp" with "[$]") as "(Hwp&_)".
  iMod "Hclo'".
  iMod ("Hwp" with "[$] [$]") as "Hwp". iModIntro.
  rewrite Nat_iter_add.
  iEval rewrite Nat_iter_S_r.
  iApply (step_fupdN_wand with "Hwp").
  iIntros "Hwp".
  iModIntro. iNext. rewrite right_id. rewrite Nat_iter_S_r.
  iApply step_fupdN_inner_later; auto. iNext. iNext. iNext. iModIntro.
  iDestruct "Hwp" as "H".
  iMod "H". iModIntro.
  iDestruct "H" as "(%&H)".
  iSplitL "".
  { destruct s; eauto. }
  iIntros.
  iMod ("H" with "[//]") as "H".
  iEval rewrite Nat_iter_S.
  iModIntro. iModIntro. iNext.
  rewrite Nat_iter_add.
  iModIntro. iApply (step_fupdN_le (S k)); try (auto; lia).
  iApply (step_fupdN_wand with "H"). iIntros "H".
  rewrite right_id.
  iEval rewrite Nat_iter_S.
  do 2 iMod "H". iModIntro. iNext.
  iMod "H".
  iMod "H".
  iModIntro.
  iApply (step_fupdN_wand with "H"). iIntros "H".
  iMod "H".
  iDestruct "H" as "(Hσ&H&Hefs&HNC)".
  iSpecialize ("Hclo" $!
               (WPC e2 @ k; E1 ∖ ↑N;∅ {{ v, Φ v ∗ P }}{{Φc ∗ P}} ∗ (C ∨ NC))%I
               Φc with "[H HNC]").
  { iSplitL "H HNC". 
    - iNext. iFrame.
    - iAlways. iIntros "HC (H&_)".
    replace (2 * (((S k)))) with (S k + S k) by lia.
    rewrite Nat_iter_add.
    iPoseProof (wpc_crash with "H") as "H".
    iSpecialize ("H" with "[$]").
    iMod (fupd_intro_mask' _ (E1 ∖ ↑N)) as "Hclo".
    { set_solver. }
    iMod "H". iModIntro.
    iEval rewrite step_fupdN_S_fupd.
    iApply (step_fupdN_wand with "H").
    iIntros "HP".
    iMod "HP". iMod "Hclo".
    iApply (step_fupdN_inner_wand with "HP"); eauto.
    { set_solver+. }
    iIntros "($&$)".
  }
  iMod "Hclo".
  iMod (fupd_intro_mask' _ ∅) as "Hclo''"; first by set_solver+.
  iModIntro. iModIntro. iNext. iMod "Hclo''" as "_".
  iModIntro.
  iApply step_fupdN_inner_frame_l; iFrame.
  rewrite (comm _ _ NC).
  iApply step_fupdN_inner_frame_r; iFrame.
  iSplitR "Hefs"; last first.
  { iApply (big_sepL_mono with "Hefs").
    iIntros. iApply (wpc_strong_mono' with "[$]"); eauto.
    - lia.
    - iSplit; eauto. rewrite difference_diag_L; eauto.
  }
  iApply (wpc_staged_invariant_aux s k E1 E2 E1' E2'
                _ Φ Φc P
                (state_interp σ2 a1 (strings.length efs + a2)) _
                ([∗ list] ef ∈ efs, WPC ef @ k; ⊤;∅ {{ v, fork_post v }}{{True}})%I  _ N γ with "[Hclo]"); try assumption.
  { iIntros. iFrame "Hinv". iFrame "Hclo".
    iSplit.
    - eauto.
    - iAlways. iIntros "H". iApply (big_sepL_mono with "H").
      iIntros. iApply (wpc_strong_mono' with "[$]"); eauto.
  }
Qed.


End ci.
