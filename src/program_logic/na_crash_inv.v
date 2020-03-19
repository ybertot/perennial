From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl.
From iris.base_logic Require Export invariants.
From iris.program_logic Require Export weakestpre.
From Perennial.program_logic Require Import staged_invariant crash_weakestpre staged_wpc.
From Perennial.program_logic Require Export staged_wpc.
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

Definition na_crash_inv Γ N k :=
  (staged_inv Γ N k (⊤ ∖ ↑N) (⊤ ∖ ↑N))%I.

Definition na_crash_bundle Γ N k Q bset :=
  (∃ Qr, staged_inv Γ N k (⊤ ∖ ↑N) (⊤ ∖ ↑N) ∗ staged_bundle Γ Q Qr false bset)%I.

Definition na_crash_val Γ P bset :=
  (staged_crash Γ P bset)%I.

Definition na_crash_pending Γ N k P :=
  (∃ i, staged_inv Γ N k (⊤ ∖ ↑N) (⊤ ∖ ↑N) ∗ staged_crash_pending Γ P i)%I.

Global Instance na_crash_inv_pers Γ N k : Persistent (na_crash_inv Γ N k).
Proof. apply _. Qed.

Global Instance na_crash_val_pers Γ P bset : Persistent (na_crash_val Γ P bset).
Proof. apply _. Qed.

Lemma na_crash_inv_init N k E:
  (|={E}=> ∃ Γ, na_crash_inv Γ N k)%I.
Proof. iMod (staged_inv_init) as (Γ) "H". iExists Γ. iFrame "H". eauto. Qed.

Lemma na_crash_inv_alloc Γ N k E P Q:
  ↑N ⊆ E →
  na_crash_inv Γ N k -∗
  ▷ Q -∗ □ (Q -∗ P) ={E}=∗
  ∃ i, na_crash_bundle Γ N k Q {[i]} ∗ na_crash_val Γ P {[i]} ∗ na_crash_pending Γ N k P.
Proof.
  iIntros (?) "#Hinv HQ #HQP".
  iMod (staged_inv_alloc Γ N k E (⊤ ∖ ↑N) P Q True%I with "[HQ]") as (i') "(Hbundle&#Hval&Hpend)".
  { auto. }
  { iFrame "#". iFrame. iAlways; iIntros; eauto. rewrite right_id. iApply "HQP"; eauto. }
  iModIntro. iExists i'. iFrame "#".
  iSplitL "Hbundle".
  - iExists _. iFrame.
  - iExists _. eauto.
Qed.

Lemma na_crash_inv_full_impl N k Q P:
  na_crash_inv_full N k Q P -∗ □ (Q -∗ P).
Proof. iIntros "H". iDestruct "H" as (???) "(?&?&$)"; eauto. Qed.

Lemma na_crash_inv_full_weaken N k Q P:
  na_crash_inv_full N k Q P -∗ na_crash_inv N k P.
Proof. iIntros "H". iDestruct "H" as (???) "(?&?)"; eauto. iExists _, _. iFrame. Qed.

Lemma na_crash_inv_pending_weaken N k P:
  na_crash_inv_pending N k P -∗ na_crash_inv N k P.
Proof. iIntros "H". iDestruct "H" as (??) "(?&?)"; eauto. iExists _, _. iFrame. Qed.

Lemma wpc_na_crash_inv_open s k k' E1 E2 e Φ Φc Q P N:
  ↑N ⊆ E1 →
  S k < k' →
  to_val e = None →
  na_crash_inv_full N (LVL k') Q P -∗
  (Φc ∧ (Q -∗ WPC e @ NotStuck; (LVL k); (E1 ∖ ↑N); ∅
                    {{λ v, Q ∗ (na_crash_inv_full N (LVL k') Q P -∗ (Φ v ∧ Φc))}}
                    {{ Φc ∗ P }})) -∗
  WPC e @ s; LVL (S (S k)); E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (???) "Hfull Hwp".
  iDestruct "Hfull" as (???) "(#Hinv&Hval&#Hwand)".
  iApply (wpc_staged_inv_open _ _ _ _ _ _ _ _ _ _ _ (λ _, Q)); eauto.
  iFrame "Hinv". iFrame.
  iSplit.
  { iDestruct "Hwp" as "($&_)". }
  iDestruct "Hwp" as "(_&Hwp)".
  iIntros "HQ". iSpecialize ("Hwp" with "HQ").
  iApply (wpc_strong_mono' with "Hwp"); eauto.
  iSplit.
  - iIntros (?) "(HQ&HQrest)".
    iModIntro. iFrame "HQ".
    iFrame "Hwand". iIntros.
    iApply "HQrest". iExists _, _, _. iFrame. iFrame "Hinv". iFrame "Hwand".
  - iIntros. rewrite difference_diag_L. iModIntro; eauto.
Qed.

Lemma wpc_na_crash_inv_open_modify Qnew s k k' E1 E2 e Φ Φc Q P N :
  ↑N ⊆ E1 →
  S k < k' →
  to_val e = None →
  na_crash_inv_full N (LVL k') Q P -∗
  (Φc ∧ (Q -∗ WPC e @ NotStuck; (LVL k); (E1 ∖ ↑N); ∅
                    {{λ v, Qnew v ∗ □ (Qnew v -∗ P)  ∗ (na_crash_inv_full N (LVL k') (Qnew v) P -∗ (Φ v ∧ Φc))}}
                    {{ Φc ∗ P }})) -∗
  WPC e @ s; LVL (S (S k)); E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (???) "Hfull Hwp".
  iDestruct "Hfull" as (???) "(#Hinv&Hval&#Hwand)".
  iApply (wpc_staged_inv_open _ _ _ _ _ _ _ _ _ _ _ Qnew); eauto.
  iFrame "Hinv". iFrame.
  iSplit.
  { iDestruct "Hwp" as "($&_)". }
  iDestruct "Hwp" as "(_&Hwp)".
  iIntros "HQ". iSpecialize ("Hwp" with "HQ").
  iApply (wpc_strong_mono' with "Hwp"); eauto.
  iSplit.
  - iIntros (?) "(HQ&#Hwand'&HQrest)".
    iModIntro. iFrame "HQ Hwand'". iIntros "Hval".
    iApply "HQrest". iExists _, _, _. iFrame. iFrame "Hinv". iFrame "Hwand'".
  - iIntros. rewrite difference_diag_L. iModIntro; eauto.
Qed.

Lemma wpc_na_crash_inv_init s k k' N E2 e Φ Φc P :
  k' < k →
  na_crash_inv_pending N (LVL k') P ∗
  WPC e @ s; LVL k; ⊤; E2 {{ Φ }} {{ Φc }} ⊢
  WPC e @ s; LVL (S k); ⊤; E2 {{ Φ }} {{ Φc ∗ P }}.
Proof.
  iIntros (?) "(H&?)".
  iDestruct "H" as (??) "(?&?)".
  iApply wpc_staged_inv_init; last (by iFrame); eauto.
Qed.

Lemma na_crash_inv_open_modify N k' k E E' P Q R:
  ↑N ⊆ E →
  na_crash_inv_full N k' Q P -∗
  ((Q ∗ (∀ Q', ▷ Q' ∗ □ (Q' -∗ P) ={E∖↑N,E}=∗ na_crash_inv_full N k' Q' P)) ∨ (C ∗ |={E∖↑N, E}=> na_crash_inv_full N k' Q P)
   -∗ |={E ∖ ↑N, E'}_k=> R) -∗
  (|={E,E'}_(S (S k))=> R).
Proof.
  iIntros (?) "H Hwp".
  iDestruct "H" as (???) "(#Hinv&H&#Hwand)".
  iMod (staged_inv_open with "[H]") as "HQ"; try iFrame "H Hinv"; eauto.
  iMod (fupd_intro_mask' _ ∅) as "Hclo"; first set_solver.
  iModIntro.
  rewrite Nat_iter_S.
  iModIntro. iNext. iModIntro.
  rewrite Nat_iter_S.
  iModIntro. iNext. iMod "Hclo" as "_".
  iApply ("Hwp" with "[HQ]").
  iDestruct "HQ" as "[(HQ&Hclo)|(?&HC&Hclo)]".
  - iLeft. iFrame. iIntros (Q') "(HQ'&#Hwand')". iMod ("Hclo" $! Q' True%I with "[HQ']") as "H".
    { iFrame. iAlways. iIntros. iApply step_fupdN_inner_later; auto. iNext.
      iDestruct ("Hwand'" with "[$]") as "$". }
    iModIntro. iExists _, _, _. iFrame "H Hinv Hwand'".
  - iRight. iFrame. iMod "Hclo". iModIntro. iExists _, _, _. iFrame "Hclo Hwand Hinv".
Qed.

Lemma na_crash_inv_open N k' k E E' P Q R:
  ↑N ⊆ E →
  na_crash_inv_full N k' Q P -∗
  ((Q ∗ (▷ Q ={E∖↑N,E}=∗ na_crash_inv_full N k' Q P)) ∨ (C ∗ |={E∖↑N, E}=> na_crash_inv_full N k' Q P)
   -∗ |={E ∖ ↑N, E'}_k=> R) -∗
  (|={E,E'}_(S (S k))=> R).
Proof.
  iIntros (?) "H1 H2". iDestruct (na_crash_inv_full_impl with "[$]") as "#HQP".
  iApply (na_crash_inv_open_modify with "[$]"); first done.
  iIntros "Hwand". iApply ("H2" with "[Hwand]").
  iDestruct "Hwand" as "[H1|H2]".
   - iLeft. iDestruct "H1" as "($&H)". iIntros "HQ". by iMod ("H" $! Q with "[$]").
   - iRight. iFrame.
Qed.

End ci.
