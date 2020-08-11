From iris.algebra Require Import gmap auth agree gset coPset excl csum.
From iris.base_logic.lib Require Export fancy_updates.
From stdpp Require Export namespaces.
From iris.base_logic.lib Require Import wsat invariants saved_prop.
From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics.
From Perennial.program_logic Require Export step_fupd_extra crash_token crash_weakestpre ae_invariants_mutable ghost_var.
Set Default Proof Using "Type".
Import uPred.

Class stagedG (Σ : gFunctors) : Set := WsatG {
  staging_shot_inG :> inG Σ (csumR (fracR) (agreeR unitO));
}.

Definition stagedΣ : gFunctors :=
    #[GFunctor (csumR fracR (agreeR unitO))].

Instance subG_stagedG {Σ} : subG stagedΣ Σ → stagedG Σ.
Proof. solve_inG. Qed.

Definition staged_pending `{stagedG Σ} (q: Qp) (γ: gname) : iProp Σ :=
  own γ (Cinl q).
Definition staged_done `{stagedG Σ} (γ: gname) : iProp Σ :=
  own γ (Cinr (to_agree ())).

(* Schema:
   Fixed: O => C, 1 => P
   Mutable: O => Qs, 1 => Qr *)

Definition bi_sch_cfupd E E' P :=
  bi_sch_wand (bi_sch_var_fixed O) (bi_sch_fupd E E (bi_sch_fupd E' ∅ P)).

Definition bi_sch_staged_fupd (E: coPset) :=
  bi_sch_persistently
    (bi_sch_wand (bi_sch_var_mut O)
                 (bi_sch_cfupd E ∅ (bi_sch_sep (bi_sch_var_fixed 1) (bi_sch_var_mut 1)))).

Definition bi_sch_staged_cases :=
  bi_sch_or (bi_sch_var_mut O)
            (bi_sch_sep (bi_sch_var_mut 1) (bi_sch_sep (bi_sch_var_fixed O) (bi_sch_var_fixed 1))).

Definition bi_sch_staged E :=
  bi_sch_sep (bi_sch_staged_fupd E) (bi_sch_staged_cases).

Lemma bi_sch_staged_interp `{!invG Σ, !crashG Σ, !stagedG Σ} E k Qs Qr P :
  bi_schema_interp (S k) (bi_later <$> [C; P]) (bi_later <$> [Qs; Qr]) (bi_sch_staged E)
  ⊣⊢ (((▷ Qs -∗ ▷ C -∗ |k={E}=> |k={∅, ∅}=> ▷ P ∗ ▷ Qr) ∗ ▷ Qs) ∨ (▷ Qr ∗ ▷ C ∗ ▷ P))%I.
Proof. Admitted.
(*
  remember (S k) as k' eqn:Hlvl.
  repeat (rewrite ?bi_schema_interp_unfold //=).
  rewrite /cfupd ?uPred_fupd_level_eq /uPred_fupd_level_def.
  rewrite Hlvl /bi_except_0 intuitionistically_into_persistently.
  done.
Qed.
*)

Lemma bi_sch_staged_interp_weak `{!invG Σ, !crashG Σ, !stagedG Σ} E k Qs_mut P :
  bi_schema_interp (S k) (bi_later <$> [C; P]) (bi_later <$> Qs_mut) (bi_sch_staged E)
  ⊣⊢ let Qs := default emp%I (bi_later <$> (Qs_mut !! O)) in
     let Qr := default emp%I (bi_later <$> (Qs_mut !! 1)) in
     ((((Qs -∗ ▷ C -∗ |k={E}=> |k={∅, ∅}=> ▷ P ∗ Qr) ∗ Qs) ∨ (Qr ∗ ▷ C ∗ ▷ P)))%I.
Proof. Admitted.
(*
  remember (S k) as k' eqn:Hlvl.
  repeat (rewrite ?bi_schema_interp_unfold //=).
  rewrite /cfupd ?uPred_fupd_level_eq /uPred_fupd_level_def.
  rewrite Hlvl /bi_except_0 intuitionistically_into_persistently.
  rewrite /default. rewrite ?list_lookup_fmap.
  destruct (Qs_mut !! O); destruct (Qs_mut !! 1); auto.
Qed.
*)

Section staged_inv_defns.

  Context `{!invG Σ, !crashG Σ, !stagedG Σ}.

Definition staged_inv (k: nat) E (γ: gname) (P: iProp Σ) : iProp Σ :=
  ae_inv_mut k (bi_sch_staged E) [C; (P ∨ staged_done γ)%I].

Definition staged_value (k: nat) E (γp: gname) (b: bool) (Qs Qr P: iProp Σ) :=
  (∃ γr, (if b then staged_pending 1%Qp γr else staged_done γr) ∗
  ae_inv_mut_full k (bi_sch_staged E) [Qs; (Qr ∨ staged_done γr)] [C; (P ∨ staged_done γp)%I])%I.

End staged_inv_defns.

Section inv.
Context `{!invG Σ, !stagedG Σ, !crashG Σ}.
Implicit Types i : positive.
Implicit Types N : namespace.
Implicit Types P Q R : iProp Σ.

(*
Global Instance staged_contractive k N E E' γ : Contractive (staged_inv k N E E' γ).
Proof.
  rewrite /staged_inv=> n ?? ?.
  repeat (apply step_fupdN_ne || f_contractive || f_equiv); eauto.
Qed.

Global Instance staged_ne N E E' γ γ': NonExpansive (staged_inv N E E' γ γ').
Proof.
  rewrite /staged_inv=> n ?? ?.
  repeat (apply step_fupdN_ne || f_contractive || f_equiv); eauto using dist_le.
Qed.

Global Instance staged_proper N E E' γ γ' : Proper ((⊣⊢) ==> (⊣⊢)) (staged_inv N E E' γ γ').
Proof. apply ne_proper, _. Qed.
*)

Global Instance staged_persistent k E γ P : Persistent (staged_inv k E γ P).
Proof. rewrite /staged_inv. apply _. Qed.

Lemma pending_done q γ: staged_pending q γ -∗ staged_done γ -∗ False.
Proof.
  rewrite /staged_pending/staged_done.
  iIntros "H H'".
  { by iDestruct (own_valid_2 with "H H'") as %?. }
Qed.

Lemma pending_upd_done γ: staged_pending 1%Qp γ ==∗ staged_done γ.
Proof.
  rewrite /staged_pending/staged_done.
  iIntros "H". iMod (own_update with "H") as "$".
  { by apply cmra_update_exclusive. }
  done.
Qed.

Lemma pending_alloc:
  ⊢ |==> ∃ γ, staged_pending 1 γ.
Proof.
  iApply (own_alloc (Cinl 1%Qp)).
  { rewrite //=. }
Qed.

Lemma pending_split γ:
  staged_pending 1 γ ⊢ staged_pending (1/2)%Qp γ ∗ staged_pending (1/2)%Qp γ.
Proof. by rewrite /staged_pending -own_op -Cinl_op frac_op' Qp_div_2. Qed.

Lemma pending_join γ:
 staged_pending (1/2)%Qp γ ∗ staged_pending (1/2)%Qp γ ⊢  staged_pending 1 γ.
Proof. by rewrite /staged_pending -own_op -Cinl_op frac_op' Qp_div_2. Qed.

Lemma staged_inv_alloc k E E' P Q Qr:
  ▷ Q ∗ (C -∗ ▷ Q -∗ ▷ P ∗ ▷ Qr) -∗ |(S k)={E}=>
  ∃ γ, staged_inv (S k) E' γ P ∗ staged_value (S k) E' γ true Q Qr P ∗ staged_pending 1%Qp γ.
Proof.
  iMod (pending_alloc) as (γ) "H".
  iMod (pending_alloc) as (γr) "Hr".
  iIntros "(HQ&HQP)".
  iMod (ae_inv_mut_alloc (S k) E (bi_sch_staged E')
                   [C; (P ∨ staged_done γ)%I]
                   [Q; (Qr ∨ staged_done γr)%I]
          with "[HQ HQP]")
      as "(#Hi&Hmut)".
  { simpl fmap. rewrite bi_sch_staged_interp.
    iLeft.
    iSplitL "HQP".
    - iIntros "HQ >HC". iModIntro.
      iApply fupd_level_mask_weaken; first by set_solver+.
      iDestruct ("HQP" with "[$] [$]") as "($&$)".
    - eauto.
  }
  iModIntro. iExists _. iFrame "# ∗". iExists _; eauto. iFrame.
Qed.

(* TODO: need t o be able to get something back if we don't fire the view shift. And what about the Qr case? *)
Lemma staged_inv_open_modify_ae E k E1 γ P Q Qr Q' Qr' R:
  staged_value (S k) E1 γ true Q Qr P -∗
  (▷ Q -∗ |k={E}=> (▷ Q' -∗ |C={E1, ∅}_k=> P ∗ Qr') ∗  ▷ Q' ∗ R) -∗
  |(S k)={E}=> (R ∗ staged_value (S k) E1 γ true Q' Qr' P) ∨
               (▷ Qr ∗ C ∗ staged_value (S k) E1 γ false Q' Qr' P).
Proof.
  iIntros "Hval Hshift".
  rewrite /staged_value/=.
  iDestruct "Hval" as (γr) "(Hγr&Hval)" => //=.
  iMod (ae_inv_mut_full_acc _ _ _ _ ([Q'; (Qr' ∨ staged_done γr)%I]) _
                            ((R ∗ staged_pending 1%Qp γr)  ∨ (▷ Qr ∗ C ∗ staged_done γr))%I
          with "Hval [Hγr Hshift]") as "(HR&Hclo)";
    last first.
  { iModIntro. iDestruct "Hclo" as "[(Hr&?)|(?&?&?)]".
    - iLeft. iFrame. iExists _. iFrame; eauto.
    - iRight. iFrame. iExists _. iFrame; eauto.
  }
  iIntros "HQ".
  iDestruct (bi_sch_staged_interp with "HQ") as "HQ".
  iDestruct "HQ" as "[(Hwand&HQ)|HQ]".
  - iMod ("Hshift" with "HQ") as "(Hwand2&HQ&HR)".
    iSplitL "HQ Hwand2".
    { iModIntro. erewrite bi_sch_staged_interp.
      iLeft. iFrame "HQ".
      iIntros "HQ' >HC". iMod ("Hwand2" with "[$] [$]") as "H".
      iModIntro. by iMod "H" as "($&$)".
    }
    iModIntro. iLeft. iFrame.
  - iDestruct "HQ" as "(HQr&>#HC&HP)".
    iDestruct "HQr" as "[HQR|>Hfalse]"; last first.
    { iDestruct (pending_done with "[$] [$]") as %[]. }
    iMod (pending_upd_done with "Hγr") as "#Hγr".
    iModIntro.
    iSplitL "Hshift HP".
    { rewrite bi_sch_staged_interp.
      iRight. iFrame. eauto.
    }
    iRight. iFrame "# ∗".
Qed.

(* XXX: this is not currently true, but a better encoding of inv_mut should enable that *)
Lemma staged_value_into_disc k E γ P Q Qr :
  staged_value k E γ true Q Qr P -∗
  <disc> staged_value k E γ true Q Qr P.
Proof. Admitted.

Lemma staged_inv_open_crash k E γ P Q Qr:
  (▷ Q -∗ ▷ C -∗ |k={E}=> |k={∅, ∅}=> ▷ P ∗ ▷ Qr) -∗
  staged_value (S k) E γ true Q Qr P -∗ C -∗ |(S k)={E,E}=> ▷ Qr.
Proof.
  iIntros "Hwand".
  iDestruct 1 as (?) "(Hγr&Hval)". iIntros "#HC".
  iMod (ae_inv_mut_full_acc _ _ _ _ ([Q; (Qr ∨ staged_done γr)%I]) _
                            (▷ Qr)%I
          with "Hval [Hγr]") as "(HR&Hclo)";
    last first.
  { iModIntro. auto. }
  iIntros "HQ".
  iDestruct (bi_sch_staged_interp with "HQ") as "HQ".
  iDestruct "HQ" as "[(Hwand'&HQ)|HQ]".
  - iMod ("Hwand'" with "[$] [$]") as "H".
    iMod (fupd_level_intro_mask' _ ∅) as "Hclo''"; first by set_solver+.
    iMod ("H") as "(HP&Hdone)".
    iMod "Hclo''" as "_".
    iDestruct "Hdone" as "[HQR|>Hfalse]"; last first.
    { iDestruct (pending_done with "[$] [$]") as %[]. }
    iMod (pending_upd_done with "Hγr") as "Hγr".
    iModIntro. rewrite bi_sch_staged_interp. iFrame "#". iFrame.
  - iDestruct "HQ" as "([HQr|>Hfalse]&_&HP)"; last first.
    { iDestruct (pending_done with "Hγr [$]") as %[]. }
    iMod (pending_upd_done with "Hγr") as "#Hγr".
    iModIntro.
    iSplitL "HP".
    { rewrite bi_sch_staged_interp.
      iRight. iFrame "# ∗".
    }
    eauto.
Qed.

Lemma staged_inv_weak_open E k E1 γ P:
  E1 ⊆ E →
  staged_inv (S k) E1 γ P ∗
  staged_pending 1%Qp γ ∗
  C -∗ |(S k)={E,E}=> ▷ P.
Proof.
  iIntros (?) "(#Hinv&Hpending&#HC)".
  iMod (ae_inv_mut_acc _ _ _ _ (▷ P) with "Hinv [Hpending]"); last done.
  iIntros (Qs) "Hinv0".
  iDestruct (bi_sch_staged_interp_weak with "Hinv0") as "H".
  iDestruct "H" as "[(Hwand&HQ)|HQ]".
  - iMod (fupd_level_intro_mask' _ E1) as "Hclo''"; auto.
    iDestruct ("Hwand" with "[$] [$]") as "Hwand".
    iMod (fupd_level_le with "Hwand") as "Hwand"; auto.
    iMod (fupd_level_intro_mask' _ ∅) as "Hclo'''"; first by set_solver.
    iMod (fupd_level_le with "Hwand") as "(HP&HQr)"; auto.
    iMod "Hclo'''" as "_".
    iMod "Hclo''" as "_".
    iDestruct "HP" as "[HP|>Hfalse]"; last first.
    { iDestruct (pending_done with "[$] Hfalse") as %[]. }
    iMod (pending_upd_done with "[$]") as "#Hdone".
    iModIntro. iSplitR "HP"; last done.
    iApply bi_sch_staged_interp_weak. iFrame "# ∗".
  - iDestruct "HQ" as "(HQr&_&[HP|>Hfalse])"; last first.
    { iDestruct (pending_done with "Hpending [$]") as %[]. }
    iMod (pending_upd_done with "[$]") as "#Hdone".
    iFrame.
    iModIntro.
    iApply bi_sch_staged_interp_weak. iRight. iFrame "# ∗".
Qed.

End inv.
