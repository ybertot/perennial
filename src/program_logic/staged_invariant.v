From iris.algebra Require Import gmap auth agree gset coPset excl csum.
From iris.base_logic.lib Require Export fancy_updates.
From stdpp Require Export namespaces.
From iris.base_logic.lib Require Import wsat invariants saved_prop.
From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics.
From Perennial.program_logic Require Export step_fupd_extra crash_token crash_weakestpre invariants_mutable ghost_var.
Set Default Proof Using "Type".
Import uPred.

Class stagedG (Σ : gFunctors) : Set := WsatG {
                                           (*
  staging_saved_inG :> inG Σ (agreeR (prodO gnameO gnameO));
  staging_auth_inG :> inG Σ (authR (optionUR (exclR gnameO)));
                                            *)
  staging_shot_inG :> inG Σ (csumR (fracR) (agreeR unitO));
}.

Definition staged_pending `{stagedG Σ} (q: Qp) (γ: gname) : iProp Σ :=
  own γ (Cinl q).
Definition staged_done `{stagedG Σ} (γ: gname) : iProp Σ :=
  own γ (Cinr (to_agree ())).

(* Schema:
   Fixed: O => C, 1 => P, 2 => staged_done 1 γp;
   Mutable: O => Qs, 1 => Qr; 2 => staged_done 1 γcancel; 3 => staged_pending γcancel *)

Definition bi_sch_cfupd E E' P :=
  bi_sch_wand (bi_sch_var_fixed O) (bi_sch_fupd E E (bi_sch_fupd E' ∅ P)).

Definition bi_sch_staged_fupd (E: coPset) :=
  bi_sch_persistently
    (bi_sch_wand (bi_sch_var_mut O)
                 (bi_sch_cfupd E ∅ (bi_sch_sep (bi_sch_var_fixed 1) (bi_sch_var_mut 1)))).

Definition bi_sch_True := bi_sch_pure True.
Definition bi_sch_inv' (N: namespace) (P: bi_schema) : bi_schema :=
  bi_sch_persistently
    (bi_sch_forall coPset
       (λ E : coPset,
              bi_sch_wand (bi_sch_pure (↑N ⊆ E))
                          (bi_sch_fupd E (E ∖ ↑N)
                                       (bi_sch_sep P
                                                   (bi_sch_wand P
                                                                (bi_sch_fupd (E ∖ ↑N) E bi_sch_True)))))).
Definition bi_sch_inv (N: namespace) (P: bi_schema) : bi_schema :=
  bi_sch_inv' N (bi_sch_later P).

(* Four states for the inner invariant? *)

(* active, full => Qs
   cancelled => ?
   crashed => C * (...)

Definition inner_inv Qs Qr γcancel γp γqr :=
  (Qs ∨ (C * (Qr ∨ staged_done γqr) * (P ∨ staged_done γp))) ∨ staged_done γcancel *)


Definition bi_sch_staged_cases_noncancel :=
  bi_sch_or (bi_sch_var_mut O)
            (bi_sch_sep (bi_sch_var_mut 1) (bi_sch_sep (bi_sch_var_fixed O)
                                                       (bi_sch_or (bi_sch_var_fixed 1) (bi_sch_var_fixed 2)))).

Definition bi_sch_staged_cases :=
  bi_sch_or (bi_sch_staged_cases_noncancel)
            (bi_sch_var_mut 2).

Definition bi_sch_staged_cases_inv_wrapped N :=
  bi_sch_inv' N bi_sch_staged_cases.

Definition bi_sch_pending_done :=
  bi_sch_persistently (bi_sch_wand (bi_sch_var_mut 2)
                                   (bi_sch_wand (bi_sch_var_mut 3) (bi_sch_fupd ∅ ∅ (bi_sch_pure False)))).

Definition bi_sch_staged N E :=
  bi_sch_sep (bi_sch_staged_fupd E)
             (bi_sch_sep (bi_sch_pending_done)
                         (bi_sch_sep (bi_sch_var_mut 3)
                                     (bi_sch_staged_cases_inv_wrapped N))).

Definition inv_lvl `{!invG Σ} (k: nat) (N : namespace) (P : iProp Σ) : iProp Σ :=
  □ ∀ E, ⌜↑N ⊆ E⌝ -∗ |k={E,E ∖ ↑N}=> ▷ P ∗ (▷ P -∗ |k={E ∖ ↑N,E}=> True).

Lemma bi_sch_inv_interp `{!invG Σ} k N Ps Qs sch P:
  bi_schema_interp (S k) Ps Qs sch ≡ (▷ P)%I →
  bi_schema_interp (S k) Ps Qs (bi_sch_inv' N sch) ≡ inv_lvl k N P.
Proof.
  intros Hinterp. rewrite /inv_lvl.
  remember (S k) as k' eqn:Hlvl.
  repeat (rewrite ?Hinterp; rewrite ?bi_schema_interp_unfold //=).
  rewrite intuitionistically_into_persistently.
  do 2 f_equiv. intros E.
  repeat (rewrite bi_schema_interp_unfold //=; rewrite ?Hinterp).
  rewrite ?uPred_fupd_level_eq /uPred_fupd_level_def /bi_except_0 Hlvl.
  auto.
Qed.

Lemma bi_sch_staged_interp `{!invG Σ, !crashG Σ, !stagedG Σ} N E k γp γcancel Qs Qr P :
  bi_schema_interp (S k)
                   (bi_later <$> [C; P; staged_done γp])
                   (bi_later <$> [Qs; Qr; staged_done γcancel; staged_pending (1/2)%Qp γcancel])
                   (bi_sch_staged N E)
  ⊣⊢ □ (▷ Qs -∗ ▷ C -∗ |k={E}=> |k={∅, ∅}=> ▷ P ∗ ▷ Qr) ∗
     □ (▷ staged_done γcancel -∗ ▷ staged_pending (1/2)%Qp γcancel -∗ |k={∅}=> False) ∗
     ▷ staged_pending (1/2)%Qp γcancel ∗
     inv_lvl k N ((Qs ∨ (Qr ∗ C ∗ (P ∨ staged_done γp))) ∨ staged_done γcancel)%I.
Proof.
  remember (S k) as k' eqn:Hlvl.
  do 2 rewrite bi_schema_interp_unfold //=.
  do 2 rewrite bi_schema_interp_unfold //=.
  do 2 rewrite bi_schema_interp_unfold //=.
  rewrite Hlvl.
  erewrite bi_sch_fupd_interp; last first.
  { eapply bi_sch_fupd_interp. eauto. }
  do 1 rewrite bi_schema_interp_unfold.
  do 1 rewrite bi_schema_interp_unfold.
  do 1 rewrite bi_schema_interp_unfold.
  do 1 rewrite bi_schema_interp_unfold.
  do 1 rewrite (bi_schema_interp_unfold _ _ _ (bi_sch_sep _ _)).
  rewrite (bi_sch_inv_interp); last first.
  { repeat (rewrite ?bi_schema_interp_unfold /=).
    rewrite -?later_sep -?later_or /=.
    rewrite -?later_sep -?later_or /=.
    reflexivity. }
  f_equiv; [| f_equiv].
  - repeat (rewrite ?bi_schema_interp_unfold intuitionistically_into_persistently //=).
  - rewrite /bi_sch_pending_done.
    do 1 rewrite bi_schema_interp_unfold.
    do 1 rewrite bi_schema_interp_unfold.
    do 1 rewrite bi_schema_interp_unfold.
    do 1 rewrite bi_schema_interp_unfold.
    erewrite bi_sch_fupd_interp; last first.
    { rewrite //=. }
    do 1 rewrite bi_schema_interp_unfold //= ?intuitionistically_into_persistently. auto.
Qed.

(*
Lemma bi_sch_staged_interp `{!invG Σ, !crashG Σ, !stagedG Σ} E k γ Qs Qr P :
  bi_schema_interp (S k) (bi_later <$> [C; P; staged_done γ]) (bi_later <$> [Qs; Qr]) (bi_sch_staged E)
  ⊣⊢ (□ (▷ Qs -∗ ▷ C -∗ |k={E}=> |k={∅, ∅}=> ▷ P ∗ ▷ Qr) ∗ (▷ Qs ∨ (▷ Qr ∗ ▷ C ∗ ▷ staged_done γ)))%I.
Proof.
  remember (S k) as k' eqn:Hlvl.
  repeat (rewrite ?bi_schema_interp_unfold //=).
  rewrite /cfupd ?uPred_fupd_level_eq /uPred_fupd_level_def.
  rewrite Hlvl /bi_except_0 intuitionistically_into_persistently.
  done.
Qed.
*)

Lemma bi_sch_staged_interp_weak `{!invG Σ, !crashG Σ, !stagedG Σ} N E k γ Qs_mut P :
  bi_schema_interp (S k) (bi_later <$> [C; P; staged_done γ]) (bi_later <$> Qs_mut) (bi_sch_staged N E)
  ⊣⊢ let Qs := default emp%I (Qs_mut !! O) in
     let Qr := default emp%I (Qs_mut !! 1) in
     let cancel_done := default emp%I (Qs_mut !! 2) in
     let cancel_pending := default emp%I (Qs_mut !! 3) in
     □ (▷ Qs -∗ ▷ C -∗ |k={E}=> |k={∅, ∅}=> ▷ P ∗ ▷ Qr) ∗
     □ (▷ cancel_done -∗ ▷cancel_pending -∗ |k={∅}=> False) ∗
     ▷ cancel_pending ∗
     inv_lvl k N ((Qs ∨ (Qr ∗ C ∗ (P ∨ staged_done γ))) ∨ cancel_done)%I.
Proof.
  remember (S k) as k' eqn:Hlvl.
  do 2 rewrite bi_schema_interp_unfold //=.
  do 2 rewrite bi_schema_interp_unfold //=.
  do 2 rewrite bi_schema_interp_unfold //=.
  rewrite Hlvl.
  erewrite bi_sch_fupd_interp; last first.
  { eapply bi_sch_fupd_interp. eauto. }
  do 1 rewrite bi_schema_interp_unfold.
  do 1 rewrite bi_schema_interp_unfold.
  do 1 rewrite bi_schema_interp_unfold.
  do 1 rewrite bi_schema_interp_unfold.
  do 1 rewrite (bi_schema_interp_unfold _ _ _ (bi_sch_sep _ _)).
  f_equiv; [| f_equiv; [| f_equiv]].
  - repeat (rewrite ?bi_schema_interp_unfold intuitionistically_into_persistently //=).
    rewrite ?list_lookup_fmap.
    destruct (Qs_mut !! O); destruct (Qs_mut !! 1); destruct (Qs_mut !! 2) => //=;
    rewrite ?later_emp; auto.
  - rewrite /bi_sch_pending_done.
    do 1 rewrite bi_schema_interp_unfold.
    do 1 rewrite bi_schema_interp_unfold.
    do 1 rewrite bi_schema_interp_unfold.
    do 1 rewrite bi_schema_interp_unfold.
    erewrite bi_sch_fupd_interp; last first.
    { rewrite //=. }
    do 1 rewrite bi_schema_interp_unfold //= ?intuitionistically_into_persistently. auto.
    rewrite ?list_lookup_fmap.
    destruct (Qs_mut !! 2); destruct (Qs_mut !! 3) => //=;
    rewrite ?later_emp; auto.
  - do 1 rewrite bi_schema_interp_unfold //= ?intuitionistically_into_persistently. auto.
    rewrite ?list_lookup_fmap.
    destruct (Qs_mut !! 3);
    rewrite ?later_emp; auto.
  - eapply bi_sch_inv_interp => //=.
    rewrite ?list_lookup_fmap.
    destruct (Qs_mut !! O); [| rewrite -{1}later_emp];
    (destruct (Qs_mut !! 1); [| rewrite -{2}later_emp];
     (destruct (Qs_mut !! 2); [| rewrite -{3}later_emp])) => //=;
    repeat (rewrite -?later_sep -?later_or /=) => //=.
Qed.

(*
Lemma bi_sch_staged_interp_weak `{!invG Σ, !crashG Σ, !stagedG Σ} N E k γ Qs_mut P :
  bi_schema_interp (S k) (bi_later <$> [C; P; staged_done γ]) (bi_later <$> Qs_mut) (bi_sch_staged N E)
  ⊣⊢ let Qs := default emp%I (bi_later <$> (Qs_mut !! O)) in
     let Qr := default emp%I (bi_later <$> (Qs_mut !! 1)) in
     let cancel_done := default emp%I (bi_later <$> (Qs_mut !! 2)) in
     let cancel_pending := default emp%I (bi_later <$> (Qs_mut !! 3)) in
     □ (Qs -∗ ▷ C -∗ |k={E}=> |k={∅, ∅}=> ▷ P ∗ Qr) ∗
     □ (cancel_done -∗ cancel_pending -∗ |k={∅}=> False) ∗
     cancel_pending ∗
     inv_lvl k N ((Qs ∨ (Qr ∗ C ∗ (P ∨ staged_done γ))) ∨ cancel_done)%I.
Proof.
  remember (S k) as k' eqn:Hlvl.
  do 2 rewrite bi_schema_interp_unfold //=.
  do 2 rewrite bi_schema_interp_unfold //=.
  do 2 rewrite bi_schema_interp_unfold //=.
  rewrite Hlvl.
  erewrite bi_sch_fupd_interp; last first.
  { eapply bi_sch_fupd_interp. eauto. }
  do 1 rewrite bi_schema_interp_unfold.
  do 1 rewrite bi_schema_interp_unfold.
  do 1 rewrite bi_schema_interp_unfold.
  do 1 rewrite bi_schema_interp_unfold.
  do 1 rewrite (bi_schema_interp_unfold _ _ _ (bi_sch_sep _ _)).
  f_equiv; [| f_equiv; [| f_equiv]].
  - repeat (rewrite ?bi_schema_interp_unfold intuitionistically_into_persistently //=).
    rewrite ?list_lookup_fmap.
    destruct (Qs_mut !! O); destruct (Qs_mut !! 1); destruct (Qs_mut !! 2); auto.
  - rewrite /bi_sch_pending_done.
    do 1 rewrite bi_schema_interp_unfold.
    do 1 rewrite bi_schema_interp_unfold.
    do 1 rewrite bi_schema_interp_unfold.
    do 1 rewrite bi_schema_interp_unfold.
    erewrite bi_sch_fupd_interp; last first.
    { rewrite //=. }
    do 1 rewrite bi_schema_interp_unfold //= ?intuitionistically_into_persistently. auto.
    rewrite ?list_lookup_fmap.
    destruct (Qs_mut !! O); destruct (Qs_mut !! 1); destruct (Qs_mut !! 2); auto.
  - do 1 rewrite bi_schema_interp_unfold //= ?intuitionistically_into_persistently. auto.
    rewrite ?list_lookup_fmap.
    destruct (Qs_mut !! O); destruct (Qs_mut !! 1); destruct (Qs_mut !! 2); auto.
  - eapply bi_sch_inv_interp => //=.
    rewrite ?list_lookup_fmap.
    destruct (Qs_mut !! O); destruct (Qs_mut !! 1); destruct (Qs_mut !! 2); auto => //=.
    repeat (rewrite //= -?later_emp -?later_sep -?later_or /=).
    repeat (rewrite //= -?later_emp -?later_sep -?later_or /=).
    rewrite -?later_sep -?later_or /=. reflexivity. auto.
    rewrite -?later_sep -?later_or /=.
    reflexivity. }
  f_equiv; [| f_equiv].
  - repeat (rewrite ?bi_schema_interp_unfold intuitionistically_into_persistently //=).
  - rewrite /bi_sch_pending_done.
    do 1 rewrite bi_schema_interp_unfold.
    do 1 rewrite bi_schema_interp_unfold.
    do 1 rewrite bi_schema_interp_unfold.
    do 1 rewrite bi_schema_interp_unfold.
    erewrite bi_sch_fupd_interp; last first.
    { rewrite //=. }
    do 1 rewrite bi_schema_interp_unfold //= ?intuitionistically_into_persistently. auto.
Qed.
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

Definition staged_inv (k: nat) (N1 N2: namespace) E (γ: gname) (P: iProp Σ) : iProp Σ :=
  inv_mut k N1 (bi_sch_staged N2 E) [C; P; staged_done γ].

Definition staged_value (k: nat) (N1 N2: namespace) E (γp: gname) (Qs Qr P: iProp Σ) :=
  (∃ γcancel γr,
  staged_pending 1%Qp γr ∗
  staged_pending (1/2)%Qp γcancel ∗
  inv N2 ((Qs ∨ ((Qr ∨ staged_done γr) ∗ C ∗ (P ∨ staged_done γp))) ∨ staged_done γcancel) ∗
  inv_mut_full k N1 (bi_sch_staged N2 E) [Qs; (Qr ∨ (staged_done γr)); staged_done γcancel;
                                                 staged_pending (1/2)%Qp γcancel]
                                         [C; P; staged_done γp])%I.

Definition staged_value_disc (N2: namespace) (γp: gname) (Qs Qr P: iProp Σ) :=
  (∃ γcancel γr,
  staged_pending 1%Qp γr ∗
  staged_pending (1/2)%Qp γcancel ∗
  inv N2 ((Qs ∨ ((Qr ∨ staged_done γr) ∗ C ∗ (P ∨ staged_done γp))) ∨ staged_done γcancel))%I.

End staged_inv_defns.

Section inv.
Context `{!invG Σ, !stagedG Σ, !crashG Σ}.
Implicit Types i : positive.
Implicit Types N : namespace.
Implicit Types P Q R : iProp Σ.

Lemma staged_value_into_disc k N1 N2 E γp Qs Qr P :
  staged_value k N1 N2 E γp Qs Qr P -∗
  <disc> staged_value_disc N2 γp Qs Qr P.
Proof.
  iDestruct 1 as (??) "(Hp1&Hp2&#Hinv&_)".
  iModIntro. iExists _, _. by iFrame.
Qed.

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

Global Instance staged_persistent k N E γ P : Persistent (staged_inv k N1 N2 E γ P).
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

(*
Lemma staged_inv_iff N E E' γ γ' P Q :
  ▷ □ (P ↔ Q) -∗
  staged_inv N E E' γ γ' P -∗
  staged_inv N E E' γ γ' Q.
Proof.
  iIntros "#HPQ". iApply inv_iff. iNext. iAlways. iSplit.
  - iIntros "H". iDestruct "H" as (?? P0 P0') "(?&?&?&#HP0&Hcase)". iExists _, _, P0, P0'. iFrame.
    iAlways. iIntros. iSpecialize ("HP0" with "[$] [$]").
    iApply (step_fupdN_inner_wand' with "HP0"); eauto.
    iIntros "(?&$)". by iApply "HPQ".
  - iIntros "H". iDestruct "H" as (?? P0 P0') "(?&?&?&#HP0&Hcase)". iExists _, _, P0, P0'. iFrame.
    iAlways. iIntros. iSpecialize ("HP0" with "[$] [$]").
    iApply (step_fupdN_inner_wand' with "HP0"); eauto.
    iIntros "(?&$)". by iApply "HPQ".
Qed.
*)

Lemma pending_alloc:
  ⊢ |==> ∃ γ, staged_pending 1 γ.
Proof.
  iApply (own_alloc (Cinl 1%Qp)).
  { rewrite //=. }
Qed.

Lemma pending_split γ:
  staged_pending 1 γ ⊢ staged_pending (1/2)%Qp γ ∗ staged_pending (1/2)%Qp γ.
Proof. Admitted.

Lemma pending_join γ:
 staged_pending (1/2)%Qp γ ∗ staged_pending (1/2)%Qp γ ⊢  staged_pending 1 γ.
Proof. Admitted.

Lemma staged_inv_alloc k N1 N2 E E' P Q Qr:
  ▷ Q ∗ □ (C -∗ ▷ Q -∗ ▷ P ∗ ▷ Qr) -∗ |(S k)={E}=>
  ∃ γ, staged_inv (S k) N1 N2 E' γ P ∗ staged_value (S k) N1 N2 E' γ Q Qr P ∗ staged_pending 1%Qp γ.
Proof.
  iMod (pending_alloc) as (γp) "Hp".
  iMod (pending_alloc) as (γcancel) "Hc".
  iMod (pending_alloc) as (γr) "Hr".
  iIntros "(HQ&#HQP)".
  iMod (inv_alloc' _ N2 E
        (((Q ∨ ((Qr ∨ staged_done γr) ∗ C ∗ (P ∨ staged_done γp))) ∨ staged_done γcancel))%I
        with "[HQ]") as "#Hinv0".
  { repeat iLeft. auto. }

  iDestruct (pending_split with "Hc") as "(Hc1&Hc2)".
  iMod (inv_mut_alloc (S k) N1 E (bi_sch_staged N2 E')
                   [C; P; staged_done γp]
                   [Q; (Qr ∨ staged_done γr)%I; staged_done γcancel; staged_pending (1/2)%Qp γcancel]
          with "[Hc1]")
      as "(#Hi&Hmut)".
  { simpl fmap. rewrite bi_sch_staged_interp.
    iSplitL ""; [| iSplitL ""].
    - iModIntro. iIntros "HQ >HC". iModIntro.
      iApply fupd_level_mask_weaken; first by set_solver+.
      iDestruct ("HQP" with "[$] [$]") as "($&$)".
    - iModIntro. iIntros ">H1 >H2". iModIntro. iApply (pending_done with "[$] [$]").
    - iFrame.
      rewrite /inv_lvl.
      iModIntro. iIntros (E0 Hsub).
      iInv "Hinv0" as "H" "Hclo".
      iModIntro. iFrame.
  }
  iModIntro. iExists _. iFrame "# ∗". iExists _, _. iFrame "# ∗".
Qed.

Lemma staged_inv_open_modify E k N1 N2 E1 γ P Q Qr:
  N1 ## N2 →
  ↑N1 ⊆ E →
  ↑N2 ⊆ E →
  staged_value (S k) N1 N2 E1 γ Q Qr P -∗ |(S k)={E,E∖↑N1}=>
  (▷ Q ∗ (∀ Q' Qr', ▷ Q' ∗
   □ (▷ Q' -∗ |C={E1, ∅}_k=> P ∗ Qr') -∗ |(S k)={E∖↑N1,E}=> staged_value (S k) N1 N2 E1 γ Q' Qr' P)) ∨
  (▷ Qr ∗ C ∗ |(S k)={E∖↑N1, E}=> staged_value (S k) N1 N2 E1 γ Q True P).
Proof.
  (* XXX: clean this up, the encoding is very silly in some ways *)
  iIntros (???) "Hval".
  iDestruct "Hval" as (??) "(Hqr&Hcancel&#Hinv&Hval)".
  iMod (inv_mut_full_acc with "Hval") as "(Hinterp&Hclo)"; auto.
  iInv "Hinv" as "H" "Hclo'".
  iDestruct "H" as "[HQ|>Hfalse]"; last first.
  { iDestruct (pending_done with "[$] [$]") as %[]. }
  iDestruct (bi_sch_staged_interp with "Hinterp") as "(#Hwand&_&>Hcancel2&_)".
  iDestruct "HQ" as "[HQ|HQ]".
  - iDestruct (pending_join with "[$Hcancel $Hcancel2]") as "Hcancel".
    iMod (pending_upd_done with "Hcancel") as "Hcancel".
    iMod ("Hclo'" with "[Hcancel]") as "_".
    { iRight. eauto. }
    iModIntro. iLeft. iFrame. iIntros (Q' Qr') "(HQ'&#Hwand')".
    iClear "Hinv".
    iMod (pending_alloc) as (γcancel') "Hc".
    iMod (inv_alloc' _ N2 _
        (((Q' ∨ ((Qr' ∨ staged_done γr) ∗ C ∗ (P ∨ staged_done γ))) ∨ staged_done γcancel'))%I
        with "[HQ']") as "#Hinv0".
    { repeat iLeft. auto. }
    iDestruct (pending_split with "Hc") as "(Hc1&Hc2)".
    iMod ("Hclo" $! [Q'; (Qr' ∨ staged_done γr)%I;
                     staged_done γcancel'; staged_pending (1/2)%Qp γcancel'] with "[Hc1]").
    { rewrite bi_sch_staged_interp.
      iSplitL ""; [| iSplitL ""].
      - iIntros "!> HQ' >HC".  iMod ("Hwand'" with "[$] [$]") as "H".
        iModIntro. iMod "H" as "($&$)". auto.
      - iModIntro. iIntros ">H1 >H2". iModIntro. iApply (pending_done with "[$] [$]").
      - iFrame.
        rewrite /inv_lvl.
        iModIntro. iIntros (E0 Hsub).
        iInv "Hinv0" as "H" "Hclo".
        iModIntro. iFrame.
    }
    iModIntro. iExists _, _. iFrame "# ∗".
  - iRight. iDestruct "HQ" as "(HQr&>#HC&HP)".
    iFrame "HC".
    iDestruct "HQr" as "[HQr|>Hfalse]"; last first.
    { iDestruct (pending_done with "Hqr [$]") as %[]. }
    iMod (pending_upd_done with "Hqr") as "Hqr".
    iDestruct (pending_join with "[$Hcancel $Hcancel2]") as "Hcancel".
    iMod (pending_upd_done with "Hcancel") as "Hcancel".
    iMod ("Hclo'" with "[Hcancel]") as "_".
    { iRight. eauto. }
    iModIntro. iFrame.
    iClear "Hinv".
    iMod (pending_alloc) as (γr') "Hqr'".
    iMod (pending_alloc) as (γcancel') "Hc".
    iMod (inv_alloc' _ N2 _
        (((Q ∨ ((True ∨ staged_done γr') ∗ C ∗ (P ∨ staged_done γ))) ∨ staged_done γcancel'))%I
        with "[HP]") as "#Hinv0".
    { iLeft. iRight. iFrame "# ∗". by iLeft. }
    iDestruct (pending_split with "Hc") as "(Hc1&Hc2)".
    iMod ("Hclo" $! [Q; (True ∨ staged_done γr')%I;
                     staged_done γcancel'; staged_pending (1/2)%Qp γcancel'] with "[Hc2]").
    { rewrite bi_sch_staged_interp.
      iSplitL ""; [| iSplitL ""].
      - iIntros "!> HQ' _". iMod ("Hwand" with "[$] [$]") as "H".
        iModIntro. iMod "H" as "($&?)". iModIntro. by iLeft.
      - iModIntro. iIntros ">H1 >H2". iModIntro. iApply (pending_done with "[$] [$]").
      - iFrame.
        rewrite /inv_lvl.
        iModIntro. iIntros (E0 Hsub).
        iInv "Hinv0" as "H" "Hclo".
        iModIntro. iFrame.
    }
    iModIntro.  iExists _, _. iFrame "# ∗".
Qed.

Lemma staged_inv_disc_open_crash k E N2 γ P Q Qr:
  ↑N2 ⊆ E →
  □ (▷ Q -∗ ▷ C -∗ |k={E∖↑N2}=> |k={∅, ∅}=> ▷ P ∗ ▷ Qr) -∗
  staged_value_disc N2 γ Q Qr P -∗ C -∗ |k={E,E}=> ▷ Qr.
Proof.
  iIntros (?) "#Hwand".
  iDestruct 1 as (??) "(Hqr&Hqc&#Hinv)".
  iInv "Hinv" as "H" "Hclo'".
  iDestruct "H" as "[HQ|>Hfalse]"; last first.
  { iDestruct (pending_done with "[$] [$]") as %[]. }
  iIntros "#HC".
  iDestruct "HQ" as "[HQ|HQr]".
  - iMod ("Hwand" with "[$] [$]") as "H".
    iMod (fupd_level_intro_mask' _ ∅) as "Hclo''"; first by set_solver+.
    iMod ("H") as "(HP&$)".
    iMod "Hclo''" as "_".
    iMod (pending_upd_done with "Hqr") as "Hqr".
    iMod ("Hclo'" with "[HP Hqr]").
    { iNext. iLeft. iRight. by iFrame. }
    eauto.
  - iDestruct "HQr" as "([HQr|>Hfalse]&_&HP)"; last first.
    { iDestruct (pending_done with "Hqr [$]") as %[]. }
    iMod (pending_upd_done with "Hqr") as "Hqr".
    iMod ("Hclo'" with "[HP Hqr]").
    { iNext. iLeft. iRight. by iFrame. }
    by iFrame.
Qed.

(*
Lemma staged_inv_NC_open E k N E1 E2 γ P Q Qr:
  ↑N1 ⊆ E →
  E2 ⊆ E1 →
  NC ∗
  staged_value (S k) N1 N2 E1 γ Q Qr P -∗ |(S k)={E,E∖↑N}=>
  (▷ Q ∗ (∀ Q' Qr', ▷ Q' ∗
   □ (▷ Q' -∗ |C={E1, ∅}_k=> ▷ P ∗ ▷ Qr') -∗ |(S k)={E∖↑N,E}=> staged_value (S k) N E1 γ Q' Qr' P)).
Proof.
  iIntros (??) "(HNC&Hval)".
  iMod (staged_inv_open with "[$]") as "[H|(_&HC&_)]"; auto.
  iDestruct (NC_C with "[$] [$]") as %[].
Qed.
*)

Lemma staged_inv_weak_open E k N1 N2 E1 γ P:
  E1 ⊆ E ∖ ↑N1 ∖ ↑N2 →
  N1 ## N2 →
  ↑N1 ⊆ E →
  ↑N2 ⊆ E →
  staged_inv (S k) N1 N2 E1 γ P ∗
  staged_pending 1%Qp γ ∗
  C -∗ |(S k)={E,E}=> ▷ P.
Proof.
  iIntros (????) "(#Hinv&Hpending&#HC)".
  iMod (inv_mut_acc with "Hinv") as (Qs_mut) "(Hinv0&Hclo)"; auto.
  iDestruct (bi_sch_staged_interp_weak with "Hinv0") as "(#Hwand0&#Hwand1&Hpend&#Hinv0)".
  iDestruct ("Hinv0" $! (E ∖ ↑N1) with "[]") as "Hinv0'".
  { iPureIntro. set_solver. }
  iMod (fupd_level_le with "Hinv0'") as "(H&Hclo')"; first by lia.
  iDestruct "H" as "[HQ|Hfalse]"; last first.
  {
    iSpecialize ("Hwand1" with "[$] [$]").
    iMod (fupd_level_intro_mask' _ ∅) as "_"; first by set_solver+.
    iMod (fupd_level_le with "Hwand1") as %[]; lia.
  }
  iDestruct "HQ" as "[HQ|HQ]".
  - iMod (fupd_level_intro_mask' _ E1) as "Hclo''"; auto.
    iDestruct ("Hwand0" with "[$] [$]") as "Hwand".
    iMod (fupd_level_le with "Hwand") as "Hwand"; auto.
    iMod (fupd_level_intro_mask' _ ∅) as "Hclo'''"; first by set_solver.
    iMod (fupd_level_le with "Hwand") as "(HP&HQr)"; auto.
    iMod "Hclo'''" as "_".
    iMod "Hclo''" as "_".
    iMod (pending_upd_done with "[$]") as "#Hdone".
    iSpecialize ("Hclo'" with "[HQr]").
    { iLeft. iRight. iFrame "# ∗". }
    iMod (fupd_level_le with "Hclo'") as "_"; first by lia.
    iMod ("Hclo" with "[Hpend]").
    { iApply bi_sch_staged_interp_weak. iFrame "Hwand0 Hwand1 Hpend Hinv0". }
    iModIntro; eauto.
  - iDestruct "HQ" as "(HQr&_&[HP|>Hfalse])"; last first.
    { iDestruct (pending_done with "Hpending [$]") as %[]. }
    iMod (pending_upd_done with "[$]") as "#Hdone".
    iFrame.
    iSpecialize ("Hclo'" with "[HQr]").
    { iLeft. iRight. iFrame "# ∗". }
    iMod (fupd_level_le with "Hclo'") as "_"; first by lia.
    iMod ("Hclo" with "[Hpend]").
    { iApply bi_sch_staged_interp_weak. iFrame "Hwand0 Hwand1 Hpend Hinv0". }
    iModIntro; eauto.
Qed.

End inv.
