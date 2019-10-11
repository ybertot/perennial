From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement CSL.NamedDestruct.
Require Import AllocAPI ImplAlloc ExMach.WeakestPre ExMach.RefinementAdequacy.
Require Import Logging2.Helpers.
Require Import Equality.
Require Import RefinementLog2.
Set Default Proof Using "All".
Unset Implicit Arguments.

From Tactical Require Import UnfoldLemma.


Section refinement_triples.
  Context `{!exmachG Σ, lockG Σ, !@cfgG (Alloc.Op) (Alloc.l) Σ,
            !inG Σ (authR (optionUR (exclR (listO natO)))),
            !inG Σ (authR (optionUR (exclR natO)))}.

  Import ExMach.

  Context {hTxn: gen_heapG nat (option (gen_heapG nat nat Σ)) Σ}.
  Notation "l ↦[ t ] v " := (mapsto (hG := t) l 1 v)
    (at level 20, t at level 50, format "l  ↦[ t ]  v") : bi_scope.

  Definition txn_valid (txn : nat) (hT : gen_heapG nat nat Σ) :=
    (
      txn ↦[hTxn] (Some hT) ∗
      ∀ a v, a ↦[hT] v -∗ ∃ v0, a m↦ v0
    )%I.

  Axiom begin_ok : forall s E,
    (
      WP ImplAlloc.begin @ s; E {{
        txn,
        ∃ hT, txn_valid txn hT
      }}
    )%I.

  Axiom lift_ok : forall txn hT liftm,
    (
      ( txn_valid txn hT ∗
        [∗ map] a ↦ v ∈ liftm, a m↦ v
      ) -∗
      (
        txn_valid txn hT ∗
        [∗ map] a ↦ v ∈ liftm, a ↦[hT] v
      )
    )%I.

  Definition heapT := @gen_heapG nat nat Σ nat_eq_dec nat_countable.
  Definition memHeap := exmachG0.(@exm_mem_inG Σ).
  Definition liftable (P : heapT -> iProp Σ) :=
    (
      ∀ (h1 : @gen_heapG nat nat Σ nat_eq_dec nat_countable),
      P h1 -∗
      ∃ m,
      ([∗ map] a ↦ v ∈ m, a ↦[h1] v) ∗
      ∀ (h2 : @gen_heapG nat nat Σ nat_eq_dec nat_countable),
      ([∗ map] a ↦ v ∈ m, a ↦[h2] v) -∗
      P h2
    )%I.

  Theorem lift_pred_ok : forall txn hT P,
    (
      ( txn_valid txn hT ∗
        P memHeap ∗
        liftable P
      ) -∗
      (
        txn_valid txn hT ∗
        P hT
      )
    )%I.
  Proof.
    iIntros (???) "(Htxn & Hp & Hliftable)".
    unfold liftable.
    iDestruct ("Hliftable" with "Hp") as (m) "[Hm Hp]".
    iDestruct (lift_ok with "[$Htxn $Hm]") as "[Htxn Hm]".
    iFrame.
    iApply "Hp".
    iFrame.
  Qed.

  Axiom write_ok : forall s E txn a v v0 hT,
    (
      (
        txn_valid txn hT ∗
        a ↦[hT] v0
      )
      -∗
      WP ImplAlloc.write txn a v @ s; E {{
        tt,
        txn_valid txn hT ∗
        a ↦[hT] v
      }}
    )%I.

  Axiom read_ok : forall s E txn a v0 hT,
    (
      (
        txn_valid txn hT ∗
        a ↦[hT] v0
      )
      -∗
      WP ImplAlloc.read txn a @ s; E {{
        v,
        txn_valid txn hT ∗
        a ↦[hT] v0 ∗
        ⌜ v = v0 ⌝
      }}
    )%I.

  Axiom commit_ok : forall s E txn m hT,
    (
      (
        txn_valid txn hT ∗
        [∗ map] a ↦ v ∈ m, a ↦[hT] v
      )
      -∗
      WP ImplAlloc.commit txn @ s; E {{
        r,
        [∗ map] a ↦ v ∈ m, a m↦ v
      }}
    )%I.

  Theorem commit_pred_ok : forall s E txn P hT,
    (
      (
        txn_valid txn hT ∗
        liftable P ∗
        P hT
      )
      -∗
      WP ImplAlloc.commit txn @ s; E {{
        r,
        P memHeap
      }}
    )%I.
  Proof.
    iIntros (?????) "(Htxn & Hliftable & Hp)".
    iDestruct ("Hliftable" with "Hp") as (m) "[Hm Hp]".
    iDestruct (commit_ok with "[$Htxn $Hm]") as "Hcom".
    iApply (wp_wand with "Hcom").
    iIntros (?) "Hm".
    iApply "Hp".
    iFrame.
  Qed.


  Definition AllocState (h : heapT) (off : nat) (sz : nat) (freeset : gset nat) :=
    (
      ∃ freevals,
      ⌜ length freevals = sz ⌝ ∗
      ⌜ forall i, i < sz -> i ∈ freeset <-> freevals !! i = Some 0 ⌝ ∗
      ([∗ list] i ↦ v ∈ freevals, (off+i) ↦[h] v)
    )%I.

  Definition AllocInv (freeset : gset nat) (h : heapT) :=
    ( ∃ sz,
      allocator ↦[h] sz ∗
      AllocState h (allocator+1) sz freeset
    )%I.

  Theorem alloc_below_ok : forall s E txn off n hT sz fs,
    (
      (
        txn_valid txn hT ∗
        AllocState hT off sz fs ∗
        ⌜ n <= sz ⌝
      )
      -∗
      WP ImplAlloc.alloc_below txn off n @ s; E {{
        r,
        txn_valid txn hT ∗
        match r with
        | None => AllocState hT off sz fs
        | Some a => AllocState hT off sz (fs ∖ {[a]})
        end
      }}
    )%I.
  Proof.
    intros.
    iIntros "(Htxn & Has & Hp)".
    iDestruct "Has" as (freevals) "[%[%Has]]".
    iInduction n as [|n] "IH"; simpl.
    - wp_ret. iFrame.
      iExists _. iFrame. iPureIntro. intuition.
    - iPure "Hp" as Hp.
      edestruct @lookup_lt_is_Some_2 with (i := n) (l := freevals). lia.
      destruct (decide (x = 0)).
      + iDestruct (big_sepL_insert_acc with "Has") as "[Hn Hother]". eauto.
        wp_bind.
        iDestruct (read_ok with "[$Htxn $Hn]") as "Hwp_read".
        iApply (wp_wand with "Hwp_read").
        iIntros (?) "[Htxn [Hn%]]"; subst.
        iDestruct (write_ok with "[$Htxn $Hn]") as "Hwp_write".
        wp_bind.
        iApply (wp_wand with "Hwp_write").
        iIntros (?) "[Htxn Hn]".
        wp_ret. iFrame.
        iDestruct ("Hother" with "Hn") as "Hfv".
        iExists _. iFrame.
        iPureIntro. intuition. rewrite insert_length. auto.
        * destruct (decide (i = n)); subst.
          { admit. }
          { admit. }
        * destruct (decide (i = n)); subst.
          { admit. }
          { admit. }
      + iDestruct (big_sepL_lookup_acc with "Has") as "[Hn Hother]". eauto.
        wp_bind.
        iDestruct (read_ok with "[$Htxn $Hn]") as "Hwp_read".
        iApply (wp_wand with "Hwp_read").
        iIntros (?) "[Htxn [Hn%]]"; subst.
        destruct (decide (x = 0)); try congruence.
        iDestruct ("Hother" with "Hn") as "Hfv".
        iApply ("IH" with "[$Htxn] [$Hfv]").
        iPureIntro. lia.
  Admitted.

  Theorem alloc_ok : forall s E txn hT fs,
    (
      (
        txn_valid txn hT ∗
        AllocInv fs hT
      )
      -∗
      WP ImplAlloc.alloc txn @ s; E {{
        r,
        txn_valid txn hT ∗
        match r with
        | None => AllocInv fs hT
        | Some a => AllocInv (fs ∖ {[a]}) hT
        end
      }}
    )%I.
  Proof.
    intros.
    iIntros "[Htxn Hinv]".
    iDestruct "Hinv" as (sz) "[Hsz Has]".
    wp_bind.
    iDestruct (read_ok with "[$Htxn $Hsz]") as "Hwp_read".
    iApply (wp_wand with "Hwp_read").
    iIntros (?) "[Htxn [Hsz%]]"; subst.
    iDestruct (alloc_below_ok with "[$Htxn $Has]") as "Hwp_allow_below".
    2: iApply (wp_wand with "Hwp_allow_below").
    iPureIntro. lia.
    iIntros (?) "[Htxn Hret]".
    iFrame.
    destruct a.
    - iExists _. iFrame.
    - iExists _. iFrame.
  Qed.

  Definition mem_lock := 0.
  Definition aN : namespace := (nroot.@"alloc_lock").
  Definition BigInv :=
    (
      ∃ γlock,
      is_lock aN γlock mem_lock (∃ AS, AllocInv AS memHeap)
    )%I.

  Definition alloc_and_commit :=
    (
      txn <- begin;
      _ <- ExMachAPI.lock mem_lock;
      r <- alloc txn;
      _ <- commit txn;
      _ <- ExMachAPI.unlock mem_lock;
      Ret r
    )%proc.

  Theorem AllocInv_liftable : forall s,
    liftable (AllocInv s).
  Proof.
    unfold liftable.
    intros.
    iIntros (?) "H".
    iDestruct "H" as (sz) "[Hsz Has]".
  Admitted.

  Theorem alloc_and_commit_ok :
    (
      (
        BigInv
      )
      -∗
      WP alloc_and_commit {{
        r,
        BigInv
      }}
    )%I.
  Proof.
    intros.
    iIntros "Hinv".
    iDestruct "Hinv" as (l) "#Hinv".

    iDestruct (begin_ok) as "Hwp_begin".
    wp_bind.
    iApply (wp_wand with "Hwp_begin").
    iIntros (?) "Htxn".
    iDestruct "Htxn" as (txn) "Htxn".

    wp_bind.
    wp_lock "[Hlocked Hopen]".
    iDestruct "Hopen" as (AS) "Hopen".

    iPoseProof AllocInv_liftable as "Hliftable".
    iDestruct (lift_pred_ok with "[$Htxn Hopen $Hliftable]") as "[Htxn Hopen]".
    iFrame.

    iDestruct (alloc_ok with "[$Htxn $Hopen]") as "Hwp_alloc".
    wp_bind.
    iApply (wp_wand with "Hwp_alloc").
    iIntros (?) "[Htxn Hres]".

    destruct a0.
    - iPoseProof AllocInv_liftable as "Hliftable2".
      iDestruct (commit_pred_ok with "[$Htxn $Hliftable2 $Hres]") as "Hwp_commit".
      wp_bind.
      iApply (wp_wand with "Hwp_commit").
      iIntros (?) "Hopen".

      wp_unlock "[Hopen]". iExists _. iFrame.
      wp_ret.
      iExists _. iApply "Hinv".

    - iDestruct (commit_pred_ok with "[$Htxn $Hliftable $Hres]") as "Hwp_commit".
      wp_bind.
      iApply (wp_wand with "Hwp_commit").
      iIntros (?) "Hopen".

      wp_unlock "[Hopen]". iExists _. iFrame.
      wp_ret.
      iExists _. iApply "Hinv".
  Qed.
