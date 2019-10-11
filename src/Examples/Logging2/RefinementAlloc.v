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
  Context `{!exmachG Σ, lockG Σ, !@cfgG (Inode.Op) (Inode.l) Σ,
            !inG Σ (authR (optionUR (exclR (listO natO)))),
            !inG Σ (authR (optionUR (exclR (listO pending_appendC)))),
            !inG Σ (authR (optionUR (exclR (prodO natO natO)))),
            !inG Σ (authR (optionUR (exclR natO)))}.

  (* because we use lemmas from RefinementLog2.v which accidentally got dependent on this kind of heap.. *)
  Context {hDone: gen_heapG nat (option pending_done) Σ}.

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

  Fixpoint insert_allocs (m : gmap nat nat) (l : list nat) (off : nat) :=
    match l with
    | nil => m
    | v :: l' =>
      <[off:=v]> (insert_allocs m l' (off+1))
    end.

  Theorem insert_allocs_none : forall l off off',
    off' < off ->
    insert_allocs ∅ l off !! off' = None.
  Proof.
    induction l0; simpl; intros.
    - reflexivity.
    - rewrite lookup_insert_ne; try lia.
      apply IHl0. lia.
  Qed.

  Hint Resolve insert_allocs_none.

  Theorem AllocInv_liftable : forall s,
    liftable (AllocInv s).
  Proof.
    unfold liftable.
    intros.
    iIntros (?) "H".
    iDestruct "H" as (sz) "[Hsz Has]".
    iDestruct "Has" as (l) "[%[%Has]]".
    iExists (<[allocator:=sz]> (insert_allocs ∅ l (allocator+1))).
    iSplitL.
    {
      iApply big_sepM_insert.
      eapply insert_allocs_none; lia.
      iFrame.

      clear H1 H2.
      generalize allocator as n. intro n.
      iInduction l as [|l] "IH" forall (n).
      - simpl. rewrite big_sepM_empty. iFrame.
      - simpl.
        iApply big_sepM_insert.
        eapply insert_allocs_none; lia.
        replace (n+1+0) with (n+1) by lia.
        iDestruct "Has" as "[Hn1 Has]".
        iFrame.
        iApply "IH".
        repeat setoid_rewrite <- plus_n_Sm.
        repeat rewrite <- plus_n_O.
        simpl.
        iFrame.
    }

    iIntros (?) "Hm".
    iDestruct (big_sepM_insert with "Hm") as "[Hsz Hm]".
    eapply insert_allocs_none; lia.

    iExists sz. iFrame.
    iExists l.
    iSplitR.
    { iPureIntro. auto. }
    iSplitR.
    { iPureIntro. auto. }

    clear H1 H2.
    generalize allocator as n. intro n.
    iInduction l as [|l] "IH" forall (n).
    - simpl. rewrite big_sepM_empty. iFrame.
    - simpl.
      iDestruct (big_sepM_insert with "Hm") as "[Hn1 Hm]".
      eapply insert_allocs_none; lia.
      replace (n+1+0) with (n+1) by lia.
      iFrame.
      iDestruct ("IH" with "Hm") as "Hm".
      iClear "IH".
      repeat setoid_rewrite <- plus_n_Sm.
      repeat rewrite <- plus_n_O.
      simpl.
      iFrame.
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


  Definition i0_lock := 0.
  Definition i1_lock := 1.
  Definition i0_data := 2.
  Definition i1_data := 4.

  Definition lN : namespace := (nroot.@"inode_lock").

  Definition inode_state (a : nat) (s : nat*nat) (h : heapT) :=
    (
      a ↦[h] fst s ∗
      (a+1) ↦[h] snd s
    )%I.

  Definition inode_inv (a : nat) (γs : gname) :=
    (
      ∃ data,
      own γs (● (Excl' data)) ∗
      inode_state a data memHeap
    )%I.

  Definition ExecInner γ0s γ1s :=
    (
      ∃ data0 data1,
      source_state (data0, data1) ∗
      own γ0s (◯ (Excl' data0)) ∗
      own γ1s (◯ (Excl' data1))
    )%I.

  Definition InodeInv :=
    (
      ∃ γ0lock γ1lock γ0s γ1s,
      source_ctx ∗
      is_lock lN γ0lock i0_lock (inode_inv i0_data γ0s) ∗
      is_lock lN γ1lock i1_lock (inode_inv i1_data γ1s) ∗
      inv iN (ExecInner γ0s γ1s)
    )%I.

  Import ExMachAPI.

  Definition read (i : nat) :=
    (
      match i with
      | 0 =>
        _ <- lock i0_lock;
        d0 <- read_mem i0_data;
        d1 <- read_mem (i0_data+1);
        _ <- unlock i0_lock;
        Ret (d0, d1)
      | 1 =>
        _ <- lock i1_lock;
        d0 <- read_mem i1_data;
        d1 <- read_mem (i1_data+1);
        _ <- unlock i1_lock;
        Ret (d0, d1)
      | _ => Ret (0, 0)
      end
    )%proc.

  Definition write2 (i : nat) (d0 d1 : nat) :=
    (
      txn <- begin;
      match i with
      | 0 =>
        _ <- lock i0_lock;
        _ <- write txn i0_data d0;
        _ <- write txn (i0_data+1) d1;
        _ <- commit txn;
        _ <- unlock i0_lock;
        Ret tt
      | 1 =>
        _ <- lock i1_lock;
        _ <- write txn i1_data d0;
        _ <- write txn (i1_data+1) d1;
        _ <- commit txn;
        _ <- unlock i1_lock;
        Ret tt
      | _ => Ret tt
      end
    )%proc.

  Lemma read_refinement {T} j K `{LanguageCtx Inode.Op _ T Inode.l K} i :
    {{{ j ⤇ K (Call (Inode.Read i)) ∗ Registered ∗ InodeInv }}}
      read i
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Hreg&#Hinv) HΦ".
    iDestruct "Hinv" as (g0l g1l g0s g1s) "(Hsource_inv & Hinv0 & Hinv1 & Hinv)".
    destruct i.
    - wp_bind.
      wp_lock "[Hlocked0 Hi0]".
      iDestruct "Hi0" as (i0) "[Hi0own [Hi00 Hi01]]".
      unfold memHeap.

      wp_bind.
      iInv "Hinv" as "H".
      iDestruct "H" as (d0 d1) ">H".
      iDestruct "H" as "(Hsource & Hshare0 & Hshare1)".

      iMod (ghost_step_lifting with "Hj Hsource_inv Hsource") as "(Hj&Hsource&_)".
      { simpl.
        intros. eexists. do 2 eexists; split; last by eauto. econstructor; eauto.
        econstructor.
      }
      { solve_ndisj. }
      unify_ghost.

      wp_step.

      iModIntro. iExists _, _. iFrame.

      wp_step.
      wp_unlock "[Hi0own Hi00 Hi01]".
      {
        iExists _. iFrame.
      }
      wp_ret. simpl. destruct d0.
      iApply "HΦ". iFrame.
    - admit.
  Admitted.

  Theorem inode_inv_liftable : forall d i,
    liftable (inode_state d i).
  Proof.
  Admitted.

  Lemma write2_refinement {T} j K `{LanguageCtx Inode.Op _ T Inode.l K} i d0 d1 :
    {{{ j ⤇ K (Call (Inode.Write2 i d0 d1)) ∗ Registered ∗ InodeInv }}}
      write2 i d0 d1
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Hreg&#Hinv) HΦ".
    iDestruct "Hinv" as (g0l g1l g0s g1s) "(Hsource_inv & Hinv0 & Hinv1 & Hinv)".
    destruct i.
    -
      iDestruct (begin_ok) as "Hwp_begin".
      wp_bind.
      iApply (wp_wand with "Hwp_begin").
      iIntros (?) "Htxn".
      iDestruct "Htxn" as (txn) "Htxn".

      wp_lock "[Hlocked0 Hi0]".
      iDestruct "Hi0" as (i0) "[Hi0own Hi0]".

      iPoseProof inode_inv_liftable as "Hliftable".
      iDestruct (lift_pred_ok with "[$Htxn Hi0 $Hliftable]") as "[Htxn Hi0]". iFrame.
      iDestruct "Hi0" as "[Hi00 Hi01]".

      iDestruct (write_ok with "[$Htxn $Hi00]") as "Hwp_write".
      wp_bind.
      iApply (wp_wand with "Hwp_write").
      iIntros (?) "[Htxn Hi00]".

      iDestruct (write_ok with "[$Htxn $Hi01]") as "Hwp_write".
      wp_bind.
      iApply (wp_wand with "Hwp_write").
      iIntros (?) "[Htxn Hi01]".

      iPoseProof (inode_inv_liftable _ (d0,d1)) as "Hliftable2".
      iDestruct (commit_pred_ok with "[$Htxn $Hliftable2 Hi00 Hi01]") as "Hwp_commit".
      iFrame.
      wp_bind.
      iApply (wp_wand with "Hwp_commit").
      iIntros (?) "Hi0".

      wp_bind.

      iInv "Hinv" as "H".
      iDestruct "H" as (dd0 dd1) ">H".
      iDestruct "H" as "(Hsource & Hshare0 & Hshare1)".

      iMod (ghost_step_lifting with "Hj Hsource_inv Hsource") as "(Hj&Hsource&_)".
      { simpl.
        intros. eexists. do 2 eexists; split; last by eauto. econstructor; eauto.
        econstructor.
      }
      { solve_ndisj. }
      unify_ghost.

      iMod (ghost_var_update _ (d0, d1) with "Hi0own Hshare0") as "[Hi0own Hshare0]".

      iDestruct (wp_unlock_open with "Hinv0 Hlocked0") as "Hunlock".
      2: iApply (wp_wand with "[Hi0own Hi0 Hunlock]").
      2: iApply "Hunlock".
      solve_ndisj.

      iExists _. iFrame.

      iIntros.
      iModIntro. iExists _, _. iFrame.

      wp_ret.
      iApply "HΦ". iFrame.
    - admit.
  Admitted.
