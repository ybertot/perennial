From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement CSL.NamedDestruct.
Require Import Log2API ImplLog2 ExMach.WeakestPre ExMach.RefinementAdequacy.
Require Import Logging2.Helpers.
Require Import Equality.
Set Default Proof Using "All".
Unset Implicit Arguments.

From Tactical Require Import UnfoldLemma.

Inductive pending_append :=
| Pending (blocks : list nat) (j: nat) {T2} K `{LanguageCtx _ bool T2 Log2.l K}.

Inductive pending_done :=
| PendingDone (j: nat) {T2} K `{LanguageCtx _ bool T2 Log2.l K}.


Canonical Structure pending_appendC :=
  leibnizO pending_append.


(* TODO: move out and re-use this *)
Section gen_heap.
Context `{hG: gen_heapG L V Σ}.
Lemma gen_heap_init_to_bigOp σ:
  own (gen_heap_name hG) (◯ to_gen_heap σ)
      -∗ [∗ map] i↦v ∈ σ, mapsto i 1 v .
Proof.
  induction σ using map_ind.
  - iIntros. rewrite //=.
  - iIntros "Hown".
    rewrite big_opM_insert //.
    iAssert (own (gen_heap_name hG) (◯ to_gen_heap m) ∗ (mapsto i 1 x))%I
      with "[Hown]" as "[Hrest $]".
    {
      rewrite mapsto_eq /mapsto_def //.
      rewrite to_gen_heap_insert.
      rewrite (insert_singleton_op (to_gen_heap m) i (1%Qp, to_agree x));
        last by apply lookup_to_gen_heap_None.
      rewrite auth_frag_op. iDestruct "Hown" as "(?&?)". iFrame.
    }
    by iApply IHσ.
Qed.

Lemma gen_heap_bigOpM_dom (σ: gmap L V) (q: Qp):
  ([∗ map] i↦v ∈ σ, mapsto i q v)
    -∗ [∗ set] i ∈ dom (gset L) σ, ∃ v, ⌜ σ !! i = Some v ⌝ ∗ mapsto i q v .
Proof.
  iIntros "H". iApply big_sepM_dom.
  iApply (big_sepM_mono with "H").
  iIntros (k x Hlookup) "H".
  iExists _. iFrame. eauto.
Qed.

Lemma gen_heap_bigOp_split (σ: gmap L V) (q: Qp):
  ([∗ map] i↦v ∈ σ, mapsto i q v)
    -∗ ([∗ map] i↦v ∈ σ, mapsto i (q/2) v) ∗ ([∗ map] i↦v ∈ σ, mapsto i (q/2) v).
Proof.
  rewrite -big_sepM_sep. apply big_sepM_mono.
  iIntros (?? ?) "($&$)".
Qed.

Lemma mapsto_split (i : L) (q : Qp) (v : V):
  mapsto i q v -∗ mapsto i (q/2) v ∗ mapsto i (q/2) v.
Proof.
  iIntros "($&$)".
Qed.

End gen_heap.


Fixpoint list_inserts {T M} {Insert: Insert nat T M} (l : M) (off : nat) (vs : list T) :=
  match vs with
  | nil => l
  | v :: vs' =>
    list_inserts (<[off:=v]> l) (off+1) vs'
  end.

Lemma insert_list_insert_commute {T} : forall (p : list T) off v off' (l : list T),
  off < off' ->
  list_inserts (<[off:=v]> l) off' p = <[off:=v]> (list_inserts l off' p).
Proof.
  induction p; simpl; intros; auto.
  rewrite <- IHp; try lia.
  rewrite list_insert_commute; try lia.
  reflexivity.
Qed.

Lemma insert_list_insert_commute_map
  {T MM}
  {_: FMap MM}
  {_: ∀ A : Type, Lookup nat A (MM A)}
  {_: ∀ A : Type, Empty (MM A)}
  {PA: ∀ A : Type, PartialAlter nat A (MM A)}
  {_: OMap MM}
  {_: Merge MM}
  {_: ∀ A : Type, FinMapToList nat A (MM A)}
  {_: FinMap nat MM}
  :
    forall (p : list T) off (v : T) off' (m : MM T),
      off < off' ->
      list_inserts (<[off:=v]> m) off' p = <[off:=v]> (list_inserts m off' p).
Proof.
  induction p; simpl; intros; auto.
  rewrite <- IHp; try lia.
  rewrite insert_commute; try lia.
  reflexivity.
Qed.

Lemma lookup_list_insert_lt
  {T MM}
  {_: FMap MM}
  {_: ∀ A : Type, Lookup nat A (MM A)}
  {_: ∀ A : Type, Empty (MM A)}
  {PA: ∀ A : Type, PartialAlter nat A (MM A)}
  {_: OMap MM}
  {_: Merge MM}
  {_: ∀ A : Type, FinMapToList nat A (MM A)}
  {_: FinMap nat MM}
  :
    forall (p : list T) off off' (m : MM T),
      off < off' ->
      list_inserts m off' p !! off = m !! off.
Proof.
  induction p; simpl; intros; auto.
  rewrite insert_list_insert_commute_map; try lia.
  rewrite lookup_insert_ne; try lia.
  apply IHp; try lia.
Qed.

Lemma lookup_list_insert_plus
  {T MM}
  {_: FMap MM}
  {_: ∀ A : Type, Lookup nat A (MM A)}
  {_: ∀ A : Type, Empty (MM A)}
  {PA: ∀ A : Type, PartialAlter nat A (MM A)}
  {_: OMap MM}
  {_: Merge MM}
  {_: ∀ A : Type, FinMapToList nat A (MM A)}
  {_: FinMap nat MM}
  :
    forall (p : list T) off x (m : MM T),
      x < length p ->
      list_inserts m off p !! (off+x) = p !! x.
Proof.
  induction p; simpl; intros; auto.
  - lia.
  - rewrite insert_list_insert_commute_map; try lia.
    destruct x; simpl.
    + replace (off+0) with off by lia. rewrite lookup_insert. auto.
    + rewrite lookup_insert_ne; try lia.
      rewrite <- plus_n_Sm. rewrite <- plus_Sn_m. replace (S off) with (off + 1) by lia. rewrite IHp.
      auto. lia.
Qed.

Lemma list_inserts_length {T} : forall vs (l : list T) off,
  length (list_inserts l off vs) = length l.
Proof.
  induction vs; simpl; intros; auto.
  rewrite IHvs.
  rewrite insert_length.
  auto.
Qed.

Lemma take_list_inserts_le {T} : forall (p : list T) off off' l,
  off <= off' ->
  take off (list_inserts l off' p) = take off l.
Proof.
  induction p; simpl; intros; auto.
  rewrite insert_list_insert_commute; try lia.
  rewrite take_insert; auto.
  rewrite IHp; auto.
  lia.
Qed.

Lemma take_list_inserts {T} : forall (p : list T) off bs,
  off + length p <= length bs ->
  take (off + length p) (list_inserts bs off p) = take off (list_inserts bs off p) ++ p.
Proof.
  induction p; simpl; intros.
  - rewrite app_nil_r. replace (off+0) with off by lia. auto.
  - replace (off + S (length p)) with (S off + length p) by lia.
    replace (off + 1) with (S off) by lia.
    rewrite IHp; clear IHp.
    2: {
      rewrite insert_length. lia.
    }
    rewrite take_list_inserts_le; try lia.
    rewrite take_list_inserts_le; try lia.
    replace (a :: p) with ([a] ++ p) by reflexivity.
    rewrite app_assoc.
    f_equal.

    assert (off < length bs) by lia.
    pose proof (list_lookup_insert _ _ a H0).

    apply take_drop_middle in H1.
    rewrite <- H1 at 1.
    replace (S off) with (off + 1) by lia.
    rewrite take_plus_app.
    2: {
      rewrite firstn_length_le; auto.
      rewrite insert_length. lia.
    }
    reflexivity.
Qed.


Section refinement_triples.
  Context `{!exmachG Σ, lockG Σ, !@cfgG (Log2.Op) (Log2.l) Σ,
            !inG Σ (authR (optionUR (exclR (listO natO)))),
            !inG Σ (authR (optionUR (exclR (listO pending_appendC)))),
            !inG Σ (authR mnatUR)}.

  (* hDone maps transaction IDs to the thread ID and its K value that's waiting for completion *)
  Context {hDone: gen_heapG nat pending_done Σ}.
  Import ExMach.

  Notation "l s↦{ q } v " := (mapsto (hG := hDone) l q v)
    (at level 20, q at level 50, format "l  s↦{ q }  v") : bi_scope.


  Definition ptr_map (len_val : nat) (blocks : list nat) :=
    ( log_commit d↦ len_val ∗
      [∗ list] pos ↦ b ∈ blocks, log_data pos d↦ b
    )%I.


  Definition pending_blocks (pa : pending_append) : list nat :=
    match pa with
    | Pending blocks _ _ => blocks
    end.

  Definition pending_append_j (pa : pending_append) :=
    match pa with
    | Pending _ j _ => j
    end.

  Definition pending_call (pa : pending_append) :=
    (
      match pa with
      | Pending blocks j K =>
        j ⤇ K (Call (Log2.Append blocks))
      end
    )%I.

  Global Instance pending_call_timeless pa:
    Timeless (pending_call pa).
  Proof. destruct pa; apply _. Qed.

  Definition pending_ret (pd : pending_done) :=
    (
      match pd with
      | PendingDone j K =>
        j ⤇ K (Ret true)
      end
    )%I.

  Definition pending_j (pd : pending_done) :=
    match pd with
    | PendingDone j _ => j
    end.

  Definition pending_append_to_done (pa : pending_append) :=
    match pa with
    | Pending _ j K => PendingDone j K
    end.

  Global Instance pending_ret_timeless pd:
    Timeless (pending_ret pd).
  Proof. destruct pd; apply _. Qed.


  (**
    Notes for later:
    - Can we use a resource algebra like the cmra-based list.v to replace diskpending?
   *)

  Definition ExecInner γmemblocks γdiskpending γcommit_id γcommit_id_exact :=
    (∃ (len_val : nat) (bs : list nat) (memblocks : list nat)
       (pending : list pending_append) (diskpending : list pending_append)
       (next_committed_id : nat)
       (committed_pending : gmap nat pending_done)
       (txid_map : gmap nat pending_done),

        source_state (firstn len_val bs) ∗
        ⌜ len_val <= length bs ⌝ ∗
        ⌜ length bs = log_size ⌝ ∗
        ptr_map len_val bs ∗
        own γmemblocks (◯ (Excl' memblocks)) ∗
        ⌜ firstn len_val memblocks = firstn len_val bs ⌝ ∗
        ⌜ skipn len_val memblocks = concat (map pending_blocks pending) ⌝ ∗
        ( [∗ list] pending_off ↦ p ∈ pending, pending_call p ∗ (next_committed_id + pending_off) s↦{1/2} (pending_append_to_done p)) ∗

        own γcommit_id (● (next_committed_id : mnat)) ∗
        own γcommit_id_exact (◯ (Excl' next_committed_id)) ∗
        ⌜ ∀ txid, txid < next_committed_id -> is_Some (txid_map !! txid) -> is_Some (committed_pending !! txid) ⌝ ∗
        ⌜ ∀ txid, txid >= next_committed_id -> committed_pending !! txid = None ⌝ ∗
        ⌜ ∀ txid, txid >= next_committed_id + length pending -> txid_map !! txid = None ⌝ ∗
        ( [∗ map] txid ↦ done ∈ committed_pending, pending_ret done ∗ txid s↦{1/2} done ) ∗
        gen_heap_ctx txid_map ∗

        (* diskpending is a snapshot that [disk_append] took and is in
           the process of writing to disk *)
        own γdiskpending (◯ (Excl' diskpending)) ∗
        ⌜ firstn (length diskpending) pending = diskpending ⌝
    )%I.

  (* Holding the lock guarantees the value of the log length will not
     change out from underneath you -- this is enforced by granting leases *)

  Definition lease_map (len_val : nat) (blocks : list nat) :=
    ( lease log_commit len_val ∗
      [∗ list] pos ↦ b ∈ blocks, lease (log_data pos) b
    )%I.

  Definition DiskLockInv γdiskpending γcommit_id_exact :=
    (∃ (len_val : nat) (bs : list nat) (diskpendingprefix : list pending_append) (next_committed_id : nat),
        lease_map len_val bs ∗
        ⌜ len_val <= length bs ⌝ ∗
        ⌜ length bs = log_size ⌝ ∗
        own γdiskpending (● (Excl' diskpendingprefix)) ∗
        own γcommit_id_exact (● (Excl' next_committed_id))
    )%I.

  Definition mem_map (len_val : nat) (blocks : list nat) :=
    ( mem_count m↦ len_val ∗
      [∗ list] pos ↦ b ∈ blocks, mem_data pos m↦ b )%I.

  Definition MemLockInv γmemblocks :=
    (∃ (len_val : nat) (memblocks : list nat),
      mem_map len_val memblocks ∗
      ⌜ length memblocks = log_size ⌝ ∗
      ⌜ len_val <= length memblocks ⌝ ∗
      own γmemblocks (● (Excl' (firstn len_val memblocks)))
    )%I.

  (* Post-crash, pre recovery we know the ptr mapping is in a good state w.r.t the
     abstract state, and the lock must have been reset 0 *)

  Definition CrashInner :=
    (∃ (len_val : nat) (bs : list nat) (memblocks : list nat),
        source_state (firstn len_val bs) ∗
        ⌜ len_val <= length bs /\ length bs = log_size ⌝ ∗
        ptr_map len_val bs ∗
        lease_map len_val bs ∗
        log_lock m↦ 0 ∗
        mem_lock m↦ 0 ∗
        mem_map 0 memblocks ∗
        ⌜ length memblocks = log_size ⌝
        )%I.

  Definition dN : namespace := (nroot.@"disklock").
  Definition mN : namespace := (nroot.@"memlock").
  Definition iN : namespace := (nroot.@"inner").

  Definition ExecInv γcommit_id :=
    ( source_ctx ∗
      ∃ γmemblocks γdiskpending γcommit_id_exact,
      ∃ γdisklock, is_lock dN γdisklock log_lock (DiskLockInv γdiskpending γcommit_id_exact) ∗
      ∃ γmemlock, is_lock mN γmemlock mem_lock (MemLockInv γmemblocks) ∗
      inv iN (ExecInner γmemblocks γdiskpending γcommit_id γcommit_id_exact))%I.
  Definition CrashInv := (source_ctx ∗ inv iN CrashInner)%I.

  Lemma big_sepM_insert {A: Type} {P: nat -> A -> iPropI Σ} m i x :
    m !! i = None →
    ([∗ map] k↦y ∈ <[i:=x]> m, P k y) ⊣⊢ P i x ∗ [∗ map] k↦y ∈ m, P k y.
  Proof. apply big_opM_insert. Qed.

  Lemma big_sepL_insert_acc {A: Type} {P: nat -> A -> iPropI Σ} m i x :
    m !! i = Some x →
    ([∗ list] k↦y ∈ m, P k y) ⊢
      P i x ∗ (∀ x', P i x' -∗ ([∗ list] k↦y ∈ <[i:=x']> m, P k y)).
  Proof.
    intros.
    rewrite big_sepL_delete //.
    iIntros "H".
    iDestruct "H" as "[HP Hlist]".
    iFrame.
    iIntros "% HP".
    assert (i < length m)%nat as HLength by (apply lookup_lt_is_Some_1; eauto).
    assert (i = (length (take i m) + 0)%nat) as HCidLen.
    { rewrite take_length_le. by rewrite -plus_n_O. lia. }
    replace (insert i) with (@insert _ _ _ (@list_insert A) (length (take i m) + 0)%nat) by auto.
    remember (length _ + 0)%nat as K.
    replace m with (take i m ++ [x] ++ drop (S i) m) by (rewrite take_drop_middle; auto).
    subst K.
    rewrite big_opL_app.
    rewrite big_opL_app. simpl.
    rewrite insert_app_r.
    rewrite big_opL_app.
    replace (x :: drop (S i) m) with ([x] ++ drop (S i) m) by reflexivity.
    rewrite insert_app_l; [| simpl; lia ].
    rewrite big_opL_app. simpl.
    rewrite -HCidLen.
    iDestruct "Hlist" as "[HListPre [HListMid HListSuf]]".
    iFrame.
    iSplitL "HListPre".
    {
      iApply big_sepL_proper; iFrame.
      iIntros.
      apply lookup_lt_Some in x2.
      pose proof (firstn_le_length i m).
      destruct (decide (x0 = i)); try lia.
      iSplit; iIntros; iFrame.
    }
    {
      iApply big_sepL_proper; iFrame.
      iIntros.
      destruct (decide (strings.length (take i m) + S x0 = i)); try lia.
      iSplit; iIntros; iFrame.
    }
  Qed.

  Lemma big_sepM_list_inserts {T}
    {Φ : nat -> T -> iPropI Σ} : forall l (m : gmap nat T) off,
      (forall i, i >= off -> m !! i = None) →
      ([∗ map] k↦y ∈ (list_inserts m off l), Φ k y) ⊣⊢ ([∗ list] i↦y ∈ l, Φ (off+i) y) ∗ [∗ map] k↦y ∈ m, Φ k y.
  Proof.
    induction l0; simpl; intros.
    - iSplit.
      + iIntros "Hm"; iFrame.
      + iIntros "[Hemp Hm]". iFrame.
    - iSplit.
      + iIntros "Hm".
        rewrite insert_list_insert_commute_map; try lia.
        iDestruct (big_sepM_insert with "Hm") as "[Hoff Hm]".
        {
          rewrite lookup_list_insert_lt; try lia.
          apply H1. lia.
        }
        replace (off+0) with off by lia.
        iFrame.
        iDestruct (IHl0 with "Hm") as "Hm".
        {
          intros. apply H1. lia.
        }
        rewrite <- plus_n_Sm.
        rewrite <- plus_n_O.
        setoid_rewrite <- plus_n_Sm.
        simpl. iFrame.
      + iIntros "[[Hoff Hl] Hm]".
        replace (off+0) with (off) by lia.
        rewrite insert_list_insert_commute_map; try lia.
        iApply big_sepM_insert.
        {
          rewrite lookup_list_insert_lt; try lia.
          apply H1. lia.
        }
        iFrame.
        iApply IHl0.
        {
          intros. apply H1. lia.
        }
        iFrame.
        replace (off+1) with (S off) by lia. simpl.
        setoid_rewrite <- plus_n_Sm.
        iFrame.
  Qed.


  Local Ltac destruct_einner H :=
    let disklen := fresh "disklen" in
    let diskblocks := fresh "diskblocks" in
    let memblocks := fresh "memblocks" in
    let pending := fresh "pending" in
    let diskpending := fresh "diskpending" in
    let next_committed_id := fresh "next_committed_id" in
    let committed_pending := fresh "committed_pending" in
    let txid_map := fresh "txid_map" in
    let Hlen0 := fresh "Hlen0" in
    let Hlen1 := fresh "Hlen1" in
    let Hprefix := fresh "Hprefix" in
    let Hsuffix := fresh "Hsuffix" in
    let Hcid_pre := fresh "Hcid_pre" in
    let Hcid_mid := fresh "Hcid_mid" in
    let Hcid_post := fresh "Hcid_post" in
    let Hpendingprefix := fresh "Hpendingprefix" in
    iDestruct H as (disklen diskblocks memblocks pending diskpending next_committed_id committed_pending txid_map)
      ">(Hsource & Hlen0 & Hlen1 & Hmap & Hown & Hprefix & Hsuffix & Hpending & Howncommitid & Howncommitidexact & Hcid_pre & Hcid_mid & Hcid_post & Hcommitted_pending & Htxid_heap & Hownpending & Hpendingprefix)";
    iDestruct "Hmap" as "(Hptr&Hbs)";
    repeat unify_lease;
    repeat unify_ghost;
    iPure "Hlen0" as Hlen0;
    iPure "Hlen1" as Hlen1;
    iPure "Hprefix" as Hprefix;
    iPure "Hsuffix" as Hsuffix;
    iPure "Hcid_pre" as Hcid_pre;
    iPure "Hcid_mid" as Hcid_mid;
    iPure "Hcid_post" as Hcid_post;
    iPure "Hpendingprefix" as Hpendingprefix.

  Lemma write_blocks_ok bs p off len_val γcommit_id:
    (
      ( ExecInv γcommit_id ∗
        ⌜ off + length p <= log_size ⌝ ∗
        ⌜ length bs = log_size ⌝ ∗
        ⌜ off >= len_val ⌝ ∗
        lease log_commit len_val ∗
        [∗ list] pos↦b ∈ bs, lease (log_data pos) b )
      -∗
      WP write_blocks p off {{
        v,
        lease log_commit len_val ∗
        [∗ list] pos↦b ∈ (list_inserts bs off p), lease (log_data pos) b
      }}
    )%I.
  Proof.
    iIntros "((#Hsource_inv&Hinv)&Hinbound&Hbslen&Hoffpastlen&Hleaselen&Hlease)".
    iDestruct "Hinv" as (γblocks γpending γcommit_id_exact γdisklock) "(#Hdisklockinv&#Hinv)".
    iDestruct "Hinv" as (γmemlock) "(#Hmemlockinv&#Hinv)".
    iLöb as "IH" forall (p off bs).
    destruct p; simpl.
    - wp_ret.
      replace (off+0) with off by lia.
      iFrame.

    - wp_bind.

      iInv "Hinv" as "H".
      destruct_einner "H".

      iPure "Hinbound" as Hinbound.
      iPure "Hbslen" as Hbslen.
      iPure "Hoffpastlen" as Hoffpastlen.

      assert (off < length diskblocks) as Hoff by lia.
      apply lookup_lt_is_Some_2 in Hoff. destruct Hoff as [voff Hoff].
      iDestruct (big_sepL_insert_acc with "Hbs") as "[Hbsoff Hbsother]". apply Hoff.

      assert (off < length bs) as Hoffbs by lia.
      apply lookup_lt_is_Some_2 in Hoffbs. destruct Hoffbs as [boff Hoffbs].
      iDestruct (big_sepL_insert_acc with "Hlease") as "[Hleaseoff Hleaseother]". apply Hoffbs.

      wp_step.

      iModIntro.
      iExists _, (<[off:=n]> diskblocks), _, _, _, _, _, _.
      iSplitL "Hsource Hbsoff Hbsother Hptr Hown Hpending Howncommitid Howncommitidexact Hcommitted_pending Hownpending Htxid_heap".
      { iNext.
        iSplitL "Hsource".
        { rewrite take_insert; try lia.
          iFrame. lia. }
        iSplitR.
        { iPureIntro.
          rewrite insert_length. lia. }
        iSplitR.
        { iPureIntro.
          rewrite insert_length. lia. }
        iDestruct ("Hbsother" with "Hbsoff") as "Hbsother".
        iFrame.
        iSplit.
        { iPureIntro. rewrite take_insert; try lia. auto. }
        { iPureIntro. auto. }
      }

      iSpecialize ("IH" $! p (off + 1) (<[off:=n]> bs)).
      iApply (wp_wand with "[Hleaselen Hleaseother Hleaseoff] []").
      iApply ("IH" with "[%] [%] [%] [$Hleaselen]").

      { lia. }
      { erewrite insert_length. lia. }
      { lia. }
      { iApply "Hleaseother". iFrame. }

      iIntros "% H".
      iFrame.
  Qed.

  Lemma disk_lease_agree_log_data : forall l1 l2 off,
    length l1 = length l2 ->
    ( ( [∗ list] pos↦b ∈ l1, (off + pos) d↦ b ) -∗
      ( [∗ list] pos↦b ∈ l2, lease (off + pos) b ) -∗
      ⌜l1 = l2⌝ )%I.
  Proof.
    induction l1.
    - destruct l2; simpl; intros; try lia.
      iIntros.
      done.
    - destruct l2; simpl; intros; try lia.
      iIntros "[Hpts0 HptsS]".
      iIntros "[Hlease0 HleaseS]".

      iDestruct (disk_lease_agree with "Hpts0 Hlease0") as %Hagree. subst.

      inversion H1.
      specialize (IHl1 l2 (S off) H3).

      simpl in IHl1.
      setoid_rewrite plus_n_Sm in IHl1.

      iDestruct (IHl1 with "HptsS HleaseS") as %Hind. subst.
      done.
  Qed.

  Lemma write_mem_blocks_ok blocks p off γcommit_id:
    (
      ( ExecInv γcommit_id ∗
        ⌜ off + length p <= length blocks ⌝ ∗
        [∗ list] pos ↦ b ∈ blocks, mem_data pos m↦ b )
      -∗
      WP write_mem_blocks p off {{
        v,
        [∗ list] pos↦b ∈ (list_inserts blocks off p), mem_data pos m↦ b
      }}
    )%I.
  Proof.
    iIntros "((#Hsource_inv&Hinv)&Hlen&Hdata)".
    iDestruct "Hinv" as (γblocks γpending γcommit_id_exact γdisklock) "(#Hdisklockinv&#Hinv)".
    iDestruct "Hinv" as (γmemlock) "(#Hmemlockinv&#Hinv)".
    iLöb as "IH" forall (p off blocks).
    destruct p; simpl.
    - wp_ret. iFrame.
    - iPure "Hlen" as Hlen.

      assert (off < length blocks) as Hoff by lia.
      apply lookup_lt_is_Some_2 in Hoff. destruct Hoff as [voff Hoff].
      iDestruct (big_sepL_insert_acc with "Hdata") as "[Hdataoff Hdataother]". apply Hoff.
      wp_step.

      iSpecialize ("IH" $! p (off+1) (<[off:=n]> blocks)).
      iApply ("IH" with "").
      {
        iPureIntro.
        rewrite insert_length.
        lia.
      }
      iApply "Hdataother".
      iFrame.
  Qed.

  Lemma read_mem_blocks_ok nblocks off res blocks γcommit_id:
    (
      ( ExecInv γcommit_id ∗
        ⌜ off + nblocks <= length blocks ⌝ ∗
        [∗ list] pos↦b ∈ blocks, mem_data pos m↦ b )
      -∗
      WP read_mem_blocks nblocks off res {{
        v,
        ⌜ v = res ++ firstn nblocks (skipn off blocks) ⌝ ∗
        [∗ list] pos↦b ∈ blocks, mem_data pos m↦ b
      }}
    )%I.
  Proof.
    iIntros "((#Hsource_inv&Hinv)&Hlen&Hdata)".
    iDestruct "Hinv" as (γblocks γpending  γcommit_id_exact γdisklock) "(#Hdisklockinv&#Hinv)".
    iDestruct "Hinv" as (γmemlock) "(#Hmemlockinv&#Hinv)".
    iLöb as "IH" forall (nblocks off res).
    destruct nblocks; simpl.
    - wp_ret.
      rewrite firstn_O. rewrite app_nil_r. iFrame. iPureIntro. auto.
    - wp_bind.
      iPure "Hlen" as Hlen.

      assert (off < length blocks) as Hoffbs by lia.
      apply lookup_lt_is_Some_2 in Hoffbs. destruct Hoffbs as [boff Hoffbs].

      iDestruct (big_sepL_lookup_acc with "Hdata") as "[Hdataoff Hdataother]". apply Hoffbs.
      wp_step.
      iDestruct ("Hdataother" with "Hdataoff") as "Hdata".

      iSpecialize ("IH" $! nblocks (off+1) (res ++ [boff])).
      iApply (wp_wand with "[Hdata] []").
      {
        iApply ("IH" with "[%] [Hdata]").
        { lia. }
        iFrame.
      }

      iIntros "% [Hres Hdata]".
      iFrame.
      iPure "Hres" as Hres.
      iPureIntro.
      subst.

      apply take_drop_middle in Hoffbs.
      rewrite <- Hoffbs at 2.
      rewrite drop_app_alt. simpl.
      rewrite <- app_assoc. simpl.
      replace (off+1) with (S off) by lia.
      reflexivity.
      rewrite firstn_length_le.
      lia. lia.
  Qed.

  Lemma ghost_var_update_nat γ (n' n m : list nat) :
    own γ (● (Excl' n)) -∗ own γ (◯ (Excl' m)) ==∗
      own γ (● (Excl' n')) ∗ own γ (◯ (Excl' n')).
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (● Excl' n' ⋅ ◯ Excl' n') with "Hγ● Hγ◯") as "[$$]".
    { by apply auth_update, option_local_update, exclusive_local_update. }
    done.
  Qed.

  Lemma ghost_var_update_pending γ (n' n m : list pending_append) :
    own γ (● (Excl' n)) -∗ own γ (◯ (Excl' m)) ==∗
      own γ (● (Excl' n')) ∗ own γ (◯ (Excl' n')).
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (● Excl' n' ⋅ ◯ Excl' n') with "Hγ● Hγ◯") as "[$$]".
    { by apply auth_update, option_local_update, exclusive_local_update. }
    done.
  Qed.

  Lemma mem_append {T} j K `{LanguageCtx Log2.Op _ T Log2.l K} blocks γcommit_id:
    (
      ( j ⤇ K (Call (Log2.Append blocks)) ∗ Registered ∗ ExecInv γcommit_id )
      -∗
      WP mem_append blocks {{
        v,
        Registered ∗
        ( ( ⌜v = false⌝ ∗ j ⤇ K (Ret false) ) ∨
          ( ∃ txid, ⌜v = true⌝ ∗ txid s↦{1/2} (PendingDone j K) )
        )
      }}
    )%I.
  Proof.
    iIntros "(Hj&Hreg&(#Hsource_inv&Hinv))".
    iDestruct "Hinv" as (γblocks γpending γcommit_id_exact γdisklock) "(#Hdisklockinv&#Hinv)".
    iDestruct "Hinv" as (γmemlock) "(#Hmemlockinv&#Hinv)".

    wp_bind.
    wp_lock "(Hlocked&HML)".
    iDestruct "HML" as (memlen mblocks) "(Hmemmap & Hmemlen1 & Hmemlen2 & Hmemghost)".
    iPure "Hmemlen1" as Hmemlen1; iPure "Hmemlen2" as Hmemlen2.
    iDestruct "Hmemmap" as "[Hmemlen Hmemdata]".
    wp_step.
    destruct (gt_dec (memlen + length blocks) log_size).
    - (* First, step the spec to prove we can return false. *)
      wp_bind.
      iInv "Hinv" as "H".
      destruct_einner "H".

      iMod (ghost_step_lifting with "Hj Hsource_inv Hsource") as "(Hj&Hsource&_)".
      { intros. eexists. do 2 eexists; split; last by eauto. econstructor; eauto.
        econstructor.
        eexists.
        econstructor.
        econstructor.
        left.
        econstructor.
      }
      { solve_ndisj. }

      (* we already have the [iN] invariant opened up, and we want to
        unlock as well, which opens the [mN] invariant.  so we need to
        use the special version of [wp_unlock]. *)
      iDestruct (wp_unlock_open with "Hmemlockinv Hlocked") as "Hunlock".
      2: iApply (wp_wand with "[Hmemdata Hmemghost Hmemlen Hunlock]").
      2: iApply "Hunlock".
      solve_ndisj.
      iExists _, _. iFrame. done.

      iIntros.
      iModIntro; iExists _, _, _, _, _, _, _, _; iFrame.
      iSplit.
      { done. }

      wp_ret.
      iLeft.
      iFrame.
      done.

    - wp_bind.
      iApply (wp_wand with "[Hmemdata]").
      {
        iApply write_mem_blocks_ok.
        iFrame.
        iSplit.
        { iSplit. iApply "Hsource_inv".
          iExists _, _, _, _. iSplit. iApply "Hdisklockinv".
          iExists _. iSplit. iApply "Hmemlockinv". iApply "Hinv". }
        iPureIntro. lia.
      }

      iIntros (?) "Hmemdata".
      wp_step.
      wp_bind.

      iInv "Hinv" as "H".
      destruct_einner "H".

      iMod (ghost_var_update_nat γblocks (take (memlen + length blocks) (list_inserts mblocks memlen blocks)) with "Hmemghost Hown") as "[Hmemghost Hown]".
      iDestruct (wp_unlock_open with "Hmemlockinv Hlocked") as "Hunlock".

      2: iApply (wp_wand with "[Hmemdata Hmemghost Hmemlen Hunlock]").
      2: iApply "Hunlock".
      solve_ndisj.
      iExists _, _. iFrame.
      rewrite list_inserts_length. iPureIntro. lia.

      iIntros.

      iMod (gen_heap_alloc with "Htxid_heap") as "(Htxid_heap & Htxid_j & Hmeta_token)".
      {
        specialize (Hcid_post (next_committed_id + length pending)).
        apply Hcid_post.
        lia.
      }

      iModIntro.
      iExists _, _.
      iExists (take (memlen + strings.length blocks) (list_inserts mblocks memlen blocks)).
      iExists (pending ++ [Pending blocks j K]).
      iExists _.
      iExists _.
      iExists _.
      iExists _.

      iFrame.
      simpl.
      replace (length pending + 0) with (length pending) by lia.
      iDestruct (mapsto_split with "Htxid_j") as "[Htxid_j1 Htxid_j2]".
      iFrame.

      iSplitL "".
      { iPureIntro. intuition try lia.
        {
          rewrite <- Hprefix.
          admit.
        }
        {
          rewrite map_app. rewrite concat_app.
          rewrite <- Hsuffix.
          simpl. rewrite app_nil_r.
          admit.
        }

        {
          apply Hcid_pre; try lia.
          rewrite lookup_insert_ne in H3; try lia.
          auto.
        }
        {
          rewrite app_length in H2. simpl in H2.
          rewrite lookup_insert_ne; try lia.
          apply Hcid_post. lia.
        }

        admit.
      }

      wp_ret.
      iRight.
      iExists _.
      iFrame.
      done.
  Admitted.

  Lemma step_spec_pending : forall E, nclose sourceN ⊆ E ->
    forall pending (s : list nat),
    source_ctx -∗
    (
      ( [∗ list] p ∈ pending, pending_call p ) ∗
      source_state s ) ={E}=∗
    ( source_state (s ++ concat (map pending_blocks pending)) ∗
      ( [∗ list] p ∈ pending, pending_ret (pending_append_to_done p) ) ).
  Proof.
    intros E HE.
    induction pending.
    - simpl. iIntros (s) "#Hsource_inv (Hpending & Hsource)". rewrite app_nil_r. iFrame. done.
    - simpl. iIntros (s) "#Hsource_inv ([Hpending Hpendingother] & Hsource)".

      destruct a. simpl.

      iMod (ghost_step_lifting with "Hpending Hsource_inv Hsource") as "(Hj&Hsource&_)".
      { intros. eexists. do 2 eexists; split; last by eauto. econstructor; eauto.
        econstructor.
        eexists.
        econstructor.
        econstructor.
        right.
        econstructor.
        eexists.
        econstructor.
        econstructor.
        econstructor.
      }
      { solve_ndisj. }

      specialize (IHpending (s ++ blocks)).
      rewrite app_assoc.
      iFrame.
      iApply IHpending.
      iApply "Hsource_inv".
      iFrame.
  Qed.

  Lemma big_sepL_pending_append_to_done : forall off pending,
    ([∗ list] k↦x ∈ pending, pending_ret (pending_append_to_done x) ∗ (off + k) s↦{1 / 2} (pending_append_to_done x)) -∗
    ([∗ list] k↦x ∈ map pending_append_to_done pending, pending_ret x ∗ (off + k) s↦{1 / 2} x).
  Proof.
    intros.
    iIntros "H".
    iApply big_sepL_fmap.
    iApply (big_sepL_impl with "H").
    iModIntro. iIntros (k x) "%[Hp Hs]".
    iFrame.
  Qed.

  Lemma disk_append {T} γcommit_id txid j K `{LanguageCtx Log2.Op _ T Log2.l K}:
    (
      ( Registered ∗ ExecInv γcommit_id ∗ txid s↦{1/2} (PendingDone j K) )
      -∗
      WP disk_append {{
        tt,
        Registered ∗
        j ⤇ K (Ret true)
      }}
    )%I.
  Proof.
    iIntros "(Hreg&(#Hsource_inv&Hinv)&Hcaller_txid)".
    iDestruct "Hinv" as (γblocks γpending γcommit_id_exact γdisklock) "(#Hdisklockinv&#Hinv)".
    iDestruct "Hinv" as (γmemlock) "(#Hmemlockinv&#Hinv)".

    wp_bind.
    wp_lock "(Hlocked&HEL)".
    iDestruct "HEL" as (len_val bs diskpending next_committed_id_exact)
                         "((Hlen_ghost&Hbs_ghost)&Hbs_bounds&Hbs_len&Hdiskpendingown&Hnext_committed_exact)".
    iPure "Hbs_bounds" as Hbs_bounds.
    iPure "Hbs_len" as Hbs_len.

    wp_bind.
    iInv "Hinv" as "H".
    destruct_einner "H".
    iDestruct (disk_lease_agree_log_data with "Hbs Hbs_ghost") as %Hagree. lia. subst.

    wp_step.
    iModIntro; iExists _, _, _, _, _, _, _, _; iFrame.

    iSplitR. iPureIntro. intuition lia.

    wp_bind.
    wp_lock "(Hmlocked&HML)".
    iDestruct "HML" as (memlen mblocks) "(Hmemmap & Hmemlen1 & Hmemlen2 & Hmemghost)".
    iPure "Hmemlen1" as Hmemlen1; iPure "Hmemlen2" as Hmemlen2.
    iDestruct "Hmemmap" as "[Hmemlen Hmemdata]".

    (* snapshot the pending from memory *)
    wp_bind.
    iInv "Hinv" as "H".
    destruct_einner "H".
    iDestruct (disk_lease_agree_log_data with "Hbs Hbs_ghost") as %Hagree. lia. subst.

    wp_step.

    destruct (lt_dec txid (next_committed_id0 + length pending0)).
    2: {
      iDestruct (gen_heap_valid with "Htxid_heap Hcaller_txid") as %Hcaller_some.
      exfalso.
      rewrite Hcid_post0 in Hcaller_some. congruence.
      lia.
    }

    iMod (ghost_var_update_pending γpending pending0 with "Hdiskpendingown Hownpending") as "[Hdiskpendingown Hownpending]".
    clear Hpendingprefix0. clear Hpendingprefix. clear diskpending.
    iModIntro; iExists _, _, _, _, _, _, _, _; iFrame.
    iSplitR. iPureIntro. intuition try lia.
      rewrite firstn_all. auto.

    wp_bind.
    iApply (wp_wand with "[Hmemdata]").
    iApply read_mem_blocks_ok.
    iFrame. iSplit.
    {
      iSplit. iApply "Hsource_inv".
      iExists _, _, _, _. iSplit. iApply "Hdisklockinv".
      iExists _. iSplit. iApply "Hmemlockinv". iApply "Hinv". }
    iPureIntro. lia.

    iIntros (?) "[Hlen Hmemdata]".
    iPure "Hlen" as Hlen. subst. simpl.

    wp_unlock "[Hmemlen Hmemdata Hmemghost]".
    {
      iExists _, _.
      iFrame.
      iPureIntro. lia.
    }

    wp_bind.
    iApply (wp_wand with "[Hlen_ghost Hbs_ghost]").
    {
      iApply write_blocks_ok.
      iFrame.
      iSplitL.
      - iSplit. iApply "Hsource_inv".
        iExists _, _, _, _. iSplit. iApply "Hdisklockinv".
        iExists _. iSplit. iApply "Hmemlockinv". iApply "Hinv".
      - iPureIntro. intuition.
        rewrite firstn_length.
        lia.
    }

    iIntros "% [Hleaselen Hleaseblocks]".
    wp_bind.

    iInv "Hinv" as "H".
    destruct_einner "H".

    iDestruct (disk_lease_agree_log_data with "Hbs Hleaseblocks") as %Hagree.
    rewrite list_inserts_length. lia. subst.

    iDestruct (step_spec_pending _ _ diskpending with "Hsource_inv") as "Hspec".

    rewrite <- (firstn_skipn (length diskpending) pending1) at 1.
    rewrite Hpendingprefix.
    iDestruct (big_sepL_app with "Hpending") as "[Hpending0 Hpending1]".
    iDestruct (big_sepL_sep with "Hpending0") as "[Hpending0a Hpending0b]".
    iMod ("Hspec" with "[Hpending0a Hsource]") as "[Hsource Hdone]". iFrame.

    wp_step.

    iMod (ghost_var_update_pending γpending nil with "Hdiskpendingown Hownpending") as "[Hdiskpendingown Hownpending]".
    iMod (own_update with "Howncommitid") as "Howncommitid".
    {
      eapply auth_update_auth.
      eapply mnat_local_update.
      assert (next_committed_id <= next_committed_id + length diskpending) as Hle by lia.
      apply Hle.
    }
    iMod (ghost_var_update _ (next_committed_id + length diskpending) with "Hnext_committed_exact Howncommitidexact") as "[Hnext_committed_exact Howncommitidexact]".

    iModIntro.
    iExists memlen.
    iExists (list_inserts bs len_val (take (memlen - len_val) (drop len_val mblocks))).
    iExists memblocks0.
    iExists _.
    iExists _.
    iExists _.
    iExists (delete txid (list_inserts committed_pending1 next_committed_id (map pending_append_to_done diskpending))).
    iExists _.

    iDestruct (big_sepL_sep with "[Hpending0b Hdone]") as "Hdone".
    { iFrame. }
    simpl.

    iDestruct (big_sepL_pending_append_to_done with "Hdone") as "Hdone".

    iDestruct (big_sepM_list_inserts with "[Hcommitted_pending Hdone]") as "Hcommitted_pending".
    2: {
      iFrame. iFrame.
    }
    { auto. }

    iDestruct (gen_heap_valid with "Htxid_heap Hcaller_txid") as %Hcaller_some.
    assert (is_Some (list_inserts committed_pending1 next_committed_id (map pending_append_to_done diskpending) !! txid)) as Hretsome.
    {
      destruct (lt_dec txid next_committed_id).
      {
        rewrite lookup_list_insert_lt; [|lia].
        apply Hcid_pre1; try lia.
        eexists. apply Hcaller_some.
      }
      {
        replace (txid) with (next_committed_id + (txid-next_committed_id)) by lia.
        rewrite lookup_list_insert_plus.
        apply lookup_lt_is_Some_2. rewrite map_length. lia. rewrite map_length. lia.
      }
    }

    destruct Hretsome as [pd Hretsome].
    destruct pd; simpl in *.
    iDestruct (big_sepM_delete _ _ txid with "Hcommitted_pending") as "[[Hret Hretj] Hcommitted_pending]".
    eassumption.

    iDestruct (gen_heap_valid with "Htxid_heap Hretj") as %Hretj.
    simpl in *.
    rewrite Hcaller_some in Hretj. inversion Hretj. subst. simpl_existT. subst.

    setoid_rewrite plus_assoc.

    iFrame.
    iSplitR "Hleaseblocks Hleaselen Hlocked Hdiskpendingown Hnext_committed_exact".
    2: {
      wp_bind.
      wp_unlock "[Hleaseblocks Hleaselen Hdiskpendingown Hnext_committed_exact]".
      {
        iExists _, _, _, _. iFrame. iPureIntro. lia.
      }
      wp_ret.
      done.
    }

    iSplitL "Hsource".
    {
      iNext.
      rewrite take_list_inserts_le; try lia.
      admit.
    }

    iPureIntro. intuition try lia.
    - admit.
    - admit.
    - destruct (lt_dec txid0 next_committed_id).
      + (* XXX we need gen_heap_delete to drop txid from the heap... *)
        admit. (* rewrite lookup_list_insert_lt; try lia. auto. *)
      + admit.
    - admit.
    - apply Hcid_post1.
      admit.

  Unshelve.
    solve_ndisj.
  Admitted.

  Lemma append_refinement {T} j K `{LanguageCtx Log2.Op _ T Log2.l K} p γcommit_id:
    {{{ j ⤇ K (Call (Log2.Append p)) ∗ Registered ∗ ExecInv γcommit_id }}}
      append p
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Hreg&#Hinv) HΦ".

    wp_bind.
    iApply (wp_wand with "[Hj Hreg]").
    {
      iApply mem_append. iFrame. iApply "Hinv".
    }

    iIntros "% [Hreg H]".
    destruct a.

    - wp_bind.
      iDestruct "H" as "[[%H]|H]". congruence.
      iDestruct "H" as (?) "[%H]".

      iApply (wp_wand with "[H Hreg]").
      {
        iApply disk_append. iFrame. iApply "Hinv".
      }

      iIntros "% [Hreg H]".
      wp_ret.
      (* XXX why does iApply not work?  the triangle? *)
      (*
      iApply "HΦ".
      *)
      admit.

    - wp_ret.
      iDestruct "H" as "[[%H]|H]".
      + admit.
      + iDestruct "H" as (txid) "[%H]". congruence.
  Admitted.

  Lemma read_blocks_ok nblocks off res bs:
    (
      ( ExecInv ∗
        ⌜ off + nblocks <= length bs /\ length bs = log_size ⌝ ∗
        [∗ list] pos↦b ∈ bs, lease (log_data pos) b )
      -∗
      WP read_blocks nblocks off res {{
        v,
        ⌜ v = res ++ firstn nblocks (skipn off bs) ⌝ ∗
        [∗ list] pos↦b ∈ bs, lease (log_data pos) b
      }}
    )%I.
  Proof.
    iIntros "((#Hsource_inv&Hinv)&Hinbound&Hlease)".
    iDestruct "Hinv" as (γlock) "(#Hlockinv&#Hinv)".
    iLöb as "IH" forall (nblocks off res).
    destruct nblocks; simpl.
    - wp_ret.
      rewrite firstn_O. rewrite app_nil_r. iFrame. iPureIntro. auto.
    - wp_bind.

      iInv "Hinv" as "H".
      destruct_einner "H".

      iPure "Hinbound" as ?; intuition.
      iPure "Hlen" as ?; intuition.
      iDestruct (disk_lease_agree_log_data with "Hbs Hlease") as %Hx; subst. lia.

      assert (off < length bs) as Hoffbs by lia.
      apply lookup_lt_is_Some_2 in Hoffbs. destruct Hoffbs as [boff Hoffbs].

      iDestruct (big_sepL_lookup_acc with "Hbs") as "[Hbsoff Hbsother]". apply Hoffbs.
      iDestruct (big_sepL_lookup_acc with "Hlease") as "[Hleaseoff Hleaseother]". apply Hoffbs.
      wp_step.

      iModIntro.
      iExists _, _.
      iFrame.
      iSplitL "Hbsoff Hbsother".
      {
        iSplit.
        {
          iNext. iPureIntro. intuition.
        }

        iApply "Hbsother".
        iFrame.
      }

      iSpecialize ("IH" $! nblocks (off+1) (res ++ [boff])).
      iApply (wp_wand with "[Hleaseoff Hleaseother] []").
      {
        iApply ("IH" with "[%] [Hleaseoff Hleaseother]").
        { lia. }
        iApply "Hleaseother". iFrame.
      }

      iIntros "% [Hres Hlease]".
      iFrame.
      iPure "Hres" as Hres.
      iPureIntro.
      subst.

      apply take_drop_middle in Hoffbs.
      rewrite <- Hoffbs at 2.
      rewrite drop_app_alt. simpl.
      rewrite <- app_assoc. simpl.
      replace (off+1) with (S off) by lia.
      reflexivity.
      rewrite firstn_length_le.
      lia. lia.
  Qed.

  Lemma read_refinement {T} j K `{LanguageCtx Log2.Op (list nat) T Log2.l K}:
    {{{ j ⤇ K (Call (Log2.Read)) ∗ Registered ∗ ExecInv }}}
      read
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Hreg&#Hsource_inv&Hinv) HΦ".
    iDestruct "Hinv" as (γlock) "(#Hlockinv&#Hinv)".

    wp_lock "(Hlocked&HEL)".
    iDestruct "HEL" as (len_val bs)
                         "((Hlen_ghost&Hbs_ghost)&Hlenbound)".
    iPure "Hlenbound" as Hlenbound.

    wp_bind.
    iInv "Hinv" as "H".
    destruct_einner "H".
    wp_step.

    iPure "Hlen" as Hlen. intuition.
    iDestruct (disk_lease_agree_log_data with "Hbs Hbs_ghost") as %Hx; subst. lia.

    iMod (ghost_step_lifting with "Hj Hsource_inv Hsource") as "(Hj&Hsource&_)".
    { simpl.
      intros. eexists. do 2 eexists; split; last by eauto. econstructor; eauto.
      econstructor.
    }
    { solve_ndisj. }
    iModIntro; iExists _, _; iFrame.

    iSplit.
    {
      iNext. iPureIntro. lia.
    }

    wp_bind.
    iApply (wp_wand with "[Hbs_ghost]").
    {
      iApply read_blocks_ok.
      iFrame.
      iSplit.
      - unfold ExecInv. iSplitL. iApply "Hsource_inv". iExists _. iSplitL. iApply "Hlockinv". iApply "Hinv".
        (* XXX how to automate that? *)
      - iPureIntro. intuition.
    }

    iIntros "% [Hres Hleaseblocks]".
    iPure "Hres" as Hres. subst. simpl.
    rewrite drop_0.

    wp_bind.
    wp_unlock "[-HΦ Hreg Hj]"; iFrame.
    {
      iExists _, _.
      iFrame.
      iPureIntro. lia.
    }

    wp_ret.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma init_mem_split:
    (([∗ map] i↦v ∈ init_zero, i m↦ v) -∗ log_lock m↦ 0)%I.
  Proof.
    iIntros "Hmem".
    rewrite (big_opM_delete _ _ 0 0); last first.
    { rewrite /ExMach.mem_state. apply init_zero_lookup_lt_zero. rewrite /size. lia. }
    iDestruct "Hmem" as "(?&_)".
    iFrame.
  Qed.

  Lemma rep_delete_init_zero:
    forall off (P : nat -> nat -> iPropI Σ),
      off < size ->
      ([∗ map] k↦x ∈ rep_delete off init_zero, P k x) -∗
        P off 0 ∗ [∗ map] k↦x ∈ rep_delete (S off) init_zero, P k x.
  Proof.
    intros.
    simpl rep_delete.
    iIntros "H".
    iDestruct (big_sepM_delete with "H") as "H".
    2: iFrame.
    rewrite rep_delete_lookup; try lia.
    apply init_zero_lookup_lt_zero.
    lia.
  Qed.

  Lemma rep_delete_init_zero_list:
    forall (P : nat -> nat -> iPropI Σ) n off,
      (n + off) <= size ->
      ([∗ map] k↦x ∈ rep_delete off init_zero, P k x) -∗
        ([∗ list] pos↦b ∈ repeat 0 n, P (off+pos) b) ∗
        [∗ map] k↦x ∈ rep_delete (n + off) init_zero, P k x.
  Proof.
    induction n.
    - simpl. iIntros. iFrame.
    - simpl. iIntros (off Hoff) "H".
      iDestruct (rep_delete_init_zero with "H") as "[Hoff Hmore]". lia.
      replace (off+0) with off by lia. iFrame.
      iDestruct (IHn with "Hmore") as "[Hl Htail]". lia.
      rewrite <- plus_n_Sm. simpl. iFrame.
      setoid_rewrite <- plus_n_Sm. iFrame.
  Qed.

  Lemma init_disk_split:
    (([∗ map] i↦v ∈ init_zero, i d↦ v ∗ lease i v)
       -∗ (log_commit d↦ 0
          ∗ [∗ list] pos ↦ b ∈ (repeat 0 log_size), log_data pos d↦ b)
          ∗ lease log_commit 0
          ∗ [∗ list] pos ↦ b ∈ (repeat 0 log_size), lease (log_data pos) b).
  Proof.
    iIntros "Hdisk".
    iPoseProof (disk_ptr_iter_split_aux 0 0 with "Hdisk") as "H".
    { rewrite /size. lia. }
    iDestruct "H" as "(Hcommit&Hdata)".
    repeat iDestruct "Hcommit" as "((?&?)&H)". iFrame.
    iDestruct (big_sepM_sep with "Hdata") as "(Hpts&Hlease)".
    pose proof log_size_ok.
    iDestruct (rep_delete_init_zero_list with "Hpts") as "[Hpts Hpts']".
    2: iFrame. lia.
    iDestruct (rep_delete_init_zero_list with "Hlease") as "[Hlease Hlease']".
    2: iFrame. lia.
  Qed.

End refinement_triples.



Module sRT <: exmach_refinement_type.

  Definition helperΣ : gFunctors := #[GFunctor (authR (optionUR (exclR (natO))));
                                      GFunctor (authR (optionUR (exclR (listO natO))))].
  Instance subG_helperΣ : subG helperΣ Σ → inG Σ (authR (optionUR (exclR (natO)))).
  Proof. solve_inG. Qed.
  Instance subG_helperΣ' : subG helperΣ Σ → inG Σ (authR (optionUR (exclR (listO natO)))).
  Proof. solve_inG. Qed.

  Definition Σ : gFunctors := #[Adequacy.exmachΣ; @cfgΣ Log2.Op Log2.l; lockΣ; helperΣ].

  Definition init_absr σ1a σ1c :=
    ExMach.l.(initP) σ1c ∧ Log2.l.(initP) σ1a.

  Definition OpT := Log2.Op.
  Definition Λa := Log2.l.

  Definition impl := ImplLog2.impl.
  Existing Instance subG_cfgPreG.

  Instance CFG : @cfgPreG Log2.Op Log2.l Σ. apply _. Qed.
  Instance HEX : ExMach.Adequacy.exmachPreG Σ. apply _. Qed.
  Instance INV : Adequacy.invPreG Σ. apply _. Qed.
  Instance REG : inG Σ (csumR countingR (authR (optionUR (exclR unitO)))). apply _. Qed.

  Global Instance inG_inst1: inG Σ (authR (optionUR (exclR (listO natO)))).
  Proof. apply _. Qed.

  Global Instance inG_inst2: inG Σ (authR (optionUR (exclR natO))).
  Proof. apply _. Qed.

  Global Instance inG_inst3: lockG Σ.
  Proof. apply _. Qed.

  Definition exec_inv := fun H1 H2 => (@ExecInv Σ H2 _ H1)%I.
  Definition exec_inner :=
    fun H1 H2 => (∃ v, log_lock m↦ v ∗
          ((⌜ v = 0  ⌝ -∗ @ExecLockInv Σ H2) ∗ @ExecInner Σ H2 H1))%I.

  Definition crash_param := fun (_ : @cfgG OpT Λa Σ) (_ : exmachG Σ) => unit.
  Definition crash_inv := fun H1 H2 (_ : crash_param _ _) => @CrashInv Σ H2 H1.
  Definition crash_starter :=
    fun H1 H2 (_ : crash_param H1 H2) => (True%I : iProp Σ).
  Definition crash_inner := fun H1 H2 => (@CrashInner Σ H2 H1)%I.
  Definition E := nclose sourceN.

  Definition recv: proc ExMach.Op unit := Ret tt.

End sRT.

Module sRD := exmach_refinement_definitions sRT.

Module sRO : exmach_refinement_obligations sRT.

  Module eRD := exmach_refinement_definitions sRT.
  Import sRT.
  Import sRD.

  Lemma einv_persist: forall {H1 : @cfgG OpT Λa Σ} {H2 : _},
      Persistent (exec_inv H1 H2).
  Proof. apply _. Qed.

  Lemma cinv_persist: forall {H1 : @cfgG OpT Λa Σ} {H2 : _} P,
      Persistent (crash_inv H1 H2 P).
  Proof. apply _. Qed.

  Lemma nameIncl: nclose sourceN ⊆ E.
  Proof. solve_ndisj. Qed.

  Lemma recsingle: recover impl = rec_singleton recv.
  Proof. trivial. Qed.

  Lemma refinement_op_triples: refinement_op_triples_type.
  Proof.
    red. intros. iIntros "(?&?&HDB)". destruct op.
    - iApply (append_refinement with "[$]"). iNext. iIntros (?) "H". iFrame.
    - iApply (read_refinement with "[$]"). iNext. iIntros (?) "H". iFrame.
  Qed.

  Lemma exec_inv_source_ctx: ∀ {H1 H2}, exec_inv H1 H2 ⊢ source_ctx.
  Proof. iIntros (??) "(?&?)"; eauto. Qed.

  Lemma list_next {H: exmachG Σ} Hinv Hmem Hreg : forall bs off,
    ([∗ list] pos↦b ∈ bs, (off + pos) d↦ b) ==∗
      let Hex := ExMachG Σ Hinv Hmem (next_leased_heapG (hG := (exm_disk_inG))) Hreg in
      (([∗ list] pos↦b ∈ bs, (off + pos) d↦ b) ∗ ([∗ list] pos↦b ∈ bs, lease (off + pos) b)).
  Proof.
    simpl.
    induction bs.
    - simpl. iIntros. done.
    - simpl. iIntros (off) "(Hthis&Hnext)".
      iMod (disk_next with "[$]") as "($&$)".
      setoid_rewrite <- plus_n_Sm.
      setoid_rewrite <- plus_Sn_m.
      specialize (IHbs (S off)).
      iDestruct (IHbs with "Hnext") as "Hnext".
      iFrame.
  Qed.

  Lemma ptr_map_next {H: exmachG Σ} Hinv Hmem Hreg len_val bs:
    ptr_map len_val bs ==∗
            let Hex := ExMachG Σ Hinv Hmem (next_leased_heapG (hG := (exm_disk_inG))) Hreg in
            ptr_map len_val bs ∗ lease_map len_val bs.
  Proof.
    iIntros "(Hlen&Hbs)".
    iMod (disk_next with "[$]") as "($&$)".
    iDestruct (list_next with "Hbs") as "Hbs".
    iFrame.
  Qed.

  Lemma recv_triple: recv_triple_type.
  Proof.
    red. intros. iIntros "((#Hctx&#Hinv)&_)".
    wp_ret. iInv "Hinv" as (len_val bs) ">(?&Hlen&Hcase&Hlease&?)" "_".
    iApply (fupd_mask_weaken _ _).
    { solve_ndisj. }
    iExists (firstn len_val bs). iFrame.
    iExists (firstn len_val bs).
    iSplitL "".
    { iPureIntro; econstructor. }
    iClear "Hctx Hinv".
    iIntros (???) "(#Hctx&Hstate)".
    iMod (ptr_map_next with "Hcase") as "(Hp&Hl)".
    iExists 0. iFrame.
    iPure "Hlen" as Hlen; intuition.
    iSplitL "Hl"; iModIntro; iIntros; iExists _, _; iFrame.
    iPureIntro; intuition.
    iPureIntro; intuition.
  Qed.

  Lemma init_wf: ∀ σ1a σ1c, init_absr σ1a σ1c → ExMach.state_wf σ1c.
  Proof.
    intros ?? (H&?). inversion H. subst. eapply ExMach.init_state_wf.
  Qed.

  Lemma init_exec_inner : init_exec_inner_type.
  Proof.
    red. intros ?? (H&Hinit) ??. inversion H. inversion Hinit. subst.
    iIntros "(Hmem&Hdisk&#?&Hstate)".
    iPoseProof (init_mem_split with "Hmem") as "?".
    iPoseProof (init_disk_split with "Hdisk") as "(Hd&Hl)".
    iModIntro. iExists _. iFrame.
    iSplitL "Hl".
    - iDestruct "Hl" as "(?&?)". iIntros "_". iExists 0, _. iFrame.
      iPureIntro. intuition. lia. rewrite repeat_length. lia.
    - iDestruct "Hd" as "(?&?)". iExists 0, _. iFrame.
      iPureIntro. intuition. lia. rewrite repeat_length. lia.
  Qed.

  Lemma exec_inv_preserve_crash: exec_inv_preserve_crash_type.
  Proof.
    red. intros. iIntros "(#Hctx&#Hinv)".
    iDestruct "Hinv" as (γlock) "(#Hlock&#Hinv)".
    iInv "Hinv" as "Hopen" "_".
    destruct_einner "Hopen".
    iApply fupd_mask_weaken; first by solve_ndisj.
    iIntros (??) "Hmem".
    iPoseProof (@init_mem_split with "Hmem") as "?".
    iMod (ptr_map_next with "[Hptr Hbs]") as "(?&?)"; first by iFrame.
    iModIntro. iExists _, _. iFrame.
  Qed.

  Lemma crash_inv_preserve_crash: crash_inv_preserve_crash_type.
  Proof.
    red. intros. iIntros "(#Hctx&#Hinv)".
    iInv "Hinv" as ">Hopen" "_".
    iDestruct "Hopen" as (? ?) "(?&Hlen&Hptr&Hlease&Hlock)".
    iApply fupd_mask_weaken; first by solve_ndisj.
    iIntros (??) "Hmem".
    iMod (ptr_map_next with "Hptr") as "(?&?)".
    iModIntro. iExists _, _. iFrame.
    iPoseProof (@init_mem_split with "Hmem") as "?".
    iFrame.
  Qed.

  Lemma crash_inner_inv : crash_inner_inv_type.
  Proof.
    red. intros. iIntros "(Hinv&#Hsrc)".
    iDestruct "Hinv" as (invG) "Hinv".
    iDestruct "Hinv" as (??) "(?&?&?)".
    iMod (@inv_alloc Σ (exm_invG) iN _ CrashInner with "[-]").
    { iNext. iExists _, _; iFrame. }
    iModIntro. iFrame. iExists tt. iFrame "Hsrc".
  Qed.

  Lemma exec_inner_inv : exec_inner_inv_type.
  Proof.
    red. intros. iIntros "(Hinv&#Hsrc)".
    iDestruct "Hinv" as (invG v) "Hinv".
    iDestruct "Hinv" as "(?&Hinv)".
    iDestruct "Hinv" as "(Hlock&Hinner)".
    iMod (@lock_init Σ (ExMachG _ (exm_invG) (exm_mem_inG) (exm_disk_inG) _) _ lN
                     log_lock _ (ExecLockInv) with "[$] [-Hinner]") as (γlock) "H".
    { iFrame. }
    iMod (@inv_alloc Σ (exm_invG) iN _ (ExecInner) with "[Hinner]").
    { iFrame. }
    iModIntro. iFrame "Hsrc". iExists _. iFrame.
  Qed.

  Lemma exec_inv_preserve_finish : exec_inv_preserve_finish_type.
  Proof.
    iIntros (??) "? (?&H)".
    iDestruct "H" as (?) "(Hlock&Hinv)".
    iInv "Hinv" as "H" "_".
    iDestruct "H" as (ptr bs) ">(Hsource&Hlen&Hmap)".
    iMod (lock_crack with "Hlock") as ">H"; first by solve_ndisj.
    iDestruct "H" as (v) "(?&?)".
    iApply fupd_mask_weaken; first by solve_ndisj.
    iExists _, _; iFrame.
    iSplitL "".
    { iPureIntro. econstructor. }
    iIntros (????) "(?&?&Hmem)".
    iMod (ptr_map_next with "Hmap") as "(Hp&Hl)".
    iPoseProof (@init_mem_split with "Hmem") as "?".
    iExists _. iFrame. rewrite /ExecLockInv.
    iPure "Hlen" as Hlen. intuition.
    iSplitL "Hl"; iModIntro; iIntros; iExists _, _; iFrame.
    iPureIntro; intuition.
    iPureIntro; intuition.
  Qed.

End sRO.

Module sR := exmach_refinement sRT sRO.
Import sR.

Lemma exmach_crash_refinement_seq {T} σ1c σ1a (es: proc_seq Log2.Op T) :
  sRT.init_absr σ1a σ1c →
  wf_client_seq es →
  ¬ proc_exec_seq Log2.l es (rec_singleton (Ret ())) (1, σ1a) Err →
  ∀ σ2c res, proc_exec_seq ExMach.l (compile_proc_seq ImplLog2.impl es)
                                      (rec_singleton recv) (1, σ1c) (Val σ2c res) →
  ∃ σ2a, proc_exec_seq Log2.l es (rec_singleton (Ret tt)) (1, σ1a) (Val σ2a res).
Proof. apply sR.R.crash_refinement_seq. Qed.
