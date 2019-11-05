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

Lemma mapsto_unify (i : L) (q : Qp) (v v' : V):
  mapsto i (q/2) v -∗ mapsto i (q/2) v' -∗ mapsto i q v.
Proof.
  iIntros "H1 H2".
  iDestruct (mapsto_agree with "H1 H2") as %[= <-].
  iFrame.
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

Lemma lookup_list_insert_oob
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
      x >= off + length p ->
      list_inserts m off p !! x = m !! x.
Proof.
  induction p; simpl; intros; auto.
  rewrite insert_list_insert_commute_map; try lia.
  rewrite lookup_insert_ne; try lia.
  rewrite IHp; auto. lia.
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

Lemma take_take_le {T}:  forall  (diskblocks: list T) disklen memlen memblocks,
  disklen <= strings.length diskblocks ->
  memlen <= strings.length memblocks ->
  take disklen (take memlen memblocks) = take disklen diskblocks ->
  disklen <= memlen.
Proof.
  intros.
  destruct(dec_le disklen memlen); try lia.
  rewrite firstn_firstn in H1.
  rewrite min_r in H1; try lia.
  assert(length (take memlen memblocks) = memlen).
  rewrite(firstn_length_le); try lia.
  assert(length (take disklen diskblocks) = disklen).
  rewrite(firstn_length_le); try lia.
  rewrite H1 in H3.
  exfalso. lia.
Qed.

Lemma rep_delete_init_zero:
  forall Σ off (P : nat -> nat -> iPropI Σ),
    off < ExMach.size ->
    ([∗ map] k↦x ∈ rep_delete off ExMach.init_zero, P k x) -∗
      P off 0 ∗ [∗ map] k↦x ∈ rep_delete (S off) ExMach.init_zero, P k x.
Proof.
  intros.
  simpl rep_delete.
  iIntros "H".
  iDestruct (big_sepM_delete with "H") as "H".
  2: iFrame.
  rewrite rep_delete_lookup; try lia.
  apply ExMach.init_zero_lookup_lt_zero.
  lia.
Qed.

Lemma rep_delete_init_zero_list:
  forall Σ (P : nat -> nat -> iPropI Σ) n off,
    (n + off) <= ExMach.size ->
    ([∗ map] k↦x ∈ rep_delete off ExMach.init_zero, P k x) -∗
      ([∗ list] pos↦b ∈ repeat 0 n, P (off+pos) b) ∗
      [∗ map] k↦x ∈ rep_delete (n + off) ExMach.init_zero, P k x.
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

Local Ltac destruct_einner H :=
  let disklen := fresh "disklen" in
  let diskblocks := fresh "diskblocks" in
  let memblocks := fresh "memblocks" in
  let pending := fresh "pending" in
  let diskpending := fresh "diskpending" in
  let next_committed_id := fresh "next_committed_id" in
  let log_txns_val := fresh "log_txns_val" in
  let Hlen0 := fresh "Hlen0" in
  let Hlen1 := fresh "Hlen1" in
  let Hprefix := fresh "Hprefix" in
  let Hsuffix := fresh "Hsuffix" in
  let Hpendingprefix := fresh "Hpendingprefix" in
  let Hlog_txns_le := fresh "Hlog_txns_le" in
  let Hmem_txns_eq := fresh "Hmem_txns_eq" in
  iDestruct H as (disklen diskblocks memblocks pending
                  diskpending next_committed_id log_txns_val mem_txns_val)
    ">(Hsource & Hlen0 & Hlen1 & Hmap & Hown & Hprefix & Hsuffix & Howncommitidexact & Htxid_map_status & Hlog_txns_le & Hmem_txns_eq & Hmem_txns_part & Hlog_txns & Hownpending & Hpendingprefix)";
  iDestruct "Hmap" as "(Hptr&Hbs)";
  repeat unify_lease;
  repeat unify_ghost;
  iPure "Hlen0" as Hlen0;
  iPure "Hlen1" as Hlen1;
  iPure "Hprefix" as Hprefix;
  iPure "Hsuffix" as Hsuffix;
  iPure "Hpendingprefix" as Hpendingprefix;
  iPure "Hlog_txns_le" as Hlog_txns_le;
  iPure "Hmem_txns_eq" as Hmem_txns_eq.


Section refinement_triples.
  Context `{!exmachG Σ, lockG Σ, !@cfgG (Log2.Op) (Log2.l) Σ,
            !inG Σ (authR (optionUR (exclR (listO natO)))),
            !inG Σ (authR (optionUR (exclR (listO pending_appendC)))),
            !inG Σ (authR (optionUR (exclR natO)))}.

  (* hDone maps transaction IDs to the thread ID and its K value that's waiting for completion.
   * Being absent from the heap means the transaction ID never existed.
   * Being present as [Some pd] means there's a completion but the thread
   * hasn't used the completion yet (e.g., because it hasn't yet returned).
   * Being present as [None] means the completion was reclaimed already. *)
  Context {hDone: gen_heapG nat (option pending_done) Σ}.
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


  Definition is_SomeSome {T} (x : option (option T)) :=
    exists y, x = Some (Some y).

  Definition txid_status (txid : nat) (pd : pending_done) :=
    (
      pending_ret pd
    )%I.

  Definition txid_map_status (next_committed_id : nat) (pending : list pending_append) :=
    (
      ∃ (committed_pending : gmap nat pending_done)
        (txid_map : gmap nat (option pending_done)),
        ⌜ ∀ txid pd, txid < next_committed_id -> txid_map !! txid = Some (Some pd) -> committed_pending !! txid = Some pd ⌝ ∗
        ⌜ ∀ txid, txid >= next_committed_id -> committed_pending !! txid = None ⌝ ∗
        ⌜ ∀ txid, txid >= next_committed_id + length pending -> txid_map !! txid = None ⌝ ∗
        ⌜ ∀ off p, pending !! off = Some p ->
          txid_map !! (next_committed_id + off)%nat = Some (Some (pending_append_to_done p)) ⌝ ∗
        ( [∗ map] txid ↦ done ∈ committed_pending, txid_status txid done ) ∗
        ( [∗ list] pending_off ↦ p ∈ pending, pending_call p ) ∗
        gen_heap_ctx txid_map
    )%I.

  Definition ExecInner γmemblocks γdiskpending γcommit_id_exact γmem_txn_next :=
    (∃ (len_val : nat) (bs : list nat) (memblocks : list nat)
       (pending : list pending_append) (diskpending : list pending_append)
       (next_committed_id : nat) (log_txns_val : nat) (mem_txns_val : nat),

        source_state (firstn len_val bs) ∗
        ⌜ len_val <= length bs ⌝ ∗
        ⌜ length bs = log_size ⌝ ∗
        ptr_map len_val bs ∗
        own γmemblocks (◯ (Excl' memblocks)) ∗
        ⌜ firstn len_val memblocks = firstn len_val bs ⌝ ∗
        ⌜ skipn len_val memblocks = concat (map pending_blocks pending) ⌝ ∗

        own γcommit_id_exact (◯ (Excl' next_committed_id)) ∗
        txid_map_status next_committed_id pending ∗

        ⌜ log_txns_val <= next_committed_id ⌝ ∗
        ⌜ mem_txns_val = (next_committed_id + length pending)%nat ⌝ ∗
        own γmem_txn_next (◯ (Excl' mem_txns_val)) ∗
        log_txn_next m↦ log_txns_val ∗

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

  Definition MemLockInv γmemblocks γmem_txn_next :=
    (∃ (len_val : nat) (memblocks : list nat) (mem_txns_val : nat),
      mem_map len_val memblocks ∗
      ⌜ length memblocks = log_size ⌝ ∗
      ⌜ len_val <= length memblocks ⌝ ∗
      own γmemblocks (● (Excl' (firstn len_val memblocks))) ∗
      mem_txn_next m↦ mem_txns_val ∗
      own γmem_txn_next (● (Excl' mem_txns_val))
    )%I.

  (* Post-crash, pre recovery we know the ptr mapping is in a good state w.r.t the
     abstract state, and the lock must have been reset 0 *)

  Definition CrashInner :=
    (∃ (len_val : nat) (bs : list nat),
        source_state (firstn len_val bs) ∗
        ⌜ len_val <= length bs /\ length bs = log_size ⌝ ∗
        ptr_map len_val bs ∗
        lease_map len_val bs ∗
        log_lock m↦ 0 ∗
        mem_lock m↦ 0 ∗
        mem_map 0 (repeat 0 log_size)
        )%I.

  Definition dN : namespace := (nroot.@"disklock").
  Definition mN : namespace := (nroot.@"memlock").
  Definition iN : namespace := (nroot.@"inner").

  Definition ExecInv :=
    ( source_ctx ∗
      ∃ γmemblocks γdiskpending γcommit_id_exact γmem_txn_next,
      ∃ γdisklock, is_lock dN γdisklock log_lock (DiskLockInv γdiskpending γcommit_id_exact) ∗
      ∃ γmemlock, is_lock mN γmemlock mem_lock (MemLockInv γmemblocks γmem_txn_next) ∗
      inv iN (ExecInner γmemblocks γdiskpending γcommit_id_exact γmem_txn_next))%I.
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


  Lemma write_blocks_ok bs p off len_val:
    (
      ( ExecInv ∗
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
    iDestruct "Hinv" as (γblocks γpending γcommit_id_exact γmem_txn_next γdisklock) "(#Hdisklockinv&#Hinv)".
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
      iSplitL "Hsource Hbsoff Hbsother Hptr Hown Howncommitidexact Hownpending Htxid_map_status Hlog_txns Hmem_txns_part".
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

  Lemma write_mem_blocks_ok blocks p off :
    (
      ( ExecInv ∗
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
    iDestruct "Hinv" as (γblocks γpending γcommit_id_exact γmem_txn_next γdisklock) "(#Hdisklockinv&#Hinv)".
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

  Lemma read_mem_blocks_ok nblocks off res blocks :
    (
      ( ExecInv ∗
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
    iDestruct "Hinv" as (γblocks γpending γcommit_id_exact γmem_txn_next γdisklock) "(#Hdisklockinv&#Hinv)".
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

  Ltac destruct_txid_map_status H :=
    iDestruct H as (committed_pending txid_map Hcid_pre Hcid_mid Hcid_post Hpending_txid_map) "(Hcommitted_pending & Hpending & Htxid_heap)".

  Lemma ghost_var_new_txid next_committed_id pending pa :
    pending_call pa -∗
    txid_map_status next_committed_id pending ==∗
      (
        txid_map_status next_committed_id (pending ++ [pa]) ∗
        (next_committed_id + length pending) s↦{1} (Some (pending_append_to_done pa))
      ).
  Proof.
    iIntros "Hpc Htxid_map_status".
    destruct_txid_map_status "Htxid_map_status".
    iMod (gen_heap_alloc with "Htxid_heap") as "(Htxid_heap & Htxid_j & Hmeta_token)".
    {
      specialize (Hcid_post (next_committed_id + length pending)).
      apply Hcid_post.
      lia.
    }

    iExists _, _.
    iFrame.
    simpl.
    iPureIntro.
    intuition.
    {
      rewrite lookup_insert_ne in H2; try lia.
      auto.
    }
    {
      rewrite app_length in H1; simpl in *.
      rewrite lookup_insert_ne; try lia.
      apply Hcid_post.
      lia.
    }
    {
      destruct (decide (off = length pending)).
      {
        subst.
        rewrite lookup_insert.
        rewrite lookup_app_r in H1; try lia.
        replace (length pending - length pending) with 0 in H1 by lia.
        simpl in H1; inversion H1; subst.
        reflexivity.
      }
      {
        rewrite lookup_insert_ne; try lia.
        apply Hpending_txid_map.
        destruct (lt_dec off (length pending)).
        {
          rewrite lookup_app_l in H1; try lia. auto.
        }
        {
          apply lookup_lt_Some in H1.
          rewrite app_length in H1.
          simpl in H1.
          lia.
        }
      }
    }
  Qed.

  Lemma mem_append {T} j K `{LanguageCtx Log2.Op _ T Log2.l K} blocks :
    (
      ( j ⤇ K (Call (Log2.Append blocks)) ∗ Registered ∗ ExecInv )
      -∗
      WP mem_append blocks {{
        v,
        Registered ∗
        ( ( ⌜v = None⌝ ∗ j ⤇ K (Ret false) ) ∨
          ( ∃ txid, ⌜v = Some txid⌝ ∗ txid s↦{1} Some (PendingDone j K) )
        )
      }}
    )%I.
  Proof.
    iIntros "(Hj&Hreg&(#Hsource_inv&Hinv))".
    iDestruct "Hinv" as (γblocks γpending γcommit_id_exact γmem_txn_next γdisklock) "(#Hdisklockinv&#Hinv)".
    iDestruct "Hinv" as (γmemlock) "(#Hmemlockinv&#Hinv)".

    wp_bind.
    wp_lock "(Hlocked&HML)".
    iDestruct "HML" as (memlen mblocks mem_txn_next) "(Hmemmap & Hmemlen1 & Hmemlen2 & Hmemghost & Hmem_txn_next & Hmem_txn_own)".
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
      2: iApply (wp_wand with "[Hmemdata Hmemghost Hmemlen Hmem_txn_own Hmem_txn_next Hunlock]").
      2: iApply "Hunlock".
      solve_ndisj.
      iExists _, _, _. iFrame. done.

      iIntros.
      iModIntro; iExists _, _, _, _, _, _, _, _; iFrame.
      iSplit.
      { done. }

      wp_ret.
      iLeft.
      iFrame.
      done.

    - wp_bind.
      wp_step.
      wp_bind.

      iApply (wp_wand with "[Hmemdata]").
      {
        iApply write_mem_blocks_ok.
        iFrame.
        iSplit.
        { iFrame "#".
          iExists _, _, _, _, _. iFrame "#".
          iExists _. iFrame "#".
        }
        iPureIntro. lia.
      }

      iIntros (?) "Hmemdata".
      wp_step.
      wp_bind.

      wp_step.
      wp_bind.

      iInv "Hinv" as "H".
      destruct_einner "H".

      iMod (ghost_var_update_nat γblocks (take (memlen + length blocks) (list_inserts mblocks memlen blocks)) with "Hmemghost Hown") as "[Hmemghost Hown]".
      iMod (ghost_var_update γmem_txn_next (mem_txns_val + 1) with "Hmem_txn_own Hmem_txns_part") as "[Hmem_txn_own Hmem_txns_part]".
      iDestruct (wp_unlock_open with "Hmemlockinv Hlocked") as "Hunlock".

      2: iApply (wp_wand with "[Hmemdata Hmemghost Hmemlen Hmem_txn_own Hmem_txn_next Hunlock]").
      2: iApply "Hunlock".
      solve_ndisj.
      iExists _, _, _. iFrame.
      rewrite list_inserts_length. iPureIntro. lia.

      iIntros.

      iMod ((ghost_var_new_txid _ _ (Pending blocks j K)) with "Hj Htxid_map_status") as "(Htxid_map_status & Htxid_j)".

      iModIntro.
      iExists _, _.
      iExists (take (memlen + strings.length blocks) (list_inserts mblocks memlen blocks)).
      iExists _.
      iExists _.
      iExists _.
      iExists _, _.

      iFrame.
      simpl.

      apply take_take_le in Hprefix as Hlen; try lia.

      iSplitL "".
      { iPureIntro. intuition try lia.
        {
          rewrite <- Hprefix.
          rewrite firstn_firstn.
          rewrite min_l; try lia.
          rewrite take_list_inserts_le; try lia.
          rewrite firstn_firstn. rewrite min_l; auto.
        }
        {
          rewrite map_app. rewrite concat_app.
          rewrite <- Hsuffix.
          simpl. rewrite app_nil_r.

          rewrite take_list_inserts; try lia.
          rewrite take_list_inserts_le; try lia.
          rewrite drop_app_le; try lia.
          auto.
          rewrite take_length_le; try lia.
        }
        {
          rewrite app_length; simpl; lia.
        }

        rewrite take_app_le. auto.
        rewrite <- Hpendingprefix.
        rewrite firstn_length. lia.
      }

      wp_ret.
      iRight.
      iExists _.
      iFrame.
      subst.
      done.
  Qed.

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

  Lemma big_sepL_pending_append_to_done : forall pending,
    ([∗ list] k↦x ∈ pending, pending_ret (pending_append_to_done x)) -∗
    ([∗ list] k↦x ∈ map pending_append_to_done pending, pending_ret x).
  Proof.
    intros.
    iIntros "H".
    iApply big_sepL_fmap.
    iApply (big_sepL_impl with "H").
    iModIntro. iIntros (k x) "%Hp".
    iFrame.
  Qed.

  Lemma txid_map_status_inbound : forall next_committed_id pending pd txid,
    txid_map_status next_committed_id pending -∗
      txid s↦{1} pd -∗
      ⌜ txid < next_committed_id + length pending ⌝.
  Proof.
    intros.
    destruct (lt_dec txid (next_committed_id + length pending)); auto.
    iIntros "Htxid_map_status Hcaller_txid".
    iDestruct "Htxid_map_status" as (committed_pending txid_map Hcid_pre Hcid_mid Hcid_post Hpending_txid_map) "[Hcommitted_pending [Hpending Htxid_heap]]".
    iDestruct (gen_heap_valid with "Htxid_heap Hcaller_txid") as %Hcaller_some.
    exfalso.
    rewrite Hcid_post in Hcaller_some.
    congruence.
    lia.
  Qed.

  Lemma map_lookup {T R} (f : T -> R):
    forall l x i,
      l !! i = Some x ->
      map f l !! i = Some (f x).
  Proof.
    induction l0; simpl; intros.
    - rewrite lookup_nil in H1. congruence.
    - destruct i; simpl in *.
      + inversion H1. subst. reflexivity.
      + eauto.
  Qed.

  Lemma txid_map_status_commit : forall E (s : list _) next_committed_id pending diskpending,
    nclose sourceN ⊆ E ->
    firstn (length diskpending) pending = diskpending ->
    source_ctx -∗
    ( source_state s ∗
      txid_map_status next_committed_id pending ) ={E}=∗
    ( source_state (s ++ concat (map pending_blocks diskpending)) ∗
      txid_map_status (next_committed_id + length diskpending) (skipn (length diskpending) pending) ).
  Proof.
    intros.
    iIntros "#Hsource_inv".
    iIntros "(Hsource & Htxid_map_status)".
    iDestruct "Htxid_map_status" as (committed_pending txid_map Hcid_pre Hcid_mid Hcid_post Hpending_txid_map) "[Hcommitted_pending [Hpending Htxid_heap]]".

    iDestruct (step_spec_pending _ _ diskpending with "Hsource_inv") as "Hspec".

    rewrite <- (firstn_skipn (length diskpending) pending) at 1.
    rewrite H2.
    iDestruct (big_sepL_app with "Hpending") as "[Hpending0 Hpending1]".
    iMod ("Hspec" with "[Hpending0 Hsource]") as "[Hsource Hdone]". iFrame.

    iDestruct (big_sepL_pending_append_to_done with "Hdone") as "Hdone".

    iDestruct (big_sepM_list_inserts with "[Hcommitted_pending Hdone]") as "Hcommitted_pending".
    2: {
      iFrame. iFrame.
    }
    { apply Hcid_mid. }

    iFrame.
    iExists _, _.
    iFrame.
    iPureIntro.
    intuition.
    - destruct (lt_dec txid next_committed_id).
      + rewrite lookup_list_insert_lt; try lia. auto.
      + replace (txid) with (next_committed_id + (txid - next_committed_id)) by lia.
        rewrite lookup_list_insert_plus; [| rewrite map_length; lia ].
        edestruct (lookup_lt_is_Some_2 diskpending (txid - next_committed_id)); try lia.
        erewrite map_lookup; eauto.
        rewrite <- H2 in H5.
        rewrite lookup_take in H5; try lia.
        apply Hpending_txid_map in H5.
        replace (next_committed_id + (txid - next_committed_id)) with txid in H5; try lia.
        rewrite H4 in H5. inversion H5. reflexivity.
    - rewrite lookup_list_insert_oob; [| rewrite map_length; lia ].
      apply Hcid_mid. lia.
    - apply Hcid_post.
      rewrite skipn_length in H3. lia.
    - erewrite <- Hpending_txid_map.
      f_equal. rewrite <- plus_assoc. reflexivity.
      rewrite lookup_drop in H3; auto.

  Unshelve.
    auto.
  Qed.

  Lemma txid_map_status_extract {T} next_committed_id pending txid j K `{LanguageCtx Log2.Op _ T Log2.l K}:
    txid < next_committed_id ->
    txid_map_status next_committed_id pending -∗
      txid s↦{1} Some (PendingDone j K) ==∗
      txid_map_status next_committed_id pending ∗ j ⤇ K (Ret true).
  Proof.
    intros.
    iIntros "Htxid_map_status Hcaller_txid".
    iDestruct "Htxid_map_status" as (committed_pending txid_map Hcid_pre Hcid_mid Hcid_post Hpending_txid_map) "[Hcommitted_pending [Hpending Htxid_heap]]".
    iDestruct (gen_heap_valid with "Htxid_heap Hcaller_txid") as %Hcaller_some.

    eapply Hcid_pre in Hcaller_some as Hretsome; try lia.

    iDestruct (big_sepM_delete _ _ txid with "Hcommitted_pending") as "[Hret Hcommitted_pending]".
    eassumption.

    iMod (gen_heap_update _ _ _ None with "Htxid_heap Hcaller_txid") as "[Htxid_heap Hcaller_txid]".

    iExists _, _.
    iFrame.
    iPureIntro.
    intuition.
    - destruct (eq_nat_dec txid txid0).
      {
        subst. rewrite lookup_insert in H4. congruence.
      }
      rewrite lookup_delete_ne; try congruence.
      rewrite lookup_insert_ne in H4; try congruence.
      apply Hcid_pre; auto.
    - rewrite lookup_delete_ne; try lia.
      apply Hcid_mid. lia.
    - rewrite lookup_insert_ne; [| lia ].
      apply Hcid_post.
      lia.
    - erewrite <- Hpending_txid_map; eauto.
      rewrite lookup_insert_ne; auto.
      lia.
  Qed.

  Lemma disk_append_wait {T} txid j K `{LanguageCtx Log2.Op _ T Log2.l K}:
    (
      ( Registered ∗ ExecInv ∗ txid s↦{1} Some (PendingDone j K) )
      -∗
      WP disk_append_wait txid {{
        tt,
        Registered ∗
        j ⤇ K (Ret true)
      }}
    )%I.
  Proof.
    iIntros "(Hreg&#Hi&Hcaller_txid)".
    iLöb as "IH".
    wp_loop.
    wp_bind.
    iDestruct "Hi" as "(Hsource_inv & Hinv)".
    iDestruct "Hinv" as (γblocks γpending γcommit_id_exact γmem_txn_next γdisklock) "(#Hdisklockinv&#Hinv)".
    iDestruct "Hinv" as (γmemlock) "(#Hmemlockinv&#Hinv)".

    iInv "Hinv" as "H".
    destruct_einner "H".
    wp_step.
    destruct (decide (txid < log_txns_val)).

    - iMod (txid_map_status_extract with "Htxid_map_status Hcaller_txid") as "[Htxid_map_status Hret]". lia.
      iModIntro; iExists _, _, _, _, _, _, _, _; iFrame.
      iSplitR. iPureIntro. intuition lia.
      wp_step.
      wp_ret.
      done.

    - iDestruct ("IH" with "Hreg Hcaller_txid") as "IHreg".
      iModIntro; iExists _, _, _, _, _, _, _, _; iFrame.
      iSplitR. iPureIntro. intuition lia.
      wp_step.
      iApply "IHreg".
  Qed.

  Lemma disk_append :
    (
      ( Registered ∗ ExecInv )
      -∗
      WP disk_append {{
        tt,
        Registered
      }}
    )%I.
  Proof.
    iIntros "(Hreg&(#Hsource_inv&Hinv))".
    iDestruct "Hinv" as (γblocks γpending γcommit_id_exact γmem_txn_next γdisklock) "(#Hdisklockinv&#Hinv)".
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
    iDestruct "HML" as (memlen mblocks mem_txn_next) "(Hmemmap & Hmemlen1 & Hmemlen2 & Hmemghost & Hmem_txn_next & Hmem_txn_own)".
    iPure "Hmemlen1" as Hmemlen1; iPure "Hmemlen2" as Hmemlen2.
    iDestruct "Hmemmap" as "[Hmemlen Hmemdata]".

    (* snapshot the pending from memory *)
    wp_bind.
    iInv "Hinv" as "H".
    destruct_einner "H".
    iDestruct (disk_lease_agree_log_data with "Hbs Hbs_ghost") as %Hagree. lia. subst.

    wp_step.

    iMod (ghost_var_update_pending γpending pending0 with "Hdiskpendingown Hownpending") as "[Hdiskpendingown Hownpending]".
    clear Hpendingprefix0. clear Hpendingprefix. clear diskpending.
    iModIntro; iExists _, _, _, _, _, _, _, _; iFrame.
    iSplitR. iPureIntro. intuition try lia.
      rewrite firstn_all. auto.

    wp_bind.
    wp_step.

    wp_bind.
    iApply (wp_wand with "[Hmemdata]").
    iApply read_mem_blocks_ok.
    iFrame. iSplit.
    { iFrame "#".
      iExists _, _, _, _, _. iFrame "#".
      iExists _. iFrame "#". }
    iPureIntro. lia.

    iIntros (?) "[Hlen Hmemdata]".
    iPure "Hlen" as Hlen. subst. simpl.

    wp_unlock "[Hmemlen Hmemdata Hmemghost Hmem_txn_next Hmem_txn_own]".
    {
      iExists _, _, _.
      iFrame.
      iPureIntro. lia.
    }

    wp_bind.
    iApply (wp_wand with "[Hlen_ghost Hbs_ghost]").
    {
      iApply write_blocks_ok.
      iFrame.
      iSplitL.
      - iFrame "#".
        iExists _, _, _, _, _. iFrame "#".
        iExists _. iFrame "#".
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

    iDestruct (txid_map_status_commit with "Hsource_inv [Hsource Htxid_map_status]") as "Hcommit".
    3: { iFrame. }
    shelve.
    eassumption.

    wp_step.

    iMod (ghost_var_update_pending γpending nil with "Hdiskpendingown Hownpending") as "[Hdiskpendingown Hownpending]".
    iMod (ghost_var_update _ (next_committed_id + length diskpending) with "Hnext_committed_exact Howncommitidexact") as "[Hnext_committed_exact Howncommitidexact]".
    iMod "Hcommit" as "[Hsource Htxid_map_status]".

    iModIntro.
    iExists memlen.
    iExists (list_inserts bs len_val (take (memlen - len_val) (drop len_val mblocks))).
    iExists memblocks0.
    iExists (skipn (length diskpending) pending1).
    iExists _.
    iExists _.
    iExists _, _.

    iFrame.
    iSplitR "Hleaseblocks Hleaselen Hlocked Hdiskpendingown Hnext_committed_exact".
    2: {
      wp_bind.

      iInv "Hinv" as "H".
      destruct_einner "H".
      wp_step.
      iModIntro.
      iExists _, _, _, _, _, _, _, _.
      iFrame.
      iSplitR.
      {
        iPureIntro. intuition lia.
      }

      wp_unlock "[Hleaseblocks Hleaselen Hdiskpendingown Hnext_committed_exact]".
      {
        iExists _, _, _, _. iFrame. iPureIntro. lia.
      }

      wp_ret.
      done.
    }

    apply take_take_le in Hprefix0 as Hdisklen; try lia.

    iSplitL "Hsource".
    {
      iNext.
      rewrite take_list_inserts_le; try lia.
      admit.
    }

    iPureIntro. intuition; try lia.
    - admit.
    - admit.
    - rewrite drop_length.
      rewrite <- plus_assoc.
      replace (length diskpending + (length pending1 - length diskpending)) with (length pending1).
      reflexivity.
      admit.

  Unshelve.
    solve_ndisj.
  Admitted.

  Lemma append_refinement {T} j K `{LanguageCtx Log2.Op _ T Log2.l K} p :
    {{{ j ⤇ K (Call (Log2.Append p)) ∗ Registered ∗ ExecInv }}}
      ImplLog2.append p
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Hreg&#Hinv) HΦ".

    iApply wp_bind_proc_subst.
    iApply (wp_wand with "[Hj Hreg]").
    {
      iApply mem_append. iFrame. iApply "Hinv".
    }

    iIntros "% [Hreg H]".
    iNext.
    destruct a.

    - wp_bind.
      iDestruct "H" as "[[%H]|H]". congruence.
      iDestruct "H" as (?) "[%H]".

      iApply (wp_wand with "[H Hreg]").
      {
        inversion H3.
        iApply disk_append_wait. iFrame. iFrame "#".
      }

      iIntros "% [Hreg H]".
      wp_ret.
      iApply "HΦ".
      iFrame.

    - wp_ret.
      iDestruct "H" as "[[%H]|H]".
      + iApply "HΦ". iFrame.
      + iDestruct "H" as (txid) "[%H]". congruence.

  Unshelve.
    simpl.
    eauto.
  Qed.

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
    iDestruct "Hinv" as (γblocks γpending γcommit_id_exact γmem_txn_next γdisklock) "(#Hdisklockinv&#Hinv)".
    iDestruct "Hinv" as (γmemlock) "(#Hmemlockinv&#Hinv)".
    iLöb as "IH" forall (nblocks off res).
    destruct nblocks; simpl.
    - wp_ret.
      rewrite firstn_O. rewrite app_nil_r. iFrame. iPureIntro. auto.
    - wp_bind.

      iInv "Hinv" as "H".
      destruct_einner "H".

      iPure "Hinbound" as ?; intuition.
      iDestruct (disk_lease_agree_log_data with "Hbs Hlease") as %Hx; subst. lia.

      assert (off < length bs) as Hoffbs by lia.
      apply lookup_lt_is_Some_2 in Hoffbs. destruct Hoffbs as [boff Hoffbs].

      iDestruct (big_sepL_lookup_acc with "Hbs") as "[Hbsoff Hbsother]". apply Hoffbs.
      iDestruct (big_sepL_lookup_acc with "Hlease") as "[Hleaseoff Hleaseother]". apply Hoffbs.
      wp_step.
      iDestruct ("Hbsother" with "Hbsoff") as "Hbs".

      iModIntro.
      iExists _, _, _, _, _, _, _, _.
      iFrame.
      iSplitR.
      {
        iPureIntro. intuition.
      }

      iSpecialize ("IH" $! nblocks (off+1) (res ++ [boff])).
      iDestruct ("Hleaseother" with "Hleaseoff") as "Hlease".
      iApply (wp_wand with "[Hlease] []").
      {
        iApply ("IH" with "[%] [Hlease]").
        { lia. }
        iFrame.
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
    iDestruct "Hinv" as (γblocks γpending γcommit_id_exact γmem_txn_next γdisklock) "(#Hdisklockinv&#Hinv)".
    iDestruct "Hinv" as (γmemlock) "(#Hmemlockinv&#Hinv)".

    wp_lock "(Hlocked&HEL)".
    iDestruct "HEL" as (len_val bs diskpending next_committed_id_exact)
                         "((Hlen_ghost&Hbs_ghost)&Hbs_bounds&Hbs_len&Hdiskpendingown&Hnext_committed_exact)".
    iPure "Hbs_bounds" as Hbs_bounds.
    iPure "Hbs_len" as Hbs_len.

    wp_bind.
    iInv "Hinv" as "H".
    destruct_einner "H".
    wp_step.

    iDestruct (disk_lease_agree_log_data with "Hbs Hbs_ghost") as %Hx; subst. lia.

    iMod (ghost_step_lifting with "Hj Hsource_inv Hsource") as "(Hj&Hsource&_)".
    { simpl.
      intros. eexists. do 2 eexists; split; last by eauto. econstructor; eauto.
      econstructor.
    }
    { solve_ndisj. }
    iModIntro; iExists _, _, _, _, _, _, _, _; iFrame.

    iSplit.
    {
      iPureIntro. intuition.
    }

    wp_bind.
    iApply (wp_wand with "[Hbs_ghost]").
    {
      iApply read_blocks_ok.
      iFrame.
      iSplit.
      - iFrame "#". iExists _, _, _, _, _. iFrame "#". iExists _. iFrame "#".
      - iPureIntro. intuition.
    }

    iIntros "% [Hres Hleaseblocks]".
    iPure "Hres" as Hres. subst. simpl.
    rewrite drop_0.

    wp_bind.
    wp_unlock "[-HΦ Hreg Hj]"; iFrame.
    {
      iExists _, _, _, _.
      iFrame.
      iPureIntro. lia.
    }

    wp_ret.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma commit_worker_refinement {T} j K `{LanguageCtx Log2.Op _ T Log2.l K} :
    {{{ j ⤇ K (Call (Log2.CommitWorker)) ∗ Registered ∗ ExecInv }}}
      ImplLog2.disk_append_loop
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Hreg&#Hi) HΦ".
    iLöb as "IH".
    wp_loop.

    wp_bind.
    iApply (wp_wand with "[Hreg]").
    {
      iApply disk_append.
      iFrame. iFrame "#".
    }

    iIntros "% Hreg".
    wp_ret.
    iNext.
    iDestruct ("IH" with "Hj Hreg") as "IH2".
    iApply "IH2".
    iFrame.
  Qed.

  Lemma init_mem_split:
    (([∗ map] i↦v ∈ init_zero, i m↦ v) -∗
      ( log_lock m↦ 0 ∗ log_txn_next m↦ 0 ∗ mem_lock m↦ 0 ∗ mem_count m↦ 0 ∗ mem_txn_next m↦ 0 ) ∗
        [∗ list] pos↦b ∈ repeat 0 log_size, mem_data pos m↦ b
      )%I.
  Proof.
    clear hDone.
    iIntros "Hmem".
    iPoseProof (mem_ptr_iter_split_aux 0 4 with "Hmem") as "(H&Hrest)".
    rewrite /size; lia.
    cbn [ptr_iter plus minus].
    do 4 iDestruct "H" as "[? H]".
    iFrame.
    pose proof log_size_ok.
    iDestruct (rep_delete_init_zero_list with "Hrest") as "[Hdata Hrest]".
    2: iFrame. lia.
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

  Definition helperΣ : gFunctors := #[GFunctor (authR (optionUR (exclR (listO pending_appendC))));
                                      GFunctor (authR (optionUR (exclR (listO natO))));
                                      GFunctor (authR (optionUR (exclR natO)))].
  Instance subG_helperΣ0 : subG helperΣ Σ → inG Σ (authR (optionUR (exclR (listO pending_appendC)))).
  Proof. solve_inG. Qed.
  Instance subG_helperΣ1 : subG helperΣ Σ → inG Σ (authR (optionUR (exclR (listO natO)))).
  Proof. solve_inG. Qed.
  Instance subG_helperΣ2 : subG helperΣ Σ → inG Σ (authR (optionUR (exclR natO))).
  Proof. solve_inG. Qed.

  Definition Σ : gFunctors := #[Adequacy.exmachΣ; @cfgΣ Log2.Op Log2.l; lockΣ; helperΣ; gen_heapΣ nat (option pending_done)].

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

  Global Instance inG_inst2: inG Σ (authR (optionUR (exclR (listO pending_appendC)))).
  Proof. apply _. Qed.

  Global Instance inG_inst3: inG Σ (authR (optionUR (exclR natO))).
  Proof. apply _. Qed.

  Global Instance inG_inst4: lockG Σ.
  Proof. apply _. Qed.

  Definition exec_inv :=
    fun H1 H2 =>
      ( ∃ hG,
        (@ExecInv Σ H2 _ H1 _ _ _ hG) )%I.
  Definition exec_inner :=
    fun H1 H2 =>
      ( ∃ γmemblocks γdiskpending γcommit_id_exact γmem_txn_next hG vm vd,
        log_lock m↦ vd ∗ mem_lock m↦ vm ∗
        ( (⌜ vd = 0 ⌝ -∗ @DiskLockInv Σ H2 _ _ γdiskpending γcommit_id_exact) ∗
          (⌜ vm = 0 ⌝ -∗ @MemLockInv Σ H2 _ _ γmemblocks γmem_txn_next) ∗
            @ExecInner Σ H2 H1 _ _ _ hG γmemblocks γdiskpending γcommit_id_exact γmem_txn_next))%I.

  Definition crash_param := fun (_ : @cfgG OpT Λa Σ) (_ : exmachG Σ) => unit.
  Definition crash_inv := fun H1 H2 (_ : crash_param _ _) =>
    ( ∃ (hG: @gen_heapG nat (option pending_done) Σ nat_eq_dec nat_countable),
      @CrashInv Σ H2 H1 )%I.
  Definition crash_starter :=
    fun H1 H2 (_ : crash_param H1 H2) => (True%I : iProp Σ).
  Definition crash_inner := fun H1 H2 =>
    ( ∃ (hG: @gen_heapG nat (option pending_done) Σ nat_eq_dec nat_countable),
      @CrashInner Σ H2 H1)%I.
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
    red. intros. iIntros "(Hj&Hreg&#HDB)".
    iDestruct "HDB" as (x) "Hinv".
    destruct op.
    - iApply (append_refinement with "[$]"). iNext. iIntros (?) "H". iFrame.
    - iApply (read_refinement with "[$]"). iNext. iIntros (?) "H". iFrame.
    - iApply (commit_worker_refinement with "[$]"). iNext. iIntros (?) "H". iFrame.
  Qed.

  Lemma exec_inv_source_ctx: ∀ {H1 H2}, exec_inv H1 H2 ⊢ source_ctx.
  Proof.
    iIntros (??) "Hinv".
    iDestruct "Hinv" as (hG) "Hinv".
    iDestruct "Hinv" as "[Hsource H]".
    eauto.
  Qed.

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
    red. intros. iIntros "(#Hinv&_)".
    iDestruct "Hinv" as (hG) "[Hctx Hinv]".
    wp_ret.
    iInv "Hinv" as (len_val bs) ">(?&Hlen&Hcase&Hlease&?&?&?)" "_".
    iApply (fupd_mask_weaken _ _).
    { solve_ndisj. }
    iExists (firstn len_val bs). iFrame.
    iExists (firstn len_val bs).
    iSplitL "".
    { iPureIntro; econstructor. }
    iClear "Hctx Hinv".
    iIntros (???) "(#Hctx&Hstate)".
    iMod (ptr_map_next with "Hcase") as "(Hp&Hl)".
    iExists _. iExists _. iExists _. iExists _. iExists _, 0, 0. iFrame.
    iPure "Hlen" as Hlen; intuition.
    iSplitL "Hl"; iModIntro; iIntros.
    - (* iExists _, _; iFrame.
    iPureIntro; intuition.
    iPureIntro; intuition.
    *)
    admit.
  Admitted.

  Lemma init_wf: ∀ σ1a σ1c, init_absr σ1a σ1c → ExMach.state_wf σ1c.
  Proof.
    intros ?? (H&?). inversion H. subst. eapply ExMach.init_state_wf.
  Qed.

  Lemma init_exec_inner : init_exec_inner_type.
  Proof.
    red. intros ?? (H&Hinit) ??. inversion H. inversion Hinit. subst.
    iIntros "(Hmem&Hdisk&#?&Hstate)".

    iMod (gen_heap_strong_init (∅: gmap nat (option pending_done))) as (hG <-) "[Hheapctx Hheapown]".

    iPoseProof (init_mem_split with "Hmem") as "((Hm0&Hm1&Hm2&Hm3&Hm4)&Hmrest)".
    iPoseProof (init_disk_split with "Hdisk") as "((Hd1&Hd2)&(Hl1&Hl2))".

    iMod (ghost_var_alloc (nil : list nat)) as (γmemblocks) "[Hmemblocks0 Hmemblocks1]".
    iExists γmemblocks.

    iMod (ghost_var_alloc (nil : list pending_append)) as (γdiskpending) "[Hdiskpending0 Hdiskpending1]".
    iExists γdiskpending.

    iMod (ghost_var_alloc (0 : nat)) as (γcommit_id_exact) "[Hcommit_id_exact0 Hcommit_id_exact1]".
    iExists γcommit_id_exact.

    iMod (ghost_var_alloc (0 : nat)) as (γmem_txn_next) "[Hmem_txn_next0 Hmem_txn_next1]".
    iExists γmem_txn_next.

    iExists hG.

    iModIntro. iExists 0, 0. iFrame.
    iSplitL "Hl1 Hl2 Hdiskpending0 Hcommit_id_exact0".
    {
      iIntros "_". iExists 0, _, nil, 0. iFrame.
      iPureIntro. intuition. lia. rewrite repeat_length. lia.
    }

    iSplitL "Hm3 Hm4 Hmrest Hmemblocks0 Hmem_txn_next0".
    {
      iIntros "_". iExists 0, (repeat 0 log_size), 0. iFrame.
      iPureIntro. intuition. rewrite repeat_length. lia. lia.
    }

    iExists 0.
    iExists (repeat 0 log_size).
    iExists nil.
    iExists nil.
    iExists nil.
    iExists 0.
    iExists 0.
    iExists 0.
    simpl.
    rewrite firstn_O.
    iFrame.
    unfold txid_map_status.
    repeat ( iSplitR; [ iPureIntro; try rewrite repeat_length; auto; lia | ] ).
    iExists ∅, ∅.
    simpl.
    rewrite big_sepM_empty.
    iFrame.
    iPureIntro. intuition. lia.
    rewrite lookup_nil in H0; congruence.
  Qed.

  Lemma exec_inv_preserve_crash: exec_inv_preserve_crash_type.
  Proof.
    red. intros. iIntros "#Hinv".
    iDestruct "Hinv" as (hG) "Hinv".
    iDestruct "Hinv" as "[Hsource_ctx #Hinv]".
    iDestruct "Hinv" as (γmemblocks γdiskpending γcommit_id_exact γmem_txn_next γdisklock) "[Hdisklock Hmemlock]".
    iDestruct "Hmemlock" as (γmemlock) "[Hmemlock Hinv]".

    iInv "Hinv" as "Hopen" "_".
    destruct_einner "Hopen".
    iApply fupd_mask_weaken; first by solve_ndisj.
    iIntros (??) "Hmem".
    iPoseProof (@init_mem_split with "Hmem") as "((?&?&?&?&?)&?)".
    iMod (ptr_map_next with "[Hptr Hbs]") as "(?&?)"; first by iFrame.
    iModIntro. iExists _, _, _. iFrame.
    iPureIntro. intuition.
  Qed.

  Lemma crash_inv_preserve_crash: crash_inv_preserve_crash_type.
  Proof.
    red. intros. iIntros "#Hinv".
    iDestruct "Hinv" as (hG) "(#Hctx&#Hinv)".
    iInv "Hinv" as ">Hopen" "_".
    iDestruct "Hopen" as (? ?) "(?&Hlen&Hptr&Hlease&Hlock&Hmemlock&Hmemcount&Hmemdata)".
    iApply fupd_mask_weaken; first by solve_ndisj.
    iIntros (??) "Hmem".
    iMod (ptr_map_next with "Hptr") as "(?&?)".
    iModIntro. iExists _, _, _. iFrame.
    iPoseProof (@init_mem_split with "Hmem") as "((?&?&?&?&?)&?)".
    iFrame.
  Qed.

  Lemma crash_inner_inv : crash_inner_inv_type.
  Proof.
    red. intros. iIntros "(Hinv&#Hsrc)".
    iDestruct "Hinv" as (invG) "Hinv".
    iDestruct "Hinv" as (???) "(?&?&?&?&?&?&?)".
    iMod (@inv_alloc Σ (exm_invG) iN _ CrashInner with "[-]").
    { iNext. iExists _, _; iFrame. }
    iModIntro. iFrame. iExists tt. iFrame "Hsrc". done.
  Qed.

  Lemma exec_inner_inv : exec_inner_inv_type.
  Proof.
    red. intros. iIntros "(Hinv&#Hsrc)".
    iDestruct "Hinv" as (invG v) "Hinv".
    iDestruct "Hinv" as (??????) "(Hdisklock&Hmemlock&Hinner1&Hinner2&Hinner3)".
    iMod (@lock_init Σ (ExMachG _ (exm_invG) (exm_mem_inG) (exm_disk_inG) _) _ mN
                     mem_lock _ (MemLockInv _ _) with "[$] [Hinner2]") as (γmemlock) "Hmemlock".
    { iFrame. }
    iMod (@lock_init Σ (ExMachG _ (exm_invG) (exm_mem_inG) (exm_disk_inG) _) _ dN
                     log_lock _ (DiskLockInv _ _) with "[$] [Hinner1]") as (γdisklock) "Hdisklock".
    { iFrame. }
    iMod (@inv_alloc Σ (exm_invG) iN _ (ExecInner _ _ _ _) with "[Hinner3]").
    { iFrame. }
    iModIntro. iFrame "Hsrc". iExists _, _, _, _, _, _. iFrame.
    iExists _. iFrame.
  Qed.

  Lemma exec_inv_preserve_finish : exec_inv_preserve_finish_type.
  Proof.
    iIntros (??) "? H".
    iDestruct "H" as (?) "(#Hctx & H)".
    iDestruct "H" as (?????) "(#Hdisklock&#Hinv)".
    iDestruct "Hinv" as (?) "(#Hmemlock&Hinv)".
    iInv "Hinv" as "H" "_".
    iDestruct "H" as (ptr bs memblocks pending diskpending next_committed_id log_txns_val mem_txns_val) "H".
    iDestruct "H" as ">(Hsource&H)".
    iDestruct "H" as "(H1 & H2 & Hmap & Hmbown & Htake & Hdrop & Hownnext & Htxid_map_status & H3 & H4 & Hmem_txns_val & Hlog_txn_next & Hdiskpending & H6 )".
    iMod (lock_crack with "Hmemlock") as ">H"; first by solve_ndisj.
    iDestruct "H" as (v) "(?&Hm)".
    iMod (lock_crack with "Hdisklock") as ">H"; first by solve_ndisj.
    iDestruct "H" as (v') "(?&Hd)".
    iApply fupd_mask_weaken; first by solve_ndisj.
    iExists _, _; iFrame.
    iSplitL "".
    { iPureIntro. econstructor. }
    iIntros (????) "(?&?&Hmem)".
    iMod (ptr_map_next with "Hmap") as "(Hp&Hl)".
    iPoseProof (@init_mem_split with "Hmem") as "((?&?&?&?&?)&?)".
    iExists _, _, _, _, _, _, _. iFrame.
    iPure "Htake" as ?.
    iPure "Hdrop" as ?.
    iPure "H1" as ?.
    iPure "H2" as ?.
    iPure "H3" as ?.
    iPure "H4" as ?.
    iPure "H6" as ?.
    iSplitL "Hl"; iModIntro; iIntros.
    { iExists _, _, _, _. iFrame. shelve. }
    iSplitL ""; iIntros.
    { iExists _, _, _. shelve. }
    iExists _, _, memblocks, pending, diskpending, next_committed_id, _, mem_txns_val.
    iFrame.
  Admitted.

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
