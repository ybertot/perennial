From Perennial.goose_lang.lib Require Import encoding.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.
From Perennial.algebra Require Import deletable_heap.
From Goose.github_com.mit_pdos.goose_nfsd Require Import barebones common super inode.
From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import buftxn.specs buf.defs buf.specs txn.specs addr.specs marshal_proof.

Section heap.
Context `{!heapG Σ}.
Context `{!crashG Σ}.
Context `{!lockG Σ}.
Context `{!buftxnG Σ}.
Implicit Types (v:val).
Implicit Types (stk:stuckness) (E: coPset).

(* Definition common_NBITBLOCK := disk.block_bytes / 8.
Definition common_META := 8.
Definition common_HDRADDRS :=
Definition common_LOGSIZE := common_HDRADDRS + 2.
Definition nBlockBitmap diskSz := (diskSz / common_NBITBLOCK) + 1.
Definition nLog := common_LOGSIZE.
Definition bnum_BitmapBlockStart := nLog.
Definition bnum_BitmapInodeStart := bnum_BitmapBlockStart +  *)

Definition common_INODESZ : nat := 128.
Definition common_INODEBLK : nat := common_INODESZ / disk.block_bytes.
Definition common_ROOTINUM : nat := 1.

Definition nfstypes__NFS3_OK : nat := 0.

Definition inode_NENTRIES : nat := 8.

Record SuperData : Set := mkSuperData {
(*   superd_size : nat;
  superd_nLog : nat;
  superd_nBlockBitmap : nat;
  superd_nInodeBitmap : nat;
  superd_nInodeBlk : nat;
  superd_maxAddr : nat; *)
  superd_inodeStartPrecomp : nat;
}.

Definition is_super super superd : iProp Σ :=
(*   super ↦[FsSuper.S :: "Size"] #(superd.(superd_size)) ∗
  super ↦[FsSuper.S :: "nLog"] #(superd.(superd_nLog)) ∗
  super ↦[FsSuper.S :: "NBlockBitmap"] #(superd.(superd_nBlockBitmap)) ∗
  super ↦[FsSuper.S :: "NInodeBitmap"] #(superd.(superd_nInodeBitmap)) ∗
  super ↦[FsSuper.S :: "nInodeBlk"] #(superd.(superd_nInodeBlk)) ∗
  super ↦[FsSuper.S :: "Maxaddr"] #(superd.(superd_maxAddr)). *)
  super ↦[FsSuper.S :: "InodeStartPrecomp"] #(superd.(superd_inodeStartPrecomp)) ∗
  ⌜ superd.(superd_inodeStartPrecomp) = O ⌝. (* this is blatantly false but it doesn't matter that much *)

Record FhData : Set := mkFhData {
  fhd_ino : nat;
  fhd_gen : nat;
}.

Definition fhd2val fhd : val := (#fhd.(fhd_ino), (#fhd.(fhd_gen), #())).

Definition is_fh fhl fhd : iProp Σ :=
  fhl ↦[Fh.S :: "Ino"] #(fhd.(fhd_ino)) ∗
  fhl ↦[Fh.S :: "Gen"] #(fhd.(fhd_gen)).

Record InodeEntry : Set := mkInodeEntry {
  inodee_inum : nat;
  inodee_name : nat; (* all our names are one character long *)
}.

Record InodeData : Set := mkInodeData {
  inoded_inum : nat;
  inoded_gen : nat;
  inoded_parent : nat;
  inoded_entries : vec InodeEntry inode_NENTRIES;
}.

Definition inoded_children inoded := vmap inodee_inum (inoded_entries inoded).
Definition inoded_names inoded := vmap inodee_name (inoded_entries inoded).

Definition inoded2fhd inoded := {|
  fhd_ino := inoded.(inoded_inum);
  fhd_gen := inoded.(inoded_gen);
|}.

Definition nat2val (n: nat) := #(n).
Definition inoded_children_val inoded :=
  nat2val <$> vec_to_list (inoded_children inoded).
Definition ascii2val (a: Ascii.ascii) := #(Ascii.nat_of_ascii a).
Definition inoded_names_val inoded :=
  nat2val <$> vec_to_list (inoded_names inoded).

Definition is_inode inodel inoded : iProp Σ :=
  ∃ sl_contents sl_names,
  inodel ↦[Inode.S :: "Inum"] #(inoded.(inoded_inum)) ∗
  inodel ↦[Inode.S :: "Gen"] #(inoded.(inoded_gen)) ∗
  inodel ↦[Inode.S :: "Parent"] #(inoded.(inoded_parent)) ∗
  inodel ↦[Inode.S :: "Contents"] (slice_val sl_contents) ∗
  inodel ↦[Inode.S :: "Names"] (slice_val sl_names) ∗
  is_slice_small sl_contents uint64T 1 (inoded_children_val inoded) ∗
  is_slice_small sl_names uint64T 1 (inoded_names_val inoded).

(* Definition superd_BitmapBlockStart superd := superd.(superd_nLog).
Definition superd_BitmapInodeStart superd :=
  superd_BitmapBlockStart superd + superd.(superd_nBlockBitmap).
Definition superd_InodeStart superd :=
  superd_BitmapInodeStart superd + superd.(superd_nInodeBitmap).
Definition superd_DataStart superd :=
  superd_InodeStart superd + superd.(superd_nInodeBlk). *)
(* ... *)
Definition superd_InodeStart superd :=
  superd.(superd_inodeStartPrecomp).

(* Definition inum2addr superd inum := {|
  addrBlock := superd_InodeStart superd + (inum / common_INODEBLK);
  addrOff := (inum `mod` common_INODEBLK) * common_INODESZ * 8;
|}. *)

(* simplified inum2addr *)
Definition inum2addr superd inum := {|
  addrBlock := superd_InodeStart superd + inum;
  addrOff := 0;
|}.

Definition EncNat n := EncUInt64 (U64 (Z.of_nat n)).

Definition encodes_inode i inoded : iProp Σ :=
  ∃ extra,
  ⌜
    inode_to_vals i = b2val <$> marshal_proof.encode (
      [
        EncUInt64 inoded.(inoded_gen);
        EncUInt64 inoded.(inoded_parent)
      ]
      ++ (EncNat <$> (vec_to_list (inoded_children inoded)))
      ++ (EncNat <$> (vec_to_list (inoded_names inoded)))
    ) ++ extra
  ⌝.

Definition buf_encodes_inode {K} (buf: bufDataT K) inoded : iProp Σ :=
  match buf with
  | bufInode i => encodes_inode i inoded
  | _ => False
  end.

Definition mapsto_txn_inode superd γUnified inoded : iProp Σ :=
  ∃ i,
  mapsto_txn γUnified (inum2addr superd inoded.(inoded_inum)) (bufInode i) ∗
  encodes_inode i inoded.

Definition mapsto_inode superd γT inoded : iProp Σ :=
  ∃ (v: {K & bufDataT K}),
  buf_encodes_inode (projT2 v) inoded ∗
  mapsto (hG := γT) (inum2addr superd inoded.(inoded_inum)) 1 v.

Theorem mapsto_inode_lift inoded superd buftx γT γUnified :
  (
    is_buftxn buftx γT γUnified ∗
    mapsto_txn_inode superd γUnified inoded
  )
    ==∗
  (
    is_buftxn buftx γT γUnified ∗
    mapsto_inode superd γT inoded
  ).
Proof.
  iIntros "[Hbuftxn Hmapsto]".
  iDestruct "Hmapsto" as (i) "[Hmapsto Hencodes]".
  iPoseProof (BufTxn_lift_one _ _ _ _ (existT _ _) with "[Hbuftxn Hmapsto]") as "Hmapsto".
  1: iFrame.
  iDestruct "Hmapsto" as "> [Hbuftxn Hmapsto]".
  iModIntro.
  iFrame.
  iExists _.
  iFrame.
Qed.

Definition mapsto_txn_free_inode superd γUnified inum : iProp Σ :=
  ∃ i,
  mapsto_txn γUnified (inum2addr superd inum) (bufInode i).

Definition mapsto_txn_root_inode superd γUnified root_inoded : iProp Σ :=
  ⌜ root_inoded.(inoded_inum) = common_ROOTINUM ⌝ ∗
  mapsto_txn_inode superd γUnified root_inoded.

Definition inodee_nonnull inodee := inodee.(inodee_inum) ≠ O.

Definition is_barebones_nfs_super nfsl superd : iProp Σ :=
  ∃ (superl: loc),
  nfsl ↦[BarebonesNfs.S :: "fs"] #superl ∗
  is_super superl superd.

Definition is_barebones_nfs_txn nfsl γUnified : iProp Σ :=
  ∃ (txnl: loc),
  nfsl ↦[BarebonesNfs.S :: "txn"] #txnl ∗
  is_txn txnl γUnified.
  
Definition is_barebones_nfs_meta nfsl superd γUnified root_inoded : iProp Σ :=
  is_barebones_nfs_txn nfsl γUnified ∗
  is_barebones_nfs_super nfsl superd ∗
  mapsto_txn_root_inode superd γUnified root_inoded.

Definition is_inode_entry entry name inum :=
  name = entry.(inodee_name) ∧
  inum = entry.(inodee_inum).

Definition non_null_entries_of inoded :=
  filter inodee_nonnull (vec_to_list inoded.(inoded_entries)).

Definition mapsto_txn_inode_entry superd γUnified entry name inoded : iProp Σ :=
  ⌜is_inode_entry entry name inoded.(inoded_inum)⌝
  ∗ mapsto_txn_inode superd γUnified inoded.

Definition mapsto_txn_children root_inoded (name_to_inoded_map : gmap nat InodeData) superd γUnified : iProp Σ :=
  ([∗ maplist] name ↦ inoded; entry ∈ name_to_inoded_map; (non_null_entries_of root_inoded),
    mapsto_txn_inode_entry superd γUnified entry name inoded)%I.

Theorem mapsto_txn_children_delete : ∀ root_inoded (name_to_inoded_map: gmap nat InodeData) non_null_set excluded_name superd γUnified inoded,
  ⌜non_null_entries_of root_inoded ≡ₚ map snd (map_to_list non_null_set)⌝
  ∗ ⌜name_to_inoded_map !! excluded_name = Some inoded⌝
  ∗ ([∗ map] name ↦ inoded; entry ∈ name_to_inoded_map; non_null_set,
    mapsto_txn_inode_entry superd γUnified entry name inoded
  )
  -∗
  ∃ entry,
    ⌜non_null_set !! excluded_name = Some entry⌝
    ∗ mapsto_txn_inode_entry superd γUnified entry excluded_name inoded
    ∗ ([∗ map] name ↦ inoded; entry ∈
        (delete excluded_name name_to_inoded_map);
        (delete excluded_name non_null_set), 
      mapsto_txn_inode_entry superd γUnified entry name inoded
    ).
Proof.
  iIntros (root_inoded name_to_inoded_map non_null_set excluded_name superd γUnified inoded)
    "(%Hnon_null_set & %Hin_map & Hmapsto)".
  iDestruct (big_sepM2_lookup_1_some with "Hmapsto") as %[v Hmk].
  1: eauto.
  rewrite big_sepM2_delete.
  2-3: eassumption.
  iDestruct "Hmapsto" as "[[%Hentry Hinode] Hmapsto]".
  iFrame.
  iExists v.
  eauto.
Qed.

Theorem mapsto_txn_children_undelete : ∀ root_inoded (name_to_inoded_map: gmap nat InodeData) non_null_set excluded_name superd γUnified inoded entry,
  ⌜non_null_entries_of root_inoded ≡ₚ map snd (map_to_list non_null_set)⌝
  ∗ ⌜name_to_inoded_map !! excluded_name = Some inoded⌝
  ∗ ⌜non_null_set !! excluded_name = Some entry⌝
  ∗ mapsto_txn_inode_entry superd γUnified entry excluded_name inoded
  ∗ ([∗ map] name ↦ inoded; entry ∈
      (delete excluded_name name_to_inoded_map);
      (delete excluded_name non_null_set), 
    mapsto_txn_inode_entry superd γUnified entry name inoded
  )
  -∗ ([∗ map] name ↦ inoded; entry ∈ name_to_inoded_map; non_null_set,
    mapsto_txn_inode_entry superd γUnified entry name inoded
  ).
Proof.
  iIntros (root_inoded name_to_inoded_map non_null_set excluded_name superd γUnified inoded entry)
    "(%Hnon_null_set & %Hin_map & %Hin_set & Hexcluded & Hmapsto)".
  replace name_to_inoded_map with
    (<[excluded_name:=inoded]>(delete excluded_name name_to_inoded_map)) at 2.
  2: {
    rewrite insert_delete.
    apply insert_id.
    assumption.
  }
  replace non_null_set with
    (<[excluded_name:=entry]>(delete excluded_name non_null_set)) at 2.
  2: {
    rewrite insert_delete.
    apply insert_id.
    assumption.
  }
  rewrite big_sepM2_insert.
  2-3: apply lookup_delete.
  iFrame.
Qed.

Definition mapsto_txn_free_inodes used_inums superd γUnified : iProp Σ :=
  ∀ (free_inum: nat), ⌜In free_inum used_inums⌝ -∗ 
    mapsto_txn_free_inode superd γUnified free_inum.

Definition used_inums (name_to_inoded_map: gmap nat InodeData) :=
  common_ROOTINUM :: (map (inoded_inum ∘ snd) (map_to_list name_to_inoded_map)).

Definition is_barebones_nfs (nfsl: loc) root_inoded (name_to_inoded_map: gmap nat InodeData) : iProp Σ :=
  ∃ superd γUnified,
  is_barebones_nfs_meta nfsl superd γUnified root_inoded ∗
  mapsto_txn_children root_inoded name_to_inoded_map superd γUnified ∗
  mapsto_txn_free_inodes (used_inums name_to_inoded_map) superd γUnified.

Theorem wp_FsSuper__InodeStart superl superd:
  {{{ is_super superl superd }}}
    FsSuper__InodeStart #superl
  {{{ RET #(superd.(superd_inodeStartPrecomp)); is_super superl superd }}}.
Proof.
  iIntros (Φ) "(Hsuper & Hsuper_lim) HΦ".
  wp_call.
  wp_loadField.
  iApply "HΦ".
  iFrame.
Qed.

Theorem wp_FsSuper__Inum2Addr superl superd inum:
  {{{ is_super superl superd }}}
    FsSuper__Inum2Addr #superl #inum
  {{{ RET (addr2val (inum2addr superd inum)); is_super superl superd }}}.
Proof.
  iIntros (Φ) "Hsuper HΦ".
  wp_call.
  wp_apply (wp_FsSuper__InodeStart with "Hsuper").
  rewrite /addr2val.
  iIntros "Hsuper".
  wp_pures.
  wp_call.
  rewrite /inum2addr.
  simpl.
  replace
    (@word.add _ _ superd.(superd_inodeStartPrecomp) inum)
    with
    (U64 (superd.(superd_inodeStartPrecomp) + inum)).
  2: {
    rewrite /superd_InodeStart.
    word_cleanup.
    unfold word.wrap.
    rewrite -> Zplus_mod_idemp_r.
    rewrite -> Zplus_mod_idemp_l.
    reflexivity.
  }
  iApply "HΦ".
  iFrame.
Qed.

Theorem wp_Inode__decode bufl (inum: u64) a b inoded:
  {{{ is_buf bufl a b
    ∗ buf_encodes_inode b.(bufData) inoded }}}
    inode.Decode #bufl #(inoded.(inoded_inum))
  {{{ inodel, RET #inodel;
    buf_encodes_inode b.(bufData) inoded
    ∗ is_inode inodel inoded }}}.
Proof.
  iIntros (Φ) "(Hbufl & Hbuf) HΦ".
  wp_call.
  wp_apply wp_allocStruct.
  1: repeat (try constructor; try rewrite zero_slice_val; eauto).
  iIntros (inodel') "Hinodel".
  wp_pures.
  iDestruct "Hbufl" as (data sz) "(Haddr & Hsz & Hdata & Hdirty & %Hbuf_addr & %Hbuf_sz & %Hbuf_nonnull & Hbuf_data)".
  wp_loadField.
  destruct b.(bufData); eauto.
  iDestruct "Hbuf" as "%Hbuf_inode".
  destruct Hbuf_inode as (extra & Hbuf_children).
  wp_apply (wp_NewDec with "[Hbuf_data]").
  {
    rewrite /is_buf_data Hbuf_children.
    iFrame.
  }
  iIntros (dec) "[Hdec %Hdec_data]".
  wp_pures.
  iDestruct (struct_fields_split with "Hinodel") as
    "(Hinodel_inum & Hinodel_gen & Hinodel_parent & Hinodel_contents & Hinodel_names & _)".
  wp_storeField.
  wp_apply (wp_Dec__GetInt with "Hdec").
  iIntros "Hdec".
  wp_storeField.
  wp_apply (wp_Dec__GetInt with "Hdec").
  iIntros "Hdec".
  wp_storeField.
  wp_apply (wp_Dec__GetInts with "[Hdec]").
  {
    replace (EncNat <$> _) with
      (EncUInt64 ∘ (U64 ∘ Z.of_nat) <$> vec_to_list (inoded_children inoded)).
    2: {
      eapply map_fmap_ext.
      eauto.
    }
    replace (EncUInt64 ∘ (U64 ∘ Z.of_nat) <$> _) with
      (EncUInt64 <$> (U64 ∘ Z.of_nat <$> vec_to_list (inoded_children inoded))).
    2: {
      symmetry.
      eapply map_fmap_compose.
    }
    iFrame.
    iPureIntro.
    word_cleanup.
    rewrite fmap_length vec_to_list_length.
    eauto.
  }
  iIntros (sl_children) "[Hdec Hsl_children]".
  wp_bind (struct.storeF _ _ _ _).
  iApply (wp_storeField with "Hinodel_contents").
  {
    rewrite /field_ty.
    simpl.
    eauto.
  }
  iIntros "!> Hinodel_contents".
  wp_pures.
  wp_apply (wp_Dec__GetInts with "[Hdec]").
  {
    replace (EncNat <$> _) with
      (EncUInt64 ∘ (U64 ∘ Z.of_nat) <$> vec_to_list (inoded_names inoded)).
    2: {
      eapply map_fmap_ext.
      eauto.
    }
    replace (EncUInt64 ∘ (U64 ∘ Z.of_nat) <$> _) with
      (EncUInt64 <$> (U64 ∘ Z.of_nat <$> vec_to_list (inoded_names inoded))).
    2: {
      symmetry.
      eapply map_fmap_compose.
    }
    instantiate (2:=[]).
    rewrite app_nil_r.
    iFrame.
    iPureIntro.
    word_cleanup.
    rewrite fmap_length vec_to_list_length.
    eauto.
  }
  iIntros (sl_names) "[Hdec Hsl_names]".
  wp_bind (struct.storeF _ _ _ _).
  iApply (wp_storeField with "Hinodel_names").
  {
    rewrite /field_ty.
    simpl.
    eauto.
  }
  iIntros "!> Hinodel_names".
  wp_pures.
  iApply "HΦ".
  iFrame.
  iSplitR.
  1: eauto.
  iExists _, _.
  iFrame.
  iDestruct "Hsl_children" as "[Hsl_children Hsl_children_e]".
  iDestruct "Hsl_names" as "[Hsl_names Hsl_names_e]".
  admit. (* TODO: change nat to u64 for children and names *)
Admitted.

Theorem wp_BarebonesNfs__getInode nfsl buftx superd γT γUnified inoded:
  {{{ is_barebones_nfs_super nfsl superd
    ∗ is_buftxn buftx γT γUnified
    ∗ mapsto_inode superd γT inoded }}}
    BarebonesNfs__getInode #nfsl #buftx #(inoded.(inoded_inum))
  {{{ inodel, RET #inodel;
    is_barebones_nfs_super nfsl superd
    ∗ is_inode inodel inoded
    ∗ is_buftxn buftx γT γUnified
    ∗ mapsto_inode superd γT inoded }}}.
Proof.
  iIntros (Φ) "(Hsuper & Hbuftxn & Hinode) HΦ".
  wp_call.
  iDestruct "Hsuper" as (superl) "[Hsuperl Hsuper]".
  wp_loadField.
  wp_apply (wp_FsSuper__Inum2Addr with "Hsuper").
  iIntros "Hsuper".
  wp_pures.
  rewrite /mapsto_inode.
  iDestruct "Hinode" as (v) "[Hencodes Hinode]".
  replace (@word.mul _ _ 128 8) with (U64 (Z.of_nat (128 * 8))) by eauto.
  destruct v eqn:Hv.
  simpl.
  destruct b eqn:Hb; eauto.
  wp_apply (wp_BufTxn__ReadBuf with "[> Hbuftxn Hinode]").
  {
    iFrame.
    iPureIntro.
    eauto.
  }
  iIntros (bufl dirty) "[Hbuf Hbuftxn]".
  wp_pures.
  wp_apply (wp_Inode__decode with "[Hencodes Hbuf]").
  { apply (U64 0). }
  { iFrame. }
  iIntros (inodel) "(Hencodes & Hinode)".
  wp_pures.
  iApply "HΦ".
  iDestruct ("Hbuftxn" $! b dirty) as "Hbuftxn".
  iSplitL "Hsuperl Hsuper".
  {
    iExists superl.
    iFrame.
  }
  iSplitL "Hinode".
  1: iFrame.
  rewrite Hb.
  admit. (* no more is_buf? *)
  (* iSpecialize ("Hbuftxn" with "[Hbuf]"). 1: eauto.
  rewrite sep_exist_l.
  iExists _.
  iFrame. *)
  (* iDestruct "Hbuftxn" as "[Hinode Hbuftxn]".
  iFrame. *)
  (* fancy update *)
Admitted.

Theorem wp_BarebonesNfs__getInodeByFh nfsl buftx γT γUnified superd inoded:
  {{{ is_buftxn buftx γT γUnified
    ∗ is_barebones_nfs_super nfsl superd
    ∗ mapsto_inode superd γT inoded }}}
    BarebonesNfs__getInodeByFh #nfsl #buftx (fhd2val (inoded2fhd inoded))
  {{{ inodel, RET (#inodel, #(U32 nfstypes__NFS3_OK));
    is_buftxn buftx γT γUnified
    ∗ is_barebones_nfs_super nfsl superd
    ∗ mapsto_inode superd γT inoded
    ∗ is_inode inodel inoded }}}.
Proof.
  iIntros (Φ) "(Hbuftxn & Hsuper & Hinode) HΦ".
  wp_call.
  wp_apply (wp_BarebonesNfs__getInode with "[Hbuftxn Hsuper Hinode]").
  1: iFrame.
  iIntros (inodel) "(Hsuper & Hinodel & Hbuftxn & Hinode)".
  wp_pures.
  iDestruct "Hinodel" as (sl_contents sl_names) "(Hinum & Hgen & Hinode_rest)".
  wp_loadField.
  rewrite /inoded2fhd /fhd2val.
  wp_pures.
  wp_if_destruct.
  {
    rewrite -> base.negb_true in Heqb.
    apply bool_decide_eq_false in Heqb.
    intuition.
  }
  wp_pures.
  iApply "HΦ".
  iFrame.
  iExists sl_contents, sl_names.
  iFrame.
Qed.

Theorem wp_BarebonesNfs__opGetAttr nfsl fhd root_inoded name_to_inoded_map inoded:
  {{{ is_barebones_nfs nfsl root_inoded name_to_inoded_map
    ∗ ⌜
      inoded2fhd inoded = fhd ∧
      (
        inoded.(inoded_inum) = common_ROOTINUM
        ∨ (∃ name, name_to_inoded_map !! name = Some inoded)
      )
    ⌝ }}}
    BarebonesNfs__OpGetAttr #nfsl (fhd2val fhd)
  {{{ inodel, RET (#inodel, #(U32 nfstypes__NFS3_OK));
    is_barebones_nfs nfsl root_inoded name_to_inoded_map
    ∗ is_inode inodel inoded }}}.
Proof.
  iIntros (Φ) "(Hbarebones & %Hfd) HΦ".
  wp_call.
  iDestruct "Hbarebones" as (superd γUnified)
    "((Htxn & Hsuper & Hinode_r) & Hinode_c & Hinode_f)".
  iDestruct "Htxn" as (txnl) "[Htxnl Htxn]".
  wp_loadField.
  iPoseProof (is_txn_dup with "Htxn") as "[Htxn Htxn_now]".
  wp_apply (wp_buftxn_Begin with "Htxn_now").
  iIntros (buftx γT) "Hbuftxn".
  wp_pures.
  destruct Hfd as [Hfd [ Hinum | (name & Hinoded) ]].
  1: admit. (* root inode *)

  iDestruct "Hinode_c" as (non_null_set) "[%Hnon_null_set Hinode_c]".
  iPoseProof (mapsto_txn_children_delete with "[Hinode_c]") as (entry) "(%Hin_set & [%Hentry Hinode] & Hinode_c)".
  1: eauto.
  subst fhd.
  iPoseProof (mapsto_inode_lift with "[Hbuftxn Hinode]") as "> [Hbuftxn Hinode]".
  1: iFrame.

  wp_apply (wp_BarebonesNfs__getInodeByFh with "[Hbuftxn Hsuper Hinode]").
  1: iFrame.
  iIntros (inodel) "(Hbuftxn & Hsuper & Hinode & Hinodel)".
  wp_pures.
  iDestruct "Hinode" as (v) "[Hinode_buf Hinode]".
  wp_apply (wp_BufTxn__CommitWait _ _ _
    (<[_:=_]>∅
  ) with
    "[Hbuftxn Hinode]").
  {
    iFrame.
    rewrite -> big_sepM_insert by eauto.
    eauto.
  }
  iIntros (ok) "Hinode".
  wp_pures.
  iApply "HΦ".
  iFrame.
  iExists superd, γUnified.
  iFrame.
  iSplitL "Htxnl Htxn".
  {
    iExists _.
    iFrame.
  }
  iExists non_null_set.
  iSplit.
  1: eauto.
  iApply mapsto_txn_children_undelete.
  rewrite big_sepM_insert.
  2: eauto.
  iDestruct "Hinode" as "[Hinode _]".
  iFrame.
  iSplit. 1: eauto.
  iSplit. 1: eauto.
  iSplit. 1: eauto.
  rewrite /mapsto_txn_inode_entry.
  iSplit. 1: eauto.
  destruct v eqn:Hv.
  rewrite /buf_encodes_inode.
  destruct b eqn:Hb.
  1,3: eauto.
  iExists i.
  simpl.
  iFrame.
Admitted.

End heap.
