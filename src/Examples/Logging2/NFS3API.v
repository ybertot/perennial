From Coq Require Import List.

From Perennial Require Export Lib.
Import RelationNotations.

Module NFS3.

  (** Basic types used in NFS operations *)

  Inductive err :=
  | ERR_PERM
  | ERR_NOENT
  | ERR_IO
  | ERR_NXIO
  | ERR_ACCES
  | ERR_EXIST
  | ERR_XDEV
  | ERR_NODEV
  | ERR_NOTDIR
  | ERR_ISDIR
  | ERR_INVAL
  | ERR_FBIG
  | ERR_NOSPC
  | ERR_ROFS
  | ERR_MLINK
  | ERR_NAMETOOLONG
  | ERR_NOTEMPTY
  | ERR_DQUOT
  | ERR_STALE
  | ERR_REMOTE
  | ERR_BADHANDLE
  | ERR_NOT_SYNC
  | ERR_BAD_COOKIE
  | ERR_NOTSUPP
  | ERR_TOOSMALL
  | ERR_SERVERFAULT
  | ERR_BADTYPE
  | ERR_JUKEBOX
  .

  Inductive ftype :=
  | NF3REG
  | NF3DIR
  | NF3BLK
  | NF3CHR
  | NF3LNK
  | NF3SOCK
  | NF3FIFO
  .

  Definition fh := nat.
  Definition writeverf := nat.
  Definition createverf := nat.
  Definition cookieverf := nat.
  Definition filename := string.

  (* XXX fix later *)
  Definition uint32 := nat.
  Definition uint64 := nat.

  Definition fileid := uint64.
  Definition cookie := uint64.

  Record fattr := mkFattr {
    fattr_type : ftype;
    fattr_mode : uint32;
    fattr_nlink : uint32;
    fattr_uid : uint32;
    fattr_gid : uint32;
    fattr_size : uint64;
    fattr_used : uint64;
    fattr_rdev_major : uint32;
    fattr_rdev_minor : uint32;
    fattr_fsid : uint64;
    fattr_fileid : fileid;
    fattr_atime : uint64;
    fattr_mtime : uint64;
    fattr_ctime : uint64;
  }.

  Record wcc_attr := mkWcc {
    wcc_size : uint64;
    wcc_mtime : uint64;
    wcc_ctime : uint64;
  }.

  Record wcc_data := mkWccData {
    wcc_before : option wcc_attr;
    wcc_after : option wcc_attr;
  }.

  Inductive set_time :=
  | SET_TO_CLIENT_TIME (t : uint64)
  | SET_TO_SERVER_TIME
  .

  Record sattr := mkSattr {
    sattr_mode : option uint32;
    sattr_uid : option uint32;
    sattr_gid : option uint32;
    sattr_size : option uint64;
    sattr_atime : option set_time;
    sattr_mtime : option set_time;
  }.

  Record dirop := mkDirop {
    dirop_dir : fh;
    dirop_fn : filename;
  }.

  Inductive stable :=
  | UNSTABLE
  | DATA_SYNC
  | FILE_SYNC
  .

  Inductive createhow :=
  | UNCHECKED (_ : sattr)
  | GUARDED (_ : sattr)
  | EXCLUSIVE (_ : createverf)
  .

  Definition post_op_attr := option fattr.
  Definition post_op_fh := option fh.

  Context {buf : Type}.
  Context `{!EqDecision buf}.
  Context `{!Countable buf}.

  (** Return type wrappers that include an error code *)

  Inductive res A T :=
  | OK (always : A) (v : T)
  | Err (always : A) (e : err)
  .

  Definition res2 A T1 T2 := res A (T1 * T2).
  Definition OK2 `{always : A} `{v1 : T1} `{v2 : T2} := OK always (v1, v2).

  (** Result types of different operations, when the operation
      returns more than one thing *)

  Record write_ok := {
    write_ok_count : uint32;
    write_ok_committed : stable;
    write_ok_verf : writeverf;
  }.

  Record readdir_entry := {
    readdir_entry_id : fileid;
    readdir_entry_name : filename;
    readdir_entry_cookie : cookie;
  }.

  Record readdir_ok := {
    readdir_ok_cookieverf : cookieverf;
    readdir_ok_eof : bool;
    readdir_ok_ents : list readdir_entry;
  }.

  Record readdirplus_entry := {
    readdirplus_entry_id : fileid;
    readdirplus_entry_name : filename;
    readdirplus_entry_cookie : cookie;
    readdirplus_entry_attr : post_op_attr;
    readdirplus_entry_fh : post_op_fh;
  }.

  Record readdirplus_ok := {
    readdirplus_ok_cookieverf : cookieverf;
    readdirplus_ok_eof : bool;
    readdirplus_ok_ents : list readdirplus_entry;
  }.

  Record fsstat_ok := {
    fsstat_ok_tbytes : uint64;
    fsstat_ok_fbytes : uint64;
    fsstat_ok_abytes : uint64;
    fsstat_ok_tfiles : uint64;
    fsstat_ok_ffiles : uint64;
    fsstat_ok_afiles : uint64;
    fsstat_ok_invarsec : uint32;
  }.

  Record fsinfo_ok := {
    fsinfo_ok_rtmax : uint32;
    fsinfo_ok_rtpref : uint32;
    fsinfo_ok_rtmult : uint32;
    fsinfo_ok_wtmax : uint32;
    fsinfo_ok_wtpref : uint32;
    fsinfo_ok_wtmult : uint32;
    fsinfo_ok_dtpref : uint32;
    fsinfo_ok_maxfilesize : uint64;
    fsinfo_ok_time_delta : uint64;
    fsinfo_ok_properties : uint32;
  }.

  Record pathconf_ok := {
    pathconf_ok_linkmax : uint32;
    pathconf_ok_name_max : uint32;
    pathconf_ok_no_trunc : bool;
    pathconf_ok_chown_restricted : bool;
    pathconf_ok_case_insensitive : bool;
    pathconf_ok_case_preserving : bool;
  }.

  Inductive Op : Type -> Type :=
  | NULL :
      Op unit
  | GETATTR (_ : fh) :
      Op (res unit fattr)
  | SETATTR (_ : fh) (a : sattr) (ctime_guard : option uint64) :
      Op (res wcc_data unit)
  | LOOKUP (_ : dirop) :
      Op (res2 post_op_attr fh post_op_attr)
  | ACCESS (_ : fh) (a : uint32) :
      Op (res post_op_attr uint32)
  | READLINK (_ : fh) :
      Op (res post_op_attr string)
  | READ (_ : fh) (off : uint64) (count : uint32) :
      Op (res2 post_op_attr bool buf)
  | WRITE (_ : fh) (off : uint64) (_ : stable) (data : buf) :
      Op (res wcc_data write_ok)
  | CREATE (_ : dirop) (_ : createhow) :
      Op (res2 wcc_data post_op_fh post_op_attr)
  | MKDIR (_ : dirop) (_ : sattr) :
      Op (res2 wcc_data post_op_fh post_op_attr)
  | SYMLINK (_ : dirop) (_ : sattr) (_ : filename) :
      Op (res2 wcc_data post_op_fh post_op_attr)
  | MKNOD (_ : dirop) (_ : ftype) (_ : sattr) (major : uint32) (minor : uint32) :
      Op (res2 wcc_data post_op_fh post_op_attr)
  | REMOVE (_ : dirop) :
      Op (res wcc_data unit)
  | RMDIR (_ : dirop) :
      Op (res wcc_data unit)
  | RENAME (from : dirop) (to : dirop) :
      Op (res (wcc_data * wcc_data) unit)
  | LINK (_ : fh) (link : dirop) :
      Op (res (wcc_data * post_op_attr) unit)
  | READDIR (_ : fh) (_ : cookie) (_ : cookieverf) (count : uint32) :
      Op (res post_op_attr readdir_ok)
  | READDIRPLUS (_ : fh) (_ : cookie) (_ : cookieverf) (dircount : uint32) (maxcount : uint32) :
      Op (res post_op_attr readdirplus_ok)
  | FSSTAT (_ : fh) :
      Op (res post_op_attr fsstat_ok)
  | FSINFO (_ : fh) :
      Op (res post_op_attr fsinfo_ok)
  | PATHCONF (_ : fh) :
      Op (res post_op_attr pathconf_ok)
  | COMMIT (_ : fh) (off : uint64) (count : uint32) :
      Op (res wcc_data writeverf)
  .

  (* XXX done up to this point *)

  Record file_state := mkFileState {
    latest:  nfs3_buf;
    pending: gset nfs3_buf;
  }.

  Inductive inode_state :=
  | Dir : gmap nfs3_filename nfs3_fh -> inode_state
  | File : file_state -> inode_state
  .

  Definition State := gmap nfs3_fh inode_state.

  Parameter inode_attrs : inode_state -> nfs3_fattr.
  Parameter read_data : nfs3_buf -> nat -> nat -> nfs3_buf.
  Parameter write_data : nfs3_buf -> nat -> nfs3_buf -> nfs3_buf.
  Parameter len_data : nfs3_buf -> nat.
  Parameter empty_data : nfs3_buf.
  Context `{!ElemOf nfs3_fh (gmap nfs3_fh inode_state)}.

  Definition inode_crash (s : option inode_state) (s' : option inode_state) : Prop :=
    match s, s' with
    | None, None => True
    | Some (Dir d), Some (Dir d') => d = d'
    | Some (File (mkFileState latest pending)), Some (File (mkFileState latest' pending')) =>
      latest' ∈ pending ∪ {[latest]} /\ pending' = ∅
    | _, _ => False
    end.

  Definition inode_finish (s : inode_state) : inode_state :=
    match s with
    | Dir d => s
    | File (mkFileState latest pending) =>
      File (mkFileState latest ∅)
    end.

  Definition dynamics : Dynamics Op State :=
    {| step T (op: Op T) :=
          match op with
          | Lookup d n =>
            i <- reads (fun s => s !! d);
            match i with
            | None => pure None
            | Some (File _) => pure None
            | Some (Dir dents) => pure (dents !! n)
            end
          | Getattr fh =>
            i <- reads (fun s => s !! fh);
            match i with
            | None => pure None
            | Some i => pure (Some (inode_attrs i))
            end
          | Read fh off count =>
            i <- reads (fun s => s !! fh);
            match i with
            | None => pure None
            | Some (Dir _) => pure None
            | Some (File (mkFileState latest _)) =>
              pure (Some (read_data latest off count))
            end
          | Write fh off buf =>
            i <- reads (fun s => s !! fh);
            match i with
            | None => pure None
            | Some (Dir _) => pure None
            | Some (File (mkFileState latest pending)) =>
              _ <- puts (fun s =>
                <[fh := File (mkFileState (write_data latest off buf) (pending ∪ {[latest]}))]> s);
              pure (Some (len_data buf))
            end
          | Create d n =>
            i <- reads (fun s => s !! d);
            match i with
            | None => pure None
            | Some (File _) => pure None
            | Some (Dir dents) =>
              fh <- such_that (fun s fh => fh ∉ s);
              _ <- puts (fun s =>
                <[fh := File (mkFileState empty_data ∅)]> s);
              pure (Some fh)
            end
          | Commit fh =>
            i <- reads (fun s => s !! fh);
            match i with
            | None => pure tt
            | Some (Dir _) => pure tt
            | Some (File (mkFileState vbuf pending)) =>
              _ <- puts (fun s =>
                <[fh := File (mkFileState vbuf ∅)]> s);
              pure tt
            end
          end;
       crash_step :=
          s' <- such_that (fun (s s' : State) => forall fh, inode_crash (s !! fh) (s' !! fh));
          _ <- puts (fun _ => s');
          pure tt;
       finish_step :=
          _ <- puts (fun s => fmap inode_finish s);
          pure tt;
    |}.

  Lemma crash_total_ok (s: State):
    exists s', dynamics.(crash_step) s (Val s' tt).
  Proof.
    repeat (eexists; econstructor).
    econstructor. intros.
    instantiate (1 := fmap inode_finish s).
    rewrite lookup_fmap.
    destruct (s !! fh) eqn:He; rewrite He; simpl; auto.
    destruct i; simpl; auto.
    destruct f; simpl; auto.
    intuition.
    eapply elem_of_union; right.
    eapply elem_of_singleton; auto.
  Qed.

  Lemma crash_non_err_ok (s: State) ret:
    dynamics.(crash_step) s ret -> ret ≠ Err.
  Proof.
    intros.
    destruct ret; try congruence.
    repeat intuition || match goal with
    | H: _ _ Err |- _ => inversion H; clear H
    | H: _ _ _ Err |- _ => inversion H; clear H
    | H: ∃ _, _ |- _ => destruct H
    end.
  Qed.

  Lemma finish_total_ok (s: State):
    exists s', dynamics.(finish_step) s (Val s' tt).
  Proof.
    repeat (eexists; econstructor).
  Qed.

  Lemma finish_non_err_ok (s: State) ret:
    dynamics.(finish_step) s ret -> ret ≠ Err.
  Proof.
    intros.
    destruct ret; try congruence.
    repeat intuition || match goal with
    | H: _ _ Err |- _ => inversion H; clear H
    | H: _ _ _ Err |- _ => inversion H; clear H
    | H: ∃ _, _ |- _ => destruct H
    end.
  Qed.

  Definition l : Layer Op :=
    {| Layer.OpState := State;
       sem := dynamics;
       trace_proj := fun _ => nil;
       crash_preserves_trace := fun _ _ _ => eq_refl;
       crash_total := crash_total_ok;
       finish_total := finish_total_ok;
       crash_non_err := crash_non_err_ok;
       finish_non_err := finish_non_err_ok;
       initP := fun s => s = ∅ |}.

End NFS3.
