From Coq Require Import List.
From RecordUpdate Require Import RecordSet.
From Perennial Require Export Lib.
Import RecordSetNotations.

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

  Record time := {
    time_sec : uint32;
    time_nsec : uint32;
  }.

  Global Instance EqDec_time : EqDecision time.
    intro; intros.
    destruct x, y.
    destruct (eq_nat_dec time_sec0 time_sec1).
    destruct (eq_nat_dec time_nsec0 time_nsec1).
    - left; subst; auto.
    - right; subst; congruence.
    - right; subst; congruence.
  Defined.

  Record major_minor := {
    major : uint32;
    minor : uint32;
  }.

  Record fattr := {
    fattr_type : ftype;
    fattr_mode : uint32;
    fattr_nlink : uint32;
    fattr_uid : uint32;
    fattr_gid : uint32;
    fattr_size : uint64;
    fattr_used : uint64;
    fattr_rdev : major_minor;
    fattr_fsid : uint64;
    fattr_fileid : fileid;
    fattr_atime : time;
    fattr_mtime : time;
    fattr_ctime : time;
  }.

  Record wcc_attr := {
    wcc_size : uint64;
    wcc_mtime : time;
    wcc_ctime : time;
  }.

  Record wcc_data := {
    wcc_before : option wcc_attr;
    wcc_after : option wcc_attr;
  }.

  Definition wcc_data_none := Build_wcc_data None None.

  Inductive set_time :=
  | SET_TO_CLIENT_TIME (t : time)
  | SET_TO_SERVER_TIME
  .

  Record sattr := {
    sattr_mode : option uint32;
    sattr_uid : option uint32;
    sattr_gid : option uint32;
    sattr_size : option uint64;
    sattr_atime : option set_time;
    sattr_mtime : option set_time;
  }.

  Record dirop := {
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

  Inductive mknod_type :=
  | mknod_chr (_ : major_minor)
  | mknod_blk (_ : major_minor)
  | mknod_sock
  | mknod_fifo
  .

  Definition post_op_attr := option fattr.
  Definition post_op_fh := option fh.

  (** Buffers define chunks of data for reads and writes,
      and also the state of a file. *)

  Context {buf : Type}.
  Context `{!EqDecision buf}.
  Context `{!Countable buf}.

  Parameter read_buf : buf -> nat -> nat -> buf.
  Parameter write_buf : buf -> nat -> buf -> buf.
  Parameter len_buf : buf -> nat.
  Parameter empty_buf : buf.
  Parameter resize_buf : nat -> buf -> buf. (* fill with zero if growing *)

  Record async `{Countable T} := {
    latest : T;
    pending : list T;
  }.

  Arguments async T {EqDecision1 H}.

  Definition possible `{Countable T} (ab : async T) :=
    latest ab :: pending ab.

  Definition sync `{Countable T} (v : T) : async T :=
    Build_async _ v nil.

  Definition async_put `{Countable T} (v : T) (a : async T) :=
    Build_async _ v (possible a).

  (** Return type wrappers that include an error code *)

  Inductive res A T :=
  | OK (always : A) (v : T)
  | Err (always : A) (e : err)
  .

  Arguments Err {A T}.

  Definition res2 A T1 T2 := res A (T1 * T2).
  Definition OK2 `(always : A) `(v1 : T1) `(v2 : T2) := OK always (v1, v2).

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
    fsinfo_ok_time_delta : time;
    fsinfo_ok_properties_link : bool;
    fsinfo_ok_properties_symlink : bool;
    fsinfo_ok_properties_homogeneous : bool;
    fsinfo_ok_properties_cansettime : bool;
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
  | SETATTR (_ : fh) (a : sattr) (ctime_guard : option time) :
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
  | MKNOD (_ : dirop) (_ : mknod_type) (_ : sattr) :
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

  Inductive inode_type_state :=
  | Ifile (_ : buf) (_ : createverf)
  | Idir (_ : gmap filename fh)
  | Iblk (_ : major_minor)
  | Ichr (_ : major_minor)
  | Isymlink (_ : filename)
  | Isock
  | Ififo
  .

  Record inode_meta := {
    inode_meta_mode : uint32;
    inode_meta_uid : uint32;
    inode_meta_gid : uint32;
    inode_meta_fileid : fileid;
    inode_meta_atime : time;
    inode_meta_mtime : time;
    inode_meta_ctime : time;
  }.

  Global Instance eta_inode_meta : Settable _ :=
    settable! Build_inode_meta
      < inode_meta_mode;
        inode_meta_uid;
        inode_meta_gid;
        inode_meta_fileid;
        inode_meta_atime;
        inode_meta_mtime;
        inode_meta_ctime >.

  Record inode_state := {
    inode_state_meta : inode_meta;
    inode_state_type : inode_type_state;
  }.

  Global Instance eta_inode_state : Settable _ :=
    settable! Build_inode_state
      < inode_state_meta; inode_state_type >.

  Global Instance eq_dec_inode_meta : EqDecision inode_meta.
  Admitted.

  Global Instance eq_dec_inode_state : EqDecision inode_state.
  Admitted.

  Global Instance countable_inode_state : Countable inode_state.
  Admitted.

  Record State := {
    fhs : gmap fh (async inode_state);
    verf : writeverf;
    clock : time;
  }.

  Global Instance eta_State : Settable _ :=
    settable! Build_State
      < fhs; verf; clock >.

  Definition inode_attrs (i : inode_state) (nlink : uint32) : fattr :=
    let m := inode_state_meta i in
    Build_fattr
      ( match (inode_state_type i) with
        | Ifile _ _ => NF3REG
        | Idir _ => NF3DIR
        | Iblk _ => NF3BLK
        | Ichr _ => NF3CHR
        | Isymlink _ => NF3LNK
        | Isock => NF3SOCK
        | Ififo => NF3FIFO
        end )
      (inode_meta_mode m)
      nlink
      (inode_meta_uid m)
      (inode_meta_gid m)
      ( match (inode_state_type i) with
        | Ifile b _ => len_buf b
        | _ => 0
        end )
      0
      ( match (inode_state_type i) with
        | Iblk mm => mm
        | Ichr mm => mm
        | _ => Build_major_minor 0 0
        end )
      0
      (inode_meta_fileid m)
      (inode_meta_atime m)
      (inode_meta_mtime m)
      (inode_meta_ctime m)
    .

  Definition inode_wcc (i : inode_state) : wcc_attr :=
    let m := inode_state_meta i in
    Build_wcc_attr
      ( match (inode_state_type i) with
        | Ifile b _ => len_buf b
        | _ => 0
        end )
      (inode_meta_mtime m)
      (inode_meta_ctime m).

  Definition inode_crash (i i' : async inode_state) : Prop :=
    latest i' ∈ possible i /\ pending i' = nil.

  Definition inode_crash_opt (s s' : option (async inode_state)) : Prop :=
    match s, s' with
    | None, None => True
    | Some i, Some i' => inode_crash i i'
    | _, _ => False
    end.

  Definition inode_finish (s : async inode_state) : async inode_state :=
    Build_async _ (latest s) nil.

  (** Step definitions for each RPC opcode *)

  Section SymbolicStep.

    Inductive SpecOp : Type -> Type :=
    | SymBool : SpecOp bool
    | SymFH : SpecOp fh
    | Unreachable : SpecOp unit
    | Reads : SpecOp State
    | Puts : State -> SpecOp unit
    .

    Import ProcNotations.
    Open Scope proc.

    Definition symBool := Call SymBool.
    Definition reads {T : Type} (read_f : State -> T) :=
      s <- Call Reads;
      Ret (read_f s).
    Definition puts (put_f : State -> State) :=
      s <- Call Reads;
      Call (Puts (put_f s)).
    Definition pure `(v : T) := @Ret SpecOp _ v.

    Definition spec_proc := proc SpecOp.

    Definition null_step : spec_proc unit :=
      pure tt.

    Definition count_links_dir (count_fh : fh) (dir_fh : fh) : nat :=
      if (decide (count_fh = dir_fh)) then 1 else 0.

    Definition add_up `{Countable T} (m : gmap T nat) : nat :=
      map_fold (fun k v acc => plus acc v) 0 m.

    Definition count_links (fh : fh) (i : inode_state) : nat :=
      match inode_state_type i with
      | Idir d =>
        add_up (fmap (count_links_dir fh) d)
      | _ => 0
      end.

    Definition get_fh {A T} (f : fh) (a : A) `(rx : inode_state -> spec_proc (res A T)) : spec_proc (res A T) :=
      i <- reads (fun s => s.(fhs) !! f);
      match i with
      | None =>
        z <- symBool;
        if z then
          Ret (Err a ERR_STALE)
        else
          Ret (Err a ERR_BADHANDLE)
      | Some i => rx (latest i)
      end.

    Notation "x <~- p1 ; p2" := (p1 (fun x => p2))
                                 (at level 54, right associativity, only parsing).

    Definition inode_attr (f : fh) (i : inode_state) : spec_proc fattr :=
      nlink <- reads (fun s => add_up (fmap (count_links f) (fmap latest s.(fhs))));
      pure (inode_attrs i nlink).

    Definition getattr_step (f : fh) : spec_proc (res unit fattr) :=
      i <~- get_fh f tt;
      attrs <- inode_attr f i;
      pure (OK tt attrs).

  End SymbolicStep.

Check getattr_step.
Require Import Extraction.
Extraction Language JSON.
Recursive Extraction getattr_step.

    Definition check_ctime_guard {A T} (i : inode_state) (ctime_guard : option time)
                                       (a : A) (rx : unit -> relation State State (res A T)) :=
      match ctime_guard with
      | None => rx tt
      | Some ct =>
        if (decide (ct = i.(inode_state_meta).(inode_meta_ctime))) then
          rx tt
        else
          pure (Err a ERR_NOT_SYNC)
      end.

    Definition time_ge (t t' : time) :=
      t'.(time_sec) > t.(time_sec) \/
      t'.(time_sec) = t.(time_sec) /\ t'.(time_nsec) >= t.(time_nsec).

    Definition get_time : relation State State time :=
      t <- reads (clock);
      t' <- such_that (fun _ t' => time_ge t t');
      _ <- puts (set clock (constructor t'));
      pure t'.

    Definition set_attr_one {F} (i : inode_state) (now : time)
                                (f : inode_meta -> F)
                                `{!Setter f}
                                (sattr_req : option F) :
                                inode_state :=
      match sattr_req with
      | None => i
      | Some v =>
       i <| inode_state_meta ::=
            fun m => m <| inode_meta_ctime := now |> <| f := v |> |>
      end.

    Definition set_attr_time (i : inode_state) (now : time)
                             (f : inode_meta -> time)
                             `{!Setter f}
                             (sattr_req : option set_time) :
                             inode_state :=
      match sattr_req with
      | None => i
      | Some v =>
        let newtime := match v with
                       | SET_TO_CLIENT_TIME t => t
                       | SET_TO_SERVER_TIME => now
                       end in
        i <| inode_state_meta ::=
             fun m => m <| f := newtime |> <| inode_meta_ctime := now |> |>
      end.

    Definition truncate {A T} (i : inode_state) (now : time)
                              (sattr_req : option uint64)
                              (a : A)
                              (rx : inode_state -> relation State State (res A T)) :
                              relation State State (res A T) :=
      match sattr_req with
      | None => rx i
      | Some len =>
        match i.(inode_state_type) with
        | Ifile buf cverf =>
          (if (decide (len_buf buf < len)) then pure (Err a ERR_NOSPC) else none) +
          rx (i <| inode_state_type := Ifile (resize_buf len buf) cverf |>
                <| inode_state_meta ::= set inode_meta_mtime (constructor now) |>)
        | _ =>
          pure (Err a ERR_INVAL)
        end
      end.

    Definition put_fh_sync (f : fh) (i : inode_state) : relation State State unit :=
      puts (set fhs (fun x => <[f := sync i]> x)).

    Definition set_attr_nonlen (i : inode_state) (now : time) (a : sattr) : inode_state :=
      let i := set_attr_one i now (f := inode_meta_mode) a.(sattr_mode) in
      let i := set_attr_one i now (f := inode_meta_uid) a.(sattr_uid) in
      let i := set_attr_one i now (f := inode_meta_gid) a.(sattr_gid) in
      let i := set_attr_time i now (f := inode_meta_atime) a.(sattr_atime) in
      let i := set_attr_time i now (f := inode_meta_mtime) a.(sattr_mtime) in
      i.

    Definition setattr_step (f : fh) (a : sattr) (ctime_guard : option time) : relation State State (res wcc_data unit) :=
      i <~- get_fh f wcc_data_none;
      let wcc_before := inode_wcc i in
      _ <~- check_ctime_guard i ctime_guard (Build_wcc_data (Some wcc_before) (Some wcc_before));
      t <- get_time;
      i <~- truncate i t a.(sattr_size) (Build_wcc_data (Some wcc_before) (Some wcc_before));
      let i := set_attr_nonlen i t a in
      _ <- put_fh_sync f i;
      pure (OK (Build_wcc_data (Some wcc_before) (Some (inode_wcc i))) tt).

    Definition get_dir {A T} (i : inode_state) (a : A) (rx : gmap filename fh -> relation State State (res A T)) : relation State State (res A T) :=
      match i.(inode_state_type) with
      | Idir dmap => rx dmap
      | _ => pure (Err a ERR_NOTDIR)
      end.

    Definition lookup_step (a : dirop) : relation State State (res2 post_op_attr fh post_op_attr) :=
      d <~- get_fh a.(dirop_dir) None;
      dattr <- inode_attr a.(dirop_dir) d;
      dm <~- get_dir d (Some dattr);
      match dm !! a.(dirop_fn) with
      | None => pure (Err (Some dattr) ERR_NOENT)
      | Some ffh =>
        i <- reads (fun s => s.(fhs) !! ffh);
        match i with
        | None => pure (OK2 (Some dattr) ffh None)
        | Some i =>
          iattr <- inode_attr ffh (latest i);
          pure (OK2 (Some dattr) ffh (Some iattr))
        end
      end.

    Definition access_step (f : fh) (a : uint32) : relation State State (res post_op_attr uint32) :=
      i <~- get_fh f None;
      iattr <- inode_attr f i;
      pure (OK (Some iattr) a).

    Definition readlink_step (f : fh) : relation State State (res post_op_attr string) :=
      i <~- get_fh f None;
      iattr <- inode_attr f i;
      match i.(inode_state_type) with
      | Isymlink data => pure (OK (Some iattr) data)
      | _ => pure (Err (Some iattr) ERR_INVAL)
      end.

    (* XXX we are ignoring atime on read (and every other operation).
      if we do introduce atime, then we should make it async to avoid
      disk writes on every read. *)
    Definition read_step (f : fh) (off : uint64) (count : uint32) : relation State State (res2 post_op_attr bool buf) :=
      i <~- get_fh f None;
      iattr <- inode_attr f i;
      match i.(inode_state_type) with
      | Ifile buf _ =>
        let res := read_buf buf off count in
        let eof := if decide (off + count < len_buf buf) then false else true in
        pure (OK2 (Some iattr) eof res)
      | _ => pure (Err (Some iattr) ERR_INVAL)
      end.

    Definition put_fh_async (f : fh) (i : inode_state) : relation State State unit :=
      ia <- reads (fun s => s.(fhs) !! f);
      match ia with
      | None => pure tt
      | Some ia =>
        puts (set fhs (fun x => <[f := async_put i ia]> x))
      end.

    Definition write_step (f : fh) (off : uint64) (s : stable) (data : buf) : relation State State (res wcc_data write_ok) :=
      i <~- get_fh f wcc_data_none;
      let wcc_before := inode_wcc i in
      match i.(inode_state_type) with
      | Ifile buf cverf =>
        t <- get_time;
        wverf <- reads verf;
        let buf' := write_buf buf off data in
        (if (decide (len_buf buf < len_buf buf')) then pure (Err (Build_wcc_data (Some wcc_before) (Some wcc_before)) ERR_NOSPC) else none) +
        let i' := i <| inode_state_type := Ifile buf' cverf |>
                    <| inode_state_meta ::= set inode_meta_mtime (constructor t) |> in
        let wcc := Build_wcc_data (Some (inode_wcc i)) (Some (inode_wcc i')) in
        let wok := Build_write_ok (len_buf data) s wverf in
        match s with
        | UNSTABLE =>
          _ <- put_fh_async f i';
          pure (OK wcc wok)
        | _ =>
          _ <- put_fh_sync f i';
          pure (OK wcc wok)
        end
      | _ => pure (Err (Build_wcc_data (Some wcc_before) (Some wcc_before)) ERR_INVAL)
      end.

    Definition new_inode_meta : relation State State inode_meta :=
      now <- get_time;
      fid <- such_that (fun s fid => ~∃ f i, s.(fhs) !! f = Some i /\ i.(latest).(inode_state_meta).(inode_meta_fileid) = fid);
      pure (Build_inode_meta
        420 (* mode 0644 *)
        0 (* uid *)
        0 (* gid *)
        fid
        now
        now
        now).

    Definition dir_link (a : dirop) (dirmeta : inode_meta) (dm : gmap filename fh) (f : fh) : relation State State unit :=
      now <- get_time;
      let dirmeta := dirmeta <| inode_meta_mtime := now |> in
      let dm := <[a.(dirop_fn) := f]> dm in
      puts (set fhs (insert a.(dirop_dir) (sync (Build_inode_state dirmeta (Idir dm))))).

    Definition dir_unlink (a : dirop) (dirmeta : inode_meta) (dm : gmap filename fh) : relation State State unit :=
      now <- get_time;
      let dirmeta := dirmeta <| inode_meta_mtime := now |> in
      let dm := delete a.(dirop_fn) dm in
      puts (set fhs (insert a.(dirop_dir) (sync (Build_inode_state dirmeta (Idir dm))))).

    Definition create_unchecked_step (a : dirop) (attr : sattr) (dirmeta : inode_meta) (dm : gmap filename fh) : relation State State (res2 unit post_op_fh post_op_attr) :=
      f <- match dm !! a.(dirop_fn) with
           | Some curfh => pure curfh
           | None =>
             f <- such_that (fun s f => f ∉ dom (gset fh) s.(fhs));
             m <- new_inode_meta;
             _ <- puts (set fhs (insert f (sync (Build_inode_state m (Ifile empty_buf 0)))));
             _ <- dir_link a dirmeta dm f;
             pure f
           end;
      i <- reads (fun s => s.(fhs) !! f);
      match i with
      | None => pure (Err tt ERR_SERVERFAULT)
      | Some i =>
        now <- get_time;
        let i := i.(latest) in
        let i := match attr.(sattr_size) with
                 | None => i
                 | Some len =>
                   match i.(inode_state_type) with
                   | Ifile buf cverf =>
                     i <| inode_state_type := Ifile (resize_buf len buf) cverf |>
                       <| inode_state_meta ::= set inode_meta_mtime (constructor now) |>
                   | _ => i
                   end
                 end in
        let i := set_attr_nonlen i now attr in
        _ <- put_fh_sync f i;
        iattr <- inode_attr f i;
        pure (OK2 tt (Some f) (Some iattr))
      end.

    Definition create_guarded_step (a : dirop) (attr : sattr) (dirmeta : inode_meta) (dm : gmap filename fh) : relation State State (res2 unit post_op_fh post_op_attr) :=
      match dm !! a.(dirop_fn) with
      | Some curfh => pure (Err tt ERR_EXIST)
      | None =>
        f <- such_that (fun s f => f ∉ dom (gset fh) s.(fhs));
        m <- new_inode_meta;
        now <- get_time;
        let i := match attr.(sattr_size) with
                 | None => Build_inode_state m (Ifile empty_buf 0)
                 | Some len => Build_inode_state m (Ifile (resize_buf len empty_buf) 0)
                 end in
        let i := set_attr_nonlen i now attr in
        _ <- put_fh_sync f i;
        _ <- dir_link a dirmeta dm f;
        iattr <- inode_attr f i;
        pure (OK2 tt (Some f) (Some iattr))
      end.

    Definition create_exclusive_step (a : dirop) (cverf : createverf) (dirmeta : inode_meta) (dm : gmap filename fh) : relation State State (res2 unit post_op_fh post_op_attr) :=
      match dm !! a.(dirop_fn) with
      | Some curfh =>
        i <- reads (fun s => s.(fhs) !! curfh);
        match i with
        | None => pure (Err tt ERR_SERVERFAULT)
        | Some i => let i := i.(latest) in
          match i.(inode_state_type) with
          | Ifile _ v =>
            if (decide (v = cverf)) then
              iattr <- inode_attr curfh i;
              pure (OK2 tt (Some curfh) (Some iattr))
            else
              pure (Err tt ERR_EXIST)
          | _ =>
            pure (Err tt ERR_EXIST)
          end
        end
      | None =>
        f <- such_that (fun s f => f ∉ dom (gset fh) s.(fhs));
        m <- new_inode_meta;
        let i := Build_inode_state m (Ifile empty_buf cverf) in
        _ <- put_fh_sync f i;
        _ <- dir_link a dirmeta dm f;
        iattr <- inode_attr f i;
        pure (OK2 tt (Some f) (Some iattr))
      end.

    Definition create_like_core (a : dirop) (core : inode_meta -> gmap filename fh -> relation State State (res2 unit post_op_fh post_op_attr)) : relation State State (res2 wcc_data post_op_fh post_op_attr) :=
      d <~- get_fh a.(dirop_dir) wcc_data_none;

      let wcc_before := Some (inode_wcc d) in
      let wcc_ro := Build_wcc_data wcc_before wcc_before in
      pure (Err wcc_ro ERR_NOSPC) + (

      dm <~- get_dir d wcc_ro;
      r <- core d.(inode_state_meta) dm;

      d_after <- reads (fun s => s.(fhs) !! a.(dirop_dir));
      let wcc_after := match d_after with
                       | None => None
                       | Some d_after => Some (inode_wcc d_after.(latest))
                       end in
      let wcc := Build_wcc_data wcc_before wcc_after in

      pure (match r with
            | Err _ e => Err wcc e
            | OK _ v => OK wcc v
            end)).

    Definition create_step (a : dirop) (h : createhow) : relation State State (res2 wcc_data post_op_fh post_op_attr) :=
      create_like_core a
        (match h with
         | GUARDED attr => create_guarded_step a attr
         | UNCHECKED attr => create_unchecked_step a attr
         | EXCLUSIVE cv => create_exclusive_step a cv
         end).

    Definition mkdir_core (a : dirop) (attr : sattr) (dirmeta : inode_meta) (dm : gmap filename fh) : relation State State (res2 unit post_op_fh post_op_attr) :=
      match dm !! a.(dirop_fn) with
      | Some curfh => pure (Err tt ERR_EXIST)
      | None =>
        h <- such_that (fun s h => h ∉ dom (gset fh) s.(fhs));
        m <- new_inode_meta;
        now <- get_time;
        let dm := ∅ in
        let dm := <["." := h]> dm in
        let dm := <[".." := a.(dirop_dir)]> dm in
        let i := Build_inode_state m (Idir dm) in
        let i := set_attr_nonlen i now attr in
        _ <- put_fh_sync h i;
        _ <- dir_link a dirmeta dm h;
        iattr <- inode_attr h i;
        pure (OK2 tt (Some h) (Some iattr))
      end.

    Definition mkdir_step (a : dirop) (attr : sattr) : relation State State (res2 wcc_data post_op_fh post_op_attr) :=
      create_like_core a (mkdir_core a attr).

    Definition symlink_core (a : dirop) (attr : sattr) (data : filename) (dirmeta : inode_meta) (dm : gmap filename fh) : relation State State (res2 unit post_op_fh post_op_attr) :=
      match dm !! a.(dirop_fn) with
      | Some curfh => pure (Err tt ERR_EXIST)
      | None =>
        h <- such_that (fun s h => h ∉ dom (gset fh) s.(fhs));
        m <- new_inode_meta;
        now <- get_time;
        let i := Build_inode_state m (Isymlink data) in
        let i := set_attr_nonlen i now attr in
        _ <- put_fh_sync h i;
        _ <- dir_link a dirmeta dm h;
        iattr <- inode_attr h i;
        pure (OK2 tt (Some h) (Some iattr))
      end.

    Definition symlink_step (a : dirop) (attr : sattr) (data : filename) : relation State State (res2 wcc_data post_op_fh post_op_attr) :=
      create_like_core a (symlink_core a attr data).

    Definition mknod_core (a : dirop) (attr : sattr) (ft : mknod_type) (dirmeta : inode_meta) (dm : gmap filename fh) : relation State State (res2 unit post_op_fh post_op_attr) :=
      match dm !! a.(dirop_fn) with
      | Some curfh => pure (Err tt ERR_EXIST)
      | None =>
        h <- such_that (fun s h => h ∉ dom (gset fh) s.(fhs));
        m <- new_inode_meta;
        now <- get_time;
        let t := match ft with
                 | mknod_chr mm => Ichr mm
                 | mknod_blk mm => Iblk mm
                 | mknod_sock => Isock
                 | mknod_fifo => Ififo
                 end in
        let i := Build_inode_state m t in
        let i := set_attr_nonlen i now attr in
        _ <- put_fh_sync h i;
        _ <- dir_link a dirmeta dm h;
        iattr <- inode_attr h i;
        pure (OK2 tt (Some h) (Some iattr))
      end.

    Definition mknod_step (a : dirop) (ft : mknod_type) (attr : sattr) : relation State State (res2 wcc_data post_op_fh post_op_attr) :=
      create_like_core a (mknod_core a attr ft).

    Definition remove_like_core (a : dirop) (core : inode_meta -> gmap filename fh -> relation State State (res unit unit)) : relation State State (res wcc_data unit) :=
      d <~- get_fh a.(dirop_dir) wcc_data_none;

      let wcc_before := Some (inode_wcc d) in
      let wcc_ro := Build_wcc_data wcc_before wcc_before in

      dm <~- get_dir d wcc_ro;
      r <- core d.(inode_state_meta) dm;

      d_after <- reads (fun s => s.(fhs) !! a.(dirop_dir));
      let wcc_after := match d_after with
                       | None => None
                       | Some d_after => Some (inode_wcc d_after.(latest))
                       end in
      let wcc := Build_wcc_data wcc_before wcc_after in

      pure (match r with
            | Err _ e => Err wcc e
            | OK _ v => OK wcc v
            end).

    Definition gc_fh (h : fh) : relation State State unit :=
      nlink <- reads (fun s => add_up (fmap (count_links h) (fmap latest s.(fhs))));
      if (decide (nlink = 0)) then puts (set fhs (delete h)) else pure tt.

    Definition remove_core (a : dirop) (dirmeta : inode_meta) (dm : gmap filename fh) : relation State State (res unit unit) :=
      match dm !! a.(dirop_fn) with
      | None => pure (Err tt ERR_NOENT)
      | Some curfh =>
        i <- reads (fun s => s.(fhs) !! curfh);
        match i with
        | None => pure (Err tt ERR_SERVERFAULT)
        | Some i => let i := i.(latest) in
          match i.(inode_state_type) with
          | Idir _ => pure (Err tt ERR_INVAL) (* XXX oddly, not allowed in RFC1813?? *)
          | _ =>
            _ <- dir_unlink a dirmeta dm;
            _ <- gc_fh curfh;
            pure (OK tt tt)
          end
        end
      end.

    Definition remove_step (a : dirop) : relation State State (res wcc_data unit) :=
      remove_like_core a (remove_core a).

    Definition rmdir_core (a : dirop) (dirmeta : inode_meta) (dm : gmap filename fh) : relation State State (res unit unit) :=
      if (decide (a.(dirop_fn) = ".")) then pure (Err tt ERR_INVAL) else
      if (decide (a.(dirop_fn) = "..")) then pure (Err tt ERR_INVAL) else
      match dm !! a.(dirop_fn) with
      | None => pure (Err tt ERR_NOENT)
      | Some curfh =>
        i <- reads (fun s => s.(fhs) !! curfh);
        match i with
        | None => pure (Err tt ERR_SERVERFAULT)
        | Some i => let i := i.(latest) in
          match i.(inode_state_type) with
          | Idir m =>
            let names := dom (gset filename) m in
            if (decide (size names = 2)) then
              _ <- dir_unlink a dirmeta dm;
              _ <- gc_fh curfh;
              pure (OK tt tt)
            else
              pure (Err tt ERR_NOTEMPTY)
          | _ => pure (Err tt ERR_NOTDIR)
          end
        end
      end.

    Definition rmdir_step (a : dirop) : relation State State (res wcc_data unit) :=
      remove_like_core a (rmdir_core a).

    Definition rename_core (from to : dirop) (from_dirmeta to_dirmeta : inode_meta) (from_dm to_dm : gmap filename fh) : relation State State (res unit unit) :=
      pure (Err tt ERR_NOSPC) +
      if (decide (from.(dirop_fn) = ".")) then pure (Err tt ERR_INVAL) else
      if (decide (from.(dirop_fn) = "..")) then pure (Err tt ERR_INVAL) else
      if (decide (to.(dirop_fn) = ".")) then pure (Err tt ERR_INVAL) else
      if (decide (to.(dirop_fn) = "..")) then pure (Err tt ERR_INVAL) else
      match from_dm !! from.(dirop_fn) with
      | None => pure (Err tt ERR_NOENT)
      | Some src_h =>
        match to_dm !! to.(dirop_fn) with
        | None =>
          _ <- dir_link to to_dirmeta to_dm src_h;
          _ <- dir_unlink from from_dirmeta from_dm;
          pure (OK tt tt)
        | Some dst_h =>
          src_i <- reads (fun s => s.(fhs) !! src_h);
          dst_i <- reads (fun s => s.(fhs) !! dst_h);
          match src_i, dst_i with
          | Some src_i, Some dst_i =>
            let src_i := src_i.(latest) in
            let dst_i := dst_i.(latest) in

            match src_i.(inode_state_type), dst_i.(inode_state_type) with
            | Idir src_dm, Idir dst_dm =>
              let dst_names := dom (gset filename) dst_dm in
              if (decide (size dst_names = 2)) then
                _ <- dir_unlink to to_dirmeta to_dm;
                _ <- dir_unlink from from_dirmeta from_dm;
                _ <- dir_link to to_dirmeta to_dm src_h;
                _ <- gc_fh dst_h;
                pure (OK tt tt)
              else
                pure (Err tt ERR_EXIST)
            | Idir _, _ => pure (Err tt ERR_EXIST)
            | _, Idir _ => pure (Err tt ERR_EXIST)
            | _, _ =>
              _ <- dir_unlink to to_dirmeta to_dm;
              _ <- dir_unlink from from_dirmeta from_dm;
              _ <- dir_link to to_dirmeta to_dm src_h;
              _ <- gc_fh dst_h;
              pure (OK tt tt)
            end
          | _, _ => pure (Err tt ERR_SERVERFAULT)
          end
        end
      end.

    (* XXX rename allows a client to form loops in the directory structure,
      and to make it unreachable from the root. *)

    Definition rename_step (from to : dirop) : relation State State (res (wcc_data * wcc_data) unit) :=
      from_d <~- get_fh from.(dirop_dir) (wcc_data_none, wcc_data_none);
      to_d <~- get_fh to.(dirop_dir) (wcc_data_none, wcc_data_none);

      let wcc_from_before := Some (inode_wcc from_d) in
      let wcc_to_before := Some (inode_wcc to_d) in
      let wcc_ro := ( Build_wcc_data wcc_from_before wcc_from_before,
                      Build_wcc_data wcc_to_before wcc_to_before ) in

      from_dm <~- get_dir from_d wcc_ro;
      to_dm <~- get_dir to_d wcc_ro;

      r <- rename_core from to from_d.(inode_state_meta) to_d.(inode_state_meta) from_dm to_dm;

      from_d_after <- reads (fun s => s.(fhs) !! from.(dirop_dir));
      to_d_after <- reads (fun s => s.(fhs) !! to.(dirop_dir));
      let wcc_from_after := match from_d_after with
                            | None => None
                            | Some from_d_after => Some (inode_wcc from_d_after.(latest))
                            end in
      let wcc_to_after := match to_d_after with
                          | None => None
                          | Some to_d_after => Some (inode_wcc to_d_after.(latest))
                          end in
      let wcc := ( Build_wcc_data wcc_from_before wcc_from_after,
                   Build_wcc_data wcc_to_before wcc_to_after ) in

      pure (match r with
            | Err _ e => Err wcc e
            | OK _ v => OK wcc v
            end).

    Definition link_core (link : dirop) (h : fh) (i : inode_state) (dirmeta : inode_meta) (dm : gmap filename fh) : relation State State (res unit unit) :=
      pure (Err tt ERR_NOSPC) +
      match i.(inode_state_type) with
      | Idir _ => pure (Err tt ERR_INVAL)
      | _ =>
        match dm !! link.(dirop_fn) with
        | None =>
          _ <- dir_link link dirmeta dm h;
          pure (OK tt tt)
        | Some curfh =>
          pure (Err tt ERR_EXIST)
        end
      end.

    Definition link_step (h : fh) (link : dirop) : relation State State (res (wcc_data * post_op_attr) unit) :=
      i <~- get_fh h (wcc_data_none, None);
      d <~- get_fh link.(dirop_dir) (wcc_data_none, None);

      let wcc_before := Some (inode_wcc d) in
      let wcc_ro := (Build_wcc_data wcc_before wcc_before, None) in

      dm <~- get_dir d wcc_ro;
      r <- link_core link h i d.(inode_state_meta) dm;

      d_after <- reads (fun s => s.(fhs) !! link.(dirop_dir));
      let wcc_after := match d_after with
                       | None => None
                       | Some d_after => Some (inode_wcc d_after.(latest))
                       end in
      iattr_after <- inode_attr h i;
      let wcc := (Build_wcc_data wcc_before wcc_after, Some iattr_after) in

      pure (match r with
            | Err _ e => Err wcc e
            | OK _ v => OK wcc v
            end).

    Definition readdir_step (h : fh) (c : cookie) (cv : cookieverf) (count : uint32) : relation State State (res post_op_attr readdir_ok) :=
      pure (Err None ERR_NOTSUPP).

    Definition readdirplus_step (h : fh) (c : cookie) (cv : cookieverf) (dircount : uint32) (maxcount : uint32) : relation State State (res post_op_attr readdirplus_ok) :=
      pure (Err None ERR_NOTSUPP).

    Definition fsstat_step (h : fh) : relation State State (res post_op_attr fsstat_ok) :=
      i <~- get_fh h None;
      iattr <- inode_attr h i;
      st <- such_that (fun _ st =>
        st.(fsstat_ok_fbytes) <= st.(fsstat_ok_tbytes) /\
        st.(fsstat_ok_abytes) <= st.(fsstat_ok_fbytes) /\
        st.(fsstat_ok_ffiles) <= st.(fsstat_ok_tfiles) /\
        st.(fsstat_ok_afiles) <= st.(fsstat_ok_ffiles));
      pure (OK (Some iattr) st).

    Definition fsinfo_step (h : fh) : relation State State (res post_op_attr fsinfo_ok) :=
      i <~- get_fh h None;
      iattr <- inode_attr h i;
      info <- such_that (fun _ info =>
        info.(fsinfo_ok_time_delta) = Build_time 0 1 /\
        info.(fsinfo_ok_properties_link) = true /\
        info.(fsinfo_ok_properties_symlink) = true /\
        info.(fsinfo_ok_properties_homogeneous) = true /\
        info.(fsinfo_ok_properties_cansettime) = true);
      pure (OK (Some iattr) info).

    Definition pathconf_step (h : fh) : relation State State (res post_op_attr pathconf_ok) :=
      i <~- get_fh h None;
      iattr <- inode_attr h i;
      pc <- such_that (fun _ pc =>
        pc.(pathconf_ok_no_trunc) = true /\
        pc.(pathconf_ok_case_insensitive) = false /\
        pc.(pathconf_ok_case_preserving) = true);
      pure (OK (Some iattr) pc).

    Definition commit_step (h : fh) (off : uint64) (count : uint32) : relation State State (res wcc_data writeverf) :=
      i <~- get_fh h wcc_data_none;
      let wcc_before := inode_wcc i in
      let wcc := Build_wcc_data (Some wcc_before) (Some wcc_before) in
      wverf <- reads verf;
      match i.(inode_state_type) with
      | Ifile buf cverf =>
        _ <- put_fh_sync h i;
        pure (OK wcc wverf)
      | _ => pure (OK wcc wverf)
      end.

  Definition nfs_crash_step : relation State State unit :=
    s' <- such_that (fun (s s' : State) =>
      forall fh, inode_crash_opt (s.(fhs) !! fh) (s'.(fhs) !! fh) /\
      s'.(verf) > s.(verf) /\
      time_ge s.(clock) s'.(clock));
    _ <- puts (fun _ => s');
    pure tt.

  Definition nfs_finish_step : relation State State unit :=
    _ <- puts (fun s =>
      let s := s <| fhs ::= fmap inode_finish |> in
      let s := s <| verf ::= fun x => plus x 1 |> in
      s);
    pure tt.

  Definition nfs3step : OpSemantics Op State :=
    fun T (op : Op T) =>
          match op with
          | NULL => null_step
          | GETATTR h => getattr_step h
          | SETATTR h attr ctime_guard => setattr_step h attr ctime_guard
          | LOOKUP a => lookup_step a
          | ACCESS h a => access_step h a
          | READLINK h => readlink_step h
          | READ h off count => read_step h off count
          | WRITE h off stab data => write_step h off stab data
          | CREATE a how => create_step a how
          | MKDIR a attr => mkdir_step a attr
          | SYMLINK a attr name => symlink_step a attr name
          | MKNOD a ft attr => mknod_step a ft attr
          | REMOVE a => remove_step a
          | RMDIR a => rmdir_step a
          | RENAME from to => rename_step from to
          | LINK h link => link_step h link
          | READDIR h c cverf count => readdir_step h c cverf count
          | READDIRPLUS h c cverf dircount maxcount => readdirplus_step h c cverf dircount maxcount
          | FSSTAT h => fsstat_step h
          | FSINFO h => fsinfo_step h
          | PATHCONF h => pathconf_step h
          | COMMIT h off count => commit_step h off count
          end.

  Definition dynamics : Dynamics Op State :=
    {| step := nfs3step;
       crash_step := nfs_crash_step;
       finish_step := nfs_finish_step;
    |}.

(*
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
*)

End NFS3.
