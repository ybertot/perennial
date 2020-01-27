(* autogenerated from mailboat *)
From Perennial.go_lang Require Import prelude.

(* disk FFI *)
From Perennial.go_lang Require Import ffi.disk_prelude.

Module partialFile.
  Definition S := struct.decl [
    "off" :: uint64T;
    "data" :: slice.T byteT
  ].
End partialFile.

Definition GetUserDir: val :=
  λ: "user",
    #(str"user") + uint64_to_string "user".

Definition SpoolDir : expr := #(str"spool").

Definition NumUsers : expr := #100.

Definition readMessage: val :=
  λ: "userDir" "name",
    let: "f" := FS.open "userDir" "name" in
    let: "fileContents" := ref (zero_val (slice.T byteT)) in
    let: "initData" := NewSlice byteT #0 in
    let: "pf" := ref (struct.mk partialFile.S [
      "off" ::= #0;
      "data" ::= "initData"
    ]) in
    (for: (#true); (Skip) :=
      let: "buf" := FS.readAt "f" (struct.get partialFile.S "off" (![struct.t partialFile.S] "pf")) #512 in
      let: "newData" := SliceAppendSlice byteT (struct.get partialFile.S "data" (![struct.t partialFile.S] "pf")) "buf" in
      (if: slice.len "buf" < #512
      then
        "fileContents" <-[refT (slice.T byteT)] "newData";;
        Break
      else
        "pf" <-[struct.t partialFile.S] struct.mk partialFile.S [
          "off" ::= struct.get partialFile.S "off" (![struct.t partialFile.S] "pf") + slice.len "buf";
          "data" ::= "newData"
        ];;
        Continue));;
    let: "fileData" := ![slice.T byteT] "fileContents" in
    let: "fileStr" := Data.bytesToString "fileData" in
    FS.close "f";;
    "fileStr".

Module Message.
  Definition S := struct.decl [
    "Id" :: stringT;
    "Contents" :: stringT
  ].
End Message.

(* Pickup reads all stored messages and acquires a per-user lock. *)
Definition Pickup: val :=
  λ: "user",
    let: "ls" := Globals.getX #() in
    let: "l" := SliceGet lockRefT "ls" "user" in
    lock.acquire "l";;
    let: "userDir" := GetUserDir "user" in
    let: "names" := FS.list "userDir" in
    let: "messages" := ref (zero_val (slice.T (struct.t Message.S))) in
    let: "initMessages" := NewSlice (struct.t Message.S) #0 in
    "messages" <-[refT (slice.T (struct.t Message.S))] "initMessages";;
    let: "i" := ref #0 in
    (for: (#true); (Skip) :=
      (if: (![uint64T] "i" = slice.len "names")
      then Break
      else
        let: "name" := SliceGet stringT "names" (![uint64T] "i") in
        let: "msg" := readMessage "userDir" "name" in
        let: "oldMessages" := ![slice.T (struct.t Message.S)] "messages" in
        let: "newMessages" := SliceAppend (struct.t Message.S) "oldMessages" (struct.mk Message.S [
          "Id" ::= "name";
          "Contents" ::= "msg"
        ]) in
        "messages" <-[refT (slice.T (struct.t Message.S))] "newMessages";;
        "i" <-[uint64T] ![uint64T] "i" + #1;;
        Continue));;
    let: "msgs" := ![slice.T (struct.t Message.S)] "messages" in
    "msgs".

Definition createTmp: val :=
  λ: <>,
    let: "initID" := Data.randomUint64 #() in
    let: "finalFile" := ref (zero_val fileT) in
    let: "finalName" := ref (zero_val stringT) in
    let: "id" := ref "initID" in
    (for: (#true); (Skip) :=
      let: "fname" := uint64_to_string (![uint64T] "id") in
      let: ("f", "ok") := FS.create SpoolDir "fname" in
      (if: "ok"
      then
        "finalFile" <-[refT fileT] "f";;
        "finalName" <-[refT stringT] "fname";;
        Break
      else
        let: "newID" := Data.randomUint64 #() in
        "id" <-[uint64T] "newID";;
        Continue);;
      Continue);;
    let: "f" := ![fileT] "finalFile" in
    let: "name" := ![stringT] "finalName" in
    ("f", "name").

Definition writeTmp: val :=
  λ: "data",
    let: ("f", "name") := createTmp #() in
    let: "buf" := ref "data" in
    (for: (#true); (Skip) :=
      (if: slice.len (![slice.T byteT] "buf") < #4096
      then
        FS.append "f" (![slice.T byteT] "buf");;
        Break
      else
        FS.append "f" (SliceTake (![slice.T byteT] "buf") #4096);;
        "buf" <-[slice.T byteT] SliceSkip byteT (![slice.T byteT] "buf") #4096;;
        Continue));;
    FS.close "f";;
    "name".

(* Deliver stores a new message.
   Does not require holding the per-user pickup/delete lock. *)
Definition Deliver: val :=
  λ: "user" "msg",
    let: "userDir" := GetUserDir "user" in
    let: "tmpName" := writeTmp "msg" in
    let: "initID" := Data.randomUint64 #() in
    let: "id" := ref "initID" in
    (for: (#true); (Skip) :=
      let: "ok" := FS.link SpoolDir "tmpName" "userDir" (#(str"msg") + uint64_to_string (![uint64T] "id")) in
      (if: "ok"
      then Break
      else
        let: "newID" := Data.randomUint64 #() in
        "id" <-[uint64T] "newID";;
        Continue);;
      Continue);;
    FS.delete SpoolDir "tmpName".

(* Delete deletes a message for the current user.
   Requires the per-user lock, acquired with pickup. *)
Definition Delete: val :=
  λ: "user" "msgID",
    let: "userDir" := GetUserDir "user" in
    FS.delete "userDir" "msgID".

(* Lock acquires the lock for the current user *)
Definition Lock: val :=
  λ: "user",
    let: "locks" := Globals.getX #() in
    let: "l" := SliceGet lockRefT "locks" "user" in
    lock.acquire "l".

(* Unlock releases the lock for the current user. *)
Definition Unlock: val :=
  λ: "user",
    let: "locks" := Globals.getX #() in
    let: "l" := SliceGet lockRefT "locks" "user" in
    lock.release "l".

Definition open: val :=
  λ: <>,
    let: "locks" := ref (zero_val (slice.T lockRefT)) in
    let: "initLocks" := NewSlice lockRefT #0 in
    "locks" <-[refT (slice.T lockRefT)] "initLocks";;
    let: "i" := ref #0 in
    (for: (#true); (Skip) :=
      (if: (![uint64T] "i" = NumUsers)
      then Break
      else
        let: "oldLocks" := ![slice.T lockRefT] "locks" in
        let: "l" := lock.new #() in
        let: "newLocks" := SliceAppend lockRefT "oldLocks" "l" in
        "locks" <-[refT (slice.T lockRefT)] "newLocks";;
        "i" <-[uint64T] ![uint64T] "i" + #1;;
        Continue));;
    let: "finalLocks" := ![slice.T lockRefT] "locks" in
    Globals.setX "finalLocks".

Definition init: val :=
  λ: <>,
    open #().

Definition Recover: val :=
  λ: <>,
    let: "spooled" := FS.list SpoolDir in
    let: "i" := ref #0 in
    (for: (#true); (Skip) :=
      (if: (![uint64T] "i" = slice.len "spooled")
      then Break
      else
        let: "name" := SliceGet stringT "spooled" (![uint64T] "i") in
        FS.delete SpoolDir "name";;
        "i" <-[uint64T] ![uint64T] "i" + #1;;
        Continue)).
