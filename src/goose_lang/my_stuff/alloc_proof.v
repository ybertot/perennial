From Goose.github_com.mit_pdos.goose_nfsd Require Import alloc.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_lib.

Section proof.
Context `{!heapG Σ}.

Local Opaque struct_mapsto load_ty store_ty.

(* Let's define what a valid allocator even looks like. *)

Definition alloc_fields (l:loc) (next:u64) (bitmap:Slice.t): iProp Σ :=
  l ↦[Alloc.S :: "next"] #next ∗
  l ↦[Alloc.S :: "bitmap"] slice_val bitmap. (* casts Slice.t to a val (see slice.v) *)

(* increment x mod n *)
Definition mod_inc (x n: u64) : u64 :=
  if (ge_dec (int.nat x + 1) (int.nat n)) then 0 else word.add x 1.

Theorem incNext_spec stk E l next bitmap :
  {{{ alloc_fields l next bitmap }}}
    Alloc__incNext #l @stk; E
  {{{ RET #(mod_inc next (8*int.nat bitmap.(Slice.sz)));
        alloc_fields l (mod_inc next (8*int.nat bitmap.(Slice.sz))) bitmap }}}.

Proof.
  iIntros (Φ) "Halloc HΦ".
  wp_call.
  unfold alloc_fields in *.
  iDestruct "Halloc" as "[H1 H2]".
  wp_loadField. (* needed to split Halloc to make this work *)
  wp_storeField.
  wp_loadField.

  wp_rec. (* this actually did something tiny *)

  wp_loadField. (* why does this work now? *)

  wp_pures.
  wp_bind (If _ _ _).
  wp_if_destruct.
  (* this may be easier if we define mod_inc to fit the structure better. *)
  - wp_storeField. wp_seq. wp_loadField. unfold mod_inc in *.
    destruct (ge_dec (int.nat next + 1) (int.nat (8 * int.nat bitmap.(Slice.sz)))) eqn:Hinc2.
    + iApply "HΦ". iFrame.
    + admit.
  - wp_seq. wp_loadField. unfold mod_inc in *.
    destruct (ge_dec (int.nat next + 1) (int.nat (8 * int.nat bitmap.(Slice.sz)))) eqn:Hinc2.
    + admit. (* contradiction here *)
    + iApply "HΦ". iFrame.
Admitted.

End proof.
