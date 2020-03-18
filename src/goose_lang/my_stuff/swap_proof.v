From Perennial.goose_lang.my_stuff Require Import swap.
From Perennial.goose_lang.lib Require Import encoding.
From Perennial.program_proof Require Import proof_prelude.
(* From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import marshal_proof. *)

Section heap.
Context `{!heapG Σ}.
Context `{!crashG Σ}.
Implicit Types v : val.
Implicit Types z : Z.
Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Local Opaque struct_mapsto load_ty store_ty.
