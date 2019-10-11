From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement CSL.NamedDestruct.
Require Import AllocAPI ImplAlloc ExMach.WeakestPre ExMach.RefinementAdequacy.
Require Import Logging2.Helpers.
Require Import Equality.
Set Default Proof Using "All".
Unset Implicit Arguments.

From Tactical Require Import UnfoldLemma.


Section refinement_triples.
  Context `{!exmachG Σ, lockG Σ, !@cfgG (Alloc.Op) (Alloc.l) Σ,
            !inG Σ (authR (optionUR (exclR (listO natO)))),
            !inG Σ (authR (optionUR (exclR natO)))}.

  Import ExMach.

  Context {hTxn: gen_heapG nat (option (gmap nat nat)) Σ}.
  Notation "l t↦ v " := (mapsto (hG := hTxn) l 1 v)
    (at level 20, format "l  t↦  v") : bi_scope.


  Definition txn_valid (txn : nat) (tmap : gmap nat nat) :=
    (
      txn t↦ (Some tmap) ∗
      [∗ map] a ↦ v ∈ tmap, ∃ v0, a m↦ v0
    )%I.

  Axiom begin_ok : forall s E,
    (
      WP ImplAlloc.begin @ s; E {{
        txn,
        txn_valid txn ∅
      }}
    )%I.

  Axiom lift_ok : forall txn m liftm,
    (
      ( txn_valid txn m ∗
        [∗ map] a ↦ v ∈ liftm, a m↦ v
      ) -∗
      txn_valid txn (m ∪ liftm)
    )%I.

  Axiom write_ok : forall s E txn a v m,
    (
      ( txn_valid txn m ∗
        ⌜ is_Some (m !! a) ⌝ )
      -∗
      WP ImplAlloc.write txn a v @ s; E {{
        tt,
        txn_valid txn (<[a:=v]> m)
      }}
    )%I.

  Axiom read_ok : forall s E txn a v m,
    (
      ( txn_valid txn m ∗
        ⌜ m !! a = v ⌝ )
      -∗
      WP ImplAlloc.read txn a @ s; E {{
        v,
        txn_valid txn m
      }}
    )%I.

  Axiom commit_ok : forall s E txn m,
    (
      txn_valid txn m
      -∗
      WP ImplAlloc.commit txn @ s; E {{
        r,
        [∗ map] a ↦ v ∈ m, a m↦ v
      }}
    )%I.

