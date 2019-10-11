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

  Axiom read_ok : forall s E txn a v hT,
    (
      (
        txn_valid txn hT ∗
        a ↦[hT] v
      )
      -∗
      WP ImplAlloc.read txn a @ s; E {{
        v,
        txn_valid txn hT ∗
        a ↦[hT] v
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

