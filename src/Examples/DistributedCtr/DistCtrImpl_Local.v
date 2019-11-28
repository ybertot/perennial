From iris.algebra Require Import auth frac_auth excl.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode notation lib.par lib.spin_lock.
Require Import DistributedCtr.Helpers.

(* LOCAL NODE-BASED FUNCTIONS *)
Definition alloc_node: val := λ: "()",
  let: "node" := ref (SOME #0) in
  let: "lk" := newlock #() in
  Pair "node" "lk".

Definition update_node: val := 
  λ: "node",
  match: !"node" with
    SOME "v1" => "node" <- SOME ("v1" + #1);;
                        #1
  | NONE => #0
  end.

Definition kill_node: val :=
  λ: "node",
  "node" <- NONE.

Section proof.
  Context `{!heapG Σ, !spawnG Σ, !lockG Σ, !inG Σ (authR (optionUR (exclR ZO)))}.

  Definition node_val_inv (n : Z) (optv: option Z) (γ : gname): iProp Σ := 
      ⌜ optv = Some n ∨ optv = None ⌝ ∗ own γ (◯ (Excl' n)).

  Definition node_lock_inv (γ: gname) : iProp Σ :=
    (∃ n, own γ (● (Excl' n)))%I.

  Lemma alloc_node_spec : 
    {{{ True%I }}}
      alloc_node #()
      {{{ r1 lk γ γ1 , RET PairV r1 lk;
          is_lock LockN γ lk (node_lock_inv γ1) ∗
          node_val_inv 0 (Some 0) γ1
    }}}.
  Proof.
    iIntros (Φ) "_ HPost".
    iMod (ghost_var_alloc 0) as (γ1) "[Hγ1● Hγ1◯]".

    unfold alloc_node.
    wp_alloc master as "Hr1".
    wp_let.
 
    wp_apply (newlock_spec LockN (node_lock_inv γ1) with "[- Hγ1◯ Hr1 HPost]").
    iExists 0; auto.
    iIntros (lk γ) "HIsLk".
    wp_let.
    wp_pures.
    iApply "HPost". 
    iFrame; auto.
  Qed.

  Lemma update_node_some_spec : ∀ (n: Z) γ1 node,
      {{{
           node ↦ SOMEV #n
           ∗ node_lock_inv γ1
           ∗ node_val_inv n (Some n) γ1
    }}}
      update_node #node
    {{{ RET #1;
          node ↦ SOMEV #(n+1)
          ∗ node_lock_inv γ1
          ∗ node_val_inv (n+1) (Some (n+1)) γ1
    }}}.
  Proof.
    iIntros (n γ1 node Φ) "(Hnode & Hlkinv & Hnodeinv & Hown) HPost".
    unfold update_node.
    unfold node_lock_inv.
    iDestruct "Hlkinv" as (n') "Hlkinv".
    iMod (ghost_var_update γ1 (n+1) with "Hlkinv Hown") as "[Hγ1● Hγ1◯]".
    wp_pures.
    wp_load.
    wp_pures.
    wp_store.
    iApply "HPost". 
    iFrame; auto.
  Qed.

  Lemma update_node_none_spec : ∀ (n: Z) γ1 node,
      {{{
           node ↦ NONEV
           ∗ node_lock_inv γ1
           ∗ node_val_inv n None γ1
    }}}
      update_node #node
    {{{ RET #0;
          node ↦ NONEV
          ∗ node_lock_inv γ1
          ∗ (∃ n, node_val_inv n None γ1)
    }}}.
  Proof.
    iIntros (n γ1 node Φ) "(Hnode & Hlkinv & Hnodeinv & Hown) HPost".
    unfold update_node.
    unfold node_lock_inv.
    iDestruct "Hlkinv" as (n') "Hlkinv".
    wp_pures.
    wp_load.
    wp_pures.
    iApply "HPost".
    iSplitL "Hnode"; auto.
    iSplitL "Hlkinv". iExists n'; auto.
    unfold node_val_inv. iExists n. iSplit; auto. 
  Qed.
End proof.
