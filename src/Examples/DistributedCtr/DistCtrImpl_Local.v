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
  Definition nodeN : namespace := nroot .@ "node".

  Definition node_val_prop (node: loc) (isDead: Prop) (γ : gname): iProp Σ :=
    ∃ (n: Z), ((⌜isDead⌝ ∧ node ↦ NONEV) ∨ (⌜~isDead⌝ ∧ node ↦ SOMEV #n))%I.

  Definition node_own_inv (node: loc) (n : Z) (γ : gname): iProp Σ :=
    own γ (◯ (Excl' n))%I.

  Definition node_val_inv (node: loc) (isDead: Prop) (γ : gname): iProp Σ :=
    inv nodeN (node_val_prop node isDead γ)%I.

  Definition node_lock_inv (γ: gname) : iProp Σ :=
    (∃ n, own γ (● (Excl' n)))%I.

  Lemma alloc_node_spec : 
    {{{ True%I }}}
      alloc_node #()
      {{{ r1 lk γ γ1, RET PairV #r1 lk;
          is_lock LockN γ lk (node_lock_inv γ1)
          ∗ node_val_inv r1 false γ1
          ∗ node_own_inv r1 0 γ1
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
    iMod (inv_alloc nodeN _ (node_val_prop master false γ1) with "[Hr1]") as "#Hinv".
    { unfold node_val_prop. iNext. iExists 0. iRight; iSplit; auto. }

    wp_pures.
    iApply "HPost".
    iFrame; auto.
  Qed.

  Lemma update_node_some_spec : ∀ (n: Z) γ1 node,
      {{{
           node_lock_inv γ1
          ∗ node_val_inv node false γ1
          ∗ node_own_inv node n γ1
    }}}
      update_node #node
    {{{ RET #1;
          node_lock_inv γ1
          ∗ node_val_inv node false γ1
          ∗ node_own_inv node (n+1) γ1
    }}}.
  Proof.
    iIntros (n γ1 node Φ) "(Hlkinv & #Hnodeinv & Hγ1◯) HPost".
    unfold node_val_inv.
    unfold node_val_prop.
    unfold update_node.
    unfold node_lock_inv.
    unfold node_own_inv.
    wp_pures.

    wp_bind ( ! #node )%E.
    iInv "Hnodeinv" as ">Hinv".
    iDestruct "Hinv" as (n') "[[H Halive] | [H Halive]]";
    wp_load;
    iDestruct "H" as %H. inversion H.
    iModIntro.
    iSplitL "Halive".
    { iNext. unfold node_val_prop. iExists n'. iRight. iSplitR "Halive"; auto. }

    wp_pures.
    wp_bind ( #node <- _ )%E.
    iInv "Hnodeinv" as ">Hinv".
    iDestruct "Hinv" as (n0) "[[H Halive] | [H Halive]]";
    iDestruct "H" as %H'. inversion H'.
    wp_store.
    iModIntro.

    iSplitL "Halive".
    iNext.
    iExists (n'+1).
    iRight; auto.

    iDestruct "Hlkinv" as (n1) "Hγ1●".
    iMod (ghost_var_update γ1 (n+1) with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]".
    wp_pures.
    iApply "HPost".
    iSplitL "Hγ1●".
    iExists (n+1); auto.
    iFrame; auto.
  Qed.

  Lemma update_node_none_spec : ∀ (n: Z) γ1 node,
      {{{
           node_lock_inv γ1
          ∗ node_val_inv node true γ1
          ∗ node_own_inv node n γ1
    }}}
      update_node #node
    {{{ RET #0;
        node_lock_inv γ1
        ∗ node_val_inv node true γ1
        ∗ ∃ n, node_own_inv node n γ1
    }}}.
  Proof.
    iIntros (n γ1 node Φ) "(Hlkinv & #Hnodeinv & Hγ1◯) HPost".
    unfold node_val_inv.
    unfold node_val_prop.
    unfold update_node.
    unfold node_lock_inv.
    unfold node_own_inv.
    wp_pures.

    wp_bind ( ! #node )%E.
    iInv "Hnodeinv" as ">Hinv".
    iDestruct "Hinv" as (n') "[[H Halive] | [H Halive]]";
    wp_load;
    iDestruct "H" as %H; unfold not in H; simpl in H; try contradiction.
    iModIntro.
    iSplitL "Halive".
    { iNext. unfold node_val_prop. iExists n'. iLeft. iSplitR "Halive"; auto. }

    wp_pures.
    iApply "HPost".
    iDestruct "Hlkinv" as (n1) "Hγ1●".
    iSplitL "Hγ1●".
    iExists (n1); auto.
    iFrame; auto.
  Qed.
End proof.
