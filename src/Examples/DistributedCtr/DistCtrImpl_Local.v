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
  λ: "node" "lk",
  acquire "lk";;
  let: "r" := ref #0 in
  match: !"node" with
    SOME "v1" => "node" <- SOME ("v1" + #1);;
                        "r" <- #0
  | NONE => "r" <- #(-1)
  end;;
  release "lk";;
  !"r".

Definition get_node_val: val :=
  λ: "node" "lk",
  acquire "lk";;
  let: "r" := ref #0 in
  match: !"node" with
    SOME "v1" => !"r" <- Pair "v1" #1
  | NONE => !"r" <- Pair #0 #0
  end;;
  release "lk";;
  !"r".

Definition kill_node: val :=
  λ: "node",
  "node" <- NONE.

Section proof.
  Context `{!heapG Σ, !spawnG Σ, !lockG Σ, !inG Σ (authR (optionUR (exclR ZO)))}.

  Definition node_own_inv (node: loc) (n : Z) (γ : gname): iProp Σ :=
    own γ (◯ (Excl' n))%I.

  Definition node_lock_inv (node: loc) (isDead: Prop) (γ: gname) : iProp Σ :=
    (∃ n, own γ (● (Excl' n))
    ∗ ((⌜isDead⌝ ∧ node ↦ NONEV) ∨ (⌜~isDead⌝ ∧ node ↦ SOMEV #n)))%I.

  Lemma alloc_node_spec : 
    {{{ True%I }}}
      alloc_node #()
      {{{ node lk γ γ1, RET PairV #node lk;
          is_lock LockN γ lk (node_lock_inv node false γ1)
    }}}.
  Proof.
    iIntros (Φ) "_ HPost".
    iMod (ghost_var_alloc 0) as (γ1) "[Hγ1● Hγ1◯]".

    unfold alloc_node.
    wp_alloc node as "Hr1".
    wp_let.
 
    wp_apply (newlock_spec LockN (node_lock_inv node false γ1) with "[- Hγ1◯ HPost]").
    iExists 0. iFrame. iRight;auto.
    iIntros (lk γ) "HIsLk".
    wp_let.
    wp_pures.
    iApply "HPost".
    iFrame; auto.
  Qed.

  Lemma update_node_some_spec : ∀ (n: Z) γ1 node lk,
      {{{
          is_lock LockN γ1 lk (node_lock_inv node false γ1)
          ∗ node_own_inv node n γ1
    }}}
      update_node #node lk
    {{{ RET #0;
          is_lock LockN γ1 lk (node_lock_inv node false γ1)
          ∗ node_own_inv node (n+1) γ1
    }}}.
  Proof.
    iIntros (n γ1 node lk Φ) "(#Hlkinv & Hγ1◯) HPost".
    unfold node_lock_inv.
    unfold node_own_inv.
    unfold update_node.
    wp_pures.

    wp_apply (acquire_spec with "Hlkinv").
    wp_pures.
    iIntros "(Hlked & Hinv)".
    iDestruct "Hinv" as (n') "(Hγ1● & [[H Halive] | [H Halive]])";
    wp_pures;
    iDestruct "H" as %H. inversion H; subst.
    iDestruct (ghost_var_agree with "Hγ1● Hγ1◯") as %->.
    iMod (ghost_var_update γ1 (n+1) with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]".
    wp_alloc r as "Hr".
    wp_let.
    wp_load.
    wp_pures.
    wp_store.
    wp_store.
    wp_apply (release_spec LockN γ1 lk (node_lock_inv node false γ1) with "[Hlkinv Hlked Hγ1● Halive]"); iFrame; auto.
    iSplit; auto.
    unfold node_lock_inv.
    iExists (n+1). iFrame; auto.

    iIntros. wp_pures. wp_load.
    iApply "HPost".
    iFrame; auto.
  Qed.

  Lemma update_node_none_spec : ∀ (n: Z) γ1 node lk,
      {{{
          is_lock LockN γ1 lk (node_lock_inv node true γ1)
          ∗ node_own_inv node n γ1
    }}}
      update_node #node lk
    {{{ RET #(-1);
          is_lock LockN γ1 lk (node_lock_inv node true γ1)
          ∗ node_own_inv node (n) γ1
    }}}.
  Proof.
    iIntros (n γ1 node lk Φ) "(#Hlkinv & Hγ1◯) HPost".
    unfold node_lock_inv.
    unfold node_own_inv.
    unfold update_node.
    wp_pures.

    wp_apply (acquire_spec with "Hlkinv").
    wp_pures.
    iIntros "(Hlked & Hinv)".
    iDestruct "Hinv" as (n') "(Hγ1● & [[H Halive] | [H Halive]])";
    wp_pures;
    iDestruct "H" as %H; destruct H; auto.
    iDestruct (ghost_var_agree with "Hγ1● Hγ1◯") as %->.
    wp_alloc r as "Hr".
    wp_let.
    wp_load.
    wp_pures.
    wp_store.
    wp_apply (release_spec LockN γ1 lk (node_lock_inv node true γ1) with "[Hlkinv Hlked Hγ1● Halive]"); iFrame; auto.
    iIntros. wp_pures. wp_load.
    iApply "HPost".
    iFrame; auto.
  Qed.
End proof.
