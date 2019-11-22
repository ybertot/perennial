From iris.algebra Require Import auth frac_auth excl.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode notation lib.par lib.spin_lock.

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
  | NONE => "node" <- SOME #0;;
                   #0
  end.

Definition kill_node: val :=
  λ: "node",
  "node" <- NONE.

(* GLOBAL, CLIENT-FACING FUNCTIONS *)
Definition alloc_replicas : val := λ: "()",
  let: "master" := alloc_node #() in
  let: "backup" := alloc_node #() in
  Pair "master" "backup".

Definition get_replicas : val :=
  λ: "node1" "node2",
  match: !"node1" with
    SOME "v1" => "node2" <- "v1";;
                         "v1"
    | NONE => match: !"node2" with
                SOME "v2" => "node1" <- "v2";;
                               "v2"
              | NONE => "node1" <- SOME #0;;
                                "node2" <- SOME #0;;
                                #-1
              end
  end;;
  "r".
 
Definition update_replicas: val :=
  λ: "node1" "node2" "lk1" "lk2",
  acquire "lk1";;
  acquire "lk2";;
  let: "s1" := update_node "node1" in
  let: "s2" := update_node "node2" in
  if: "s1" = #0 then get_replicas "node1" "node2" else #();;
  release "lk2";;
  release "lk1".

Section proof.
  Context `{!heapG Σ, !spawnG Σ, !lockG Σ, !inG Σ (authR (optionUR (exclR ZO)))}.
  Definition LockN : namespace := nroot .@ "LockN".

  Lemma ghost_var_alloc n :
    (|==> ∃ γ, own γ (● (Excl' n)) ∗ own γ (◯ (Excl' n)))%I.
  Proof.
    iMod (own_alloc (● (Excl' n) ⋅ ◯ (Excl' n))) as (γ) "[??]".
    - by apply auth_both_valid.
    - by eauto with iFrame.
  Qed.

  Lemma ghost_var_agree γ n m :
    own γ (● (Excl' n)) -∗ own γ (◯ (Excl' m)) -∗ ⌜ n = m ⌝. Proof. iIntros "Hγ● Hγ◯".
    Check own_valid_2.
    by iDestruct (own_valid_2 with "Hγ● Hγ◯")
      as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid.
  Qed.

  Lemma ghost_var_update γ n' n m :
    own γ (● (Excl' n)) -∗ own γ (◯ (Excl' m)) ==∗
      own γ (● (Excl' n')) ∗ own γ (◯ (Excl' n')).
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (● Excl' n' ⋅ ◯ Excl' n') with "Hγ● Hγ◯") as "[$$]".
    { apply auth_update. apply option_local_update. apply exclusive_local_update. done. }
    done.
  Qed.

  Definition node_val_inv (n : Z) (optv: option Z) (γ : gname): iProp Σ := 
      ⌜ optv = Some n ∨ optv = None ⌝ ∗ own γ (◯ (Excl' n)).

  Definition node_lock_inv (n: Z) (γ: gname) : iProp Σ :=
      own γ (● (Excl' n))%I.

  Definition global_inv (n : Z) (optv1 optv2: option Z) (γ1 γ2 : gname): iProp Σ :=
    (node_val_inv n optv1 γ1) ∗ (node_val_inv n optv2 γ2).
  (* Notes: loc = kind of like a Coq literal number, LitV (LitLoc loc) is an actual value in the language *)

  Lemma alloc_node_spec : 
    {{{ True%I }}}
      alloc_node #()
      {{{ r1 lk γ γ1 , RET PairV r1 lk;
          is_lock LockN γ lk (node_lock_inv 0 γ1) ∗
          node_val_inv 0 (Some 0) γ1
    }}}.
  Proof.
    iIntros (Φ) "_ HPost".
    iMod (ghost_var_alloc 0) as (γ1) "[Hγ1● Hγ1◯]".

    unfold alloc_node.
    wp_alloc master as "Hr1".
    wp_let.
 
    wp_apply (newlock_spec LockN (node_lock_inv 0 γ1) with "Hγ1●").
    iIntros (lk γ) "HIsLk".
    wp_let.
    wp_pures.
    iApply "HPost". 
    iFrame; auto.
  Qed.

  Lemma alloc_replicas_spec : 
    {{{ True%I }}}
      alloc_replicas #()
      {{{ r1 r2 lk1 lk2 γ1 γ2 γ3 γ4, RET PairV (PairV r1 lk1) (PairV r2 lk2);
          is_lock LockN γ3 lk1 (node_lock_inv 0 γ1) ∗
          is_lock LockN γ3 lk1 (node_lock_inv 0 γ1) ∗
          is_lock LockN γ4 lk2 (node_lock_inv 0 γ2) ∗
          is_lock LockN γ4 lk2 (node_lock_inv 0 γ2) ∗
          global_inv 0 (Some 0) (Some 0) γ1 γ2
    }}}.
  Proof.
    iIntros (Φ) "_ HPost".
    unfold alloc_replicas.
    wp_pures.
    wp_apply (alloc_node_spec); auto.
    iIntros (r1 lk γ4 γ1) "(Hislk1 & Hnodeinv1)".
    wp_let.
    wp_apply (alloc_node_spec); auto.
    iIntros (r2 lk2 γ3 γ2) "(Hislk2 & Hnodeinv2)".
    wp_let.
    wp_pures.
    iApply "HPost".
    repeat iSplit; auto.
    iFrame.
  Qed.

  Lemma update_node_some_spec : ∀ (n: Z) γ1 node,
      {{{
           node ↦ SOMEV #n
           ∗ node_lock_inv n γ1
           ∗ node_val_inv n (Some n) γ1
    }}}
      update_node #node
    {{{ RET #1;
          node ↦ SOMEV #(n+1)
          ∗ node_lock_inv (n+1) γ1
          ∗ node_val_inv (n+1) (Some (n+1)) γ1
    }}}.
  Proof.
    iIntros (n γ1 node Φ) "(Hnode & Hlkinv & Hnodeinv & Hown) HPost".
    unfold update_node.
    unfold node_lock_inv.
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
           ∗ node_lock_inv n γ1
           ∗ node_val_inv n None γ1
    }}}
      update_node #node
    {{{ RET #0;
          node ↦ SOMEV #0
          ∗ node_lock_inv 0 γ1
          ∗ node_val_inv 0 (Some 0) γ1
    }}}.
  Proof.
    iIntros (n γ1 node Φ) "(Hnode & Hlkinv & Hnodeinv & Hown) HPost".
    unfold update_node.
    unfold node_lock_inv.
    iMod (ghost_var_update γ1 0 with "Hlkinv Hown") as "[Hγ1● Hγ1◯]".
    wp_pures.
    wp_load.
    wp_pures.
    wp_store.
    iApply "HPost". 
    iFrame; auto.
  Qed.

  Lemma update_replicas_both_alive_spec : ∀ (n: Z) γ1 γ2 γ3 γ4 lk1 lk2 node1 node2,
      {{{
           node1 ↦ SOMEV #n 
           ∗ node2 ↦ SOMEV #n
           ∗ is_lock LockN γ3 lk1 (node_lock_inv n γ1)
           ∗ is_lock LockN γ3 lk1 (node_lock_inv n γ1)
           ∗ is_lock LockN γ4 lk2 (node_lock_inv n γ2)
           ∗ is_lock LockN γ4 lk2 (node_lock_inv n γ2)
           ∗ global_inv n (Some n) (Some n) γ1 γ2
    }}}
      update_replicas #node1 lk1 #node2 lk2
    {{{ RET #();
           node1 ↦ SOMEV #(n+1) 
           ∗ node2 ↦ SOMEV #(n+1)
           ∗ is_lock LockN γ3 lk1 (node_lock_inv (n+1) γ1)
           ∗ is_lock LockN γ3 lk1 (node_lock_inv (n+1) γ1)
           ∗ is_lock LockN γ4 lk2 (node_lock_inv (n+1) γ2)
           ∗ is_lock LockN γ4 lk2 (node_lock_inv (n+1) γ2)
           ∗ global_inv (n+1) (Some (n+1)) (Some (n+1)) γ1 γ2
    }}}.
  Proof.
  Admitted.

  Lemma update_replicas_one_dead_spec : ∀ (n: Z) γ1 γ2 γ3 γ4 lk1 lk2 node1 node2,
      {{{
           (node1 ↦ NONEV ∗ node2 ↦ SOMEV #n ∨ 
            node1 ↦ SOMEV #n ∗ node2 ↦ NONEV)
           ∗ is_lock LockN γ3 lk1 (node_lock_inv n γ1)
           ∗ is_lock LockN γ3 lk1 (node_lock_inv n γ1)
           ∗ is_lock LockN γ4 lk2 (node_lock_inv n γ2)
           ∗ is_lock LockN γ4 lk2 (node_lock_inv n γ2)
           ∗ global_inv n (Some n) (Some n) γ1 γ2
    }}}
      update_replicas #node1 lk1 #node2 lk2
    {{{ RET #();
           node1 ↦ SOMEV #(n+1) ∗ node2 ↦ SOMEV #(n+1)
           ∗ is_lock LockN γ3 lk1 (node_lock_inv (n+1) γ1)
           ∗ is_lock LockN γ3 lk1 (node_lock_inv (n+1) γ1)
           ∗ is_lock LockN γ4 lk2 (node_lock_inv (n+1) γ2)
           ∗ is_lock LockN γ4 lk2 (node_lock_inv (n+1) γ2)
           ∗ global_inv (n+1) (Some (n+1)) (Some (n+1)) γ1 γ2
    }}}.
  Proof.
  Admitted.

  Lemma update_replicas_both_dead_spec : ∀ (n: Z) γ1 γ2 γ3 γ4 lk1 lk2 node1 node2,
      {{{
           (node1 ↦ NONEV ∗ node2 ↦ NONEV)
           ∗ is_lock LockN γ3 lk1 (node_lock_inv n γ1)
           ∗ is_lock LockN γ3 lk1 (node_lock_inv n γ1)
           ∗ is_lock LockN γ4 lk2 (node_lock_inv n γ2)
           ∗ is_lock LockN γ4 lk2 (node_lock_inv n γ2)
           ∗ global_inv n (Some n) (Some n) γ1 γ2
    }}}
      update_replicas #node1 lk1 #node2 lk2
    {{{ RET #();
           node1 ↦ SOMEV #(0) ∗ node2 ↦ SOMEV #(0)
           ∗ is_lock LockN γ3 lk1 (node_lock_inv (0) γ1)
           ∗ is_lock LockN γ3 lk1 (node_lock_inv (0) γ1)
           ∗ is_lock LockN γ4 lk2 (node_lock_inv (0) γ2)
           ∗ is_lock LockN γ4 lk2 (node_lock_inv (0) γ2)
           ∗ global_inv (0) (Some 0) (Some 0) γ1 γ2
    }}}.
  Proof.
  Admitted.

End proof.
