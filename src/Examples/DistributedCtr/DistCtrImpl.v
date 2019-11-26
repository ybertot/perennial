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
  | NONE => #0
  end.

Definition kill_node: val :=
  λ: "node",
  "node" <- NONE.

(* GLOBAL, CLIENT-FACING FUNCTIONS *)
Definition alloc_replicas : val := λ: "()",
  let: "master" := alloc_node #() in
  let: "backup" := alloc_node #() in
  Pair "master" "backup".

Definition recover_replicas: val :=
  λ: "node1" "node2",
  match: !"node1" with
    SOME "v1" => "node2" <- SOME "v1";;
                         "v1"
    | NONE => match: !"node2" with
                SOME "v2" => "node1" <- SOME "v2";;
                               "v2"
              | NONE => "node1" <- SOME #0;;
                                "node2" <- SOME #0;;
                                #-1
              end
  end.
 
Definition get_replicas: val :=
  λ: "node1" "node2" "lk1" "lk2",
  acquire "lk1";;
  acquire "lk2";;
  let: "r" := recover_replicas "node1" "node2" in
  if: "r" = #(-1)
  then
    release "lk2";;
    release "lk1";;
    #0
  else
    release "lk2";;
    release "lk1";;
    "r".
 
Definition update_replicas: val :=
  λ: "node1" "node2" "lk1" "lk2",
  acquire "lk1";;
  acquire "lk2";;
  let: "s1" := update_node "node1" in
  let: "s2" := update_node "node2" in
  if: (("s1" = #0) || ("s2" = #0) then
    recover_replicas "node1" "node2";;
    release "lk2";;
    release "lk1"
  else 
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

  Definition node_lock_inv (γ: gname) : iProp Σ :=
    (∃ n, own γ (● (Excl' n)))%I.

  Definition global_inv (optv1 optv2: option Z) (γ1 γ2 : gname): iProp Σ := ∃ n,
    (node_val_inv n optv1 γ1) ∗ (node_val_inv n optv2 γ2).
  (* Notes: loc = kind of like a Coq literal number, LitV (LitLoc loc) is an actual value in the language *)

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

  Lemma alloc_replicas_spec : 
    {{{ True%I }}}
      alloc_replicas #()
      {{{ r1 r2 lk1 lk2 γ1 γ2 γ3 γ4, RET PairV (PairV r1 lk1) (PairV r2 lk2);
          is_lock LockN γ3 lk1 (node_lock_inv γ1) ∗
          is_lock LockN γ4 lk2 (node_lock_inv γ2) ∗
          global_inv (Some 0) (Some 0) γ1 γ2
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
    unfold global_inv; unfold node_val_inv; iExists 0; iFrame; auto.
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
          ∗ node_val_inv 0 (Some 0) γ1
    }}}.
  Proof.
    iIntros (n γ1 node Φ) "(Hnode & Hlkinv & Hnodeinv & Hown) HPost".
    unfold update_node.
    unfold node_lock_inv.
    iDestruct "Hlkinv" as (n') "Hlkinv".
    iMod (ghost_var_update γ1 0 with "Hlkinv Hown") as "[Hγ1● Hγ1◯]".
    wp_pures.
    wp_load.
    wp_pures.
    iApply "HPost". 
    iFrame; auto.
  Qed.

  Lemma recover_replicas_both_alive_spec : ∀ (n: Z) γ1 γ2 node1 node2,
      {{{
          ⌜ (bool_decide (#n = #(-1)) = false) ⌝
           ∗ node1 ↦ SOMEV #n ∗ node2 ↦ SOMEV #n
           ∗ global_inv (Some n) (Some n) γ1 γ2
    }}}
      recover_replicas #node1 #node2
      {{{ RET #n;
          ⌜ (bool_decide (#n = #(-1)) = false) ⌝
           ∗ node1 ↦ SOMEV #(n) ∗ node2 ↦ SOMEV #(n)
           ∗ global_inv (Some (n)) (Some (n)) γ1 γ2
    }}}.
  Proof.
    iIntros (n γ1 γ2 node1 node2 ϕ) "(Hn & Hnode1 & Hnode2 & Hinv) HPost".
    iDestruct "Hn" as %Hn.
    unfold global_inv; unfold node_val_inv.
    iDestruct "Hinv" as (n0) "(Hown1 & Hown2)".
    iDestruct "Hown1" as (Hsomen) "Hown1".
    iDestruct "Hown2" as (_) "Hown2".
    destruct Hsomen; [ | inversion H].
    unfold recover_replicas.
    wp_pures.
    wp_load.
    wp_pures.
    wp_store.
    iApply "HPost"; iFrame.
    iSplit; auto; iExists n0; iFrame; auto.
  Qed.

  Lemma recover_replicas_one_dead_spec : ∀ (n: Z) γ1 γ2 node1 node2,
      {{{
          ⌜ (bool_decide (#n = #(-1)) = false) ⌝
           ∗ ((node1 ↦ NONEV ∗ node2 ↦ SOMEV #n) ∨ 
            (node1 ↦ SOMEV #n ∗ node2 ↦ NONEV))
           ∗ global_inv (Some n) (Some n) γ1 γ2
    }}}
      recover_replicas #node1 #node2
    {{{ RET #n;
          ⌜ (bool_decide (#n = #(-1)) = false) ⌝
           ∗ node1 ↦ SOMEV #(n) ∗ node2 ↦ SOMEV #(n)
           ∗ global_inv (Some (n)) (Some (n)) γ1 γ2
    }}}.
  Proof.
    iIntros (n γ1 γ2 node1 node2 ϕ) "(Hnval & Hnode & Hinv) HPost".
    unfold global_inv; unfold node_val_inv.
    iDestruct "Hinv" as (n0) "(Hown1 & Hown2)".
    iDestruct "Hown1" as (Hn) "Hown1".
    iDestruct "Hown2" as (_) "Hown2".
    destruct Hn; [ | inversion H].
    unfold recover_replicas.
    iDestruct "Hnode" as "[(Hnode1 & Hnode2) | (Hnode1 & Hnode2)]";
      wp_pures; wp_load; wp_pures;
        [wp_load; wp_pures | ]; wp_store;
          iApply "HPost"; iFrame; iExists n0; iFrame; auto.
  Qed.

  Lemma recover_replicas_both_dead_spec : ∀ (n: Z) γ1 γ2 node1 node2, 
      {{{
           (node1 ↦ NONEV ∗ node2 ↦ NONEV)
           ∗ global_inv (Some n) (Some n) γ1 γ2
           ∗ node_lock_inv γ1
           ∗ node_lock_inv γ2
    }}}
      recover_replicas #node1 #node2
    {{{ RET #(-1);
           node1 ↦ SOMEV #(0) ∗ node2 ↦ SOMEV #(0)
           ∗ global_inv (Some 0) (Some 0) γ1 γ2
           ∗ node_lock_inv γ1
           ∗ node_lock_inv γ2
    }}}.
  Proof.
    iIntros (n γ1 γ2 node1 node2 ϕ) "(Hnode & Hinv & Hnodelk1 & Hnodelk2) HPost".
    unfold global_inv; unfold node_val_inv; unfold node_lock_inv.
    iDestruct "Hinv" as (n') "(Hown1 & Hown2)".
    iDestruct "Hown1" as (Hn) "Hown1".
    iDestruct "Hown2" as (_) "Hown2".
    iDestruct "Hnodelk1" as (nlk1) "Hnodelk1".
    iDestruct "Hnodelk2" as (nlk2) "Hnodelk2".
    iMod (ghost_var_update γ1 (0) with "Hnodelk1 Hown1") as "[Hγ1● Hγ1◯]".
    iMod (ghost_var_update γ2 (0) with "Hnodelk2 Hown2") as "[Hγ2● Hγ2◯]".
    destruct Hn; [ | inversion H].
    unfold recover_replicas.
    iDestruct "Hnode" as "(Hnode1 & Hnode2)".
    wp_pures. wp_load; wp_pures. wp_load; wp_pures.
    wp_store; wp_store.
    iApply "HPost". iFrame.
    admit. (* TODO how to deal with framing here? *)
  Admitted.

  Lemma get_replicas_one_alive_spec : ∀ (n: Z) γ1 γ2 γ3 γ4 lk1 lk2 node1 node2,
      {{{
          ⌜ (bool_decide (#n = #(-1)) = false) ⌝
           ∗ ((node1 ↦ SOMEV #n ∗ node2 ↦ SOMEV #n) ∨
           (node1 ↦ NONEV ∗ node2 ↦ SOMEV #n) ∨ 
           (node1 ↦ SOMEV #n ∗ node2 ↦ NONEV))
           ∗ is_lock LockN γ3 lk1 (node_lock_inv γ1)
           ∗ is_lock LockN γ4 lk2 (node_lock_inv γ2)
           ∗ global_inv (Some n) (Some n) γ1 γ2
    }}}
      get_replicas #node1 #node2 lk1 lk2
    {{{ RET #n;
        ⌜ (bool_decide (#n = #(-1)) = false) ⌝
        ∗ node1 ↦ SOMEV #(n) ∗ node2 ↦ SOMEV #(n)
        ∗ is_lock LockN γ3 lk1 (node_lock_inv γ1)
        ∗ is_lock LockN γ4 lk2 (node_lock_inv γ2)
        ∗ global_inv (Some (n)) (Some (n)) γ1 γ2
    }}}.
  Proof.
    iIntros (n γ1 γ2 γ3 γ4 lk1 lk2 node1 node2 ϕ) "(Hnval & Hnode & #Hlkinv1 & #Hlkinv2 & Hglobalinv) HPost".
    unfold global_inv; unfold node_val_inv; unfold node_lock_inv.
    iDestruct "Hglobalinv" as (n') "(Hown1 & Hown2)".
    iDestruct "Hown1" as (Hn) "Hown1".
    iDestruct "Hown2" as (_) "Hown2".
    destruct Hn; inversion H; subst.
    unfold get_replicas.
    iDestruct "Hnode" as "[(Hnode1 & Hnode2) | Honedead]";
      wp_pures; 
      wp_apply (acquire_spec with "Hlkinv1");
      iIntros "(Hlked1 & Hγ1●)"; wp_pures;
      wp_apply (acquire_spec with "Hlkinv2");
      iIntros "(Hlked2 & Hγ2●)"; wp_pures;
      [ wp_apply ((recover_replicas_both_alive_spec n' γ1 γ2)
                        with "[- HPost Hlked1 Hlked2 Hγ1● Hγ2●]")  |
        wp_apply ((recover_replicas_one_dead_spec n' γ1 γ2)
                            with "[- HPost Hlked1 Hlked2 Hγ1● Hγ2●]") ];
        iFrame; auto; unfold global_inv; unfold node_val_inv.
    1,3:
      iExists n'; iFrame; auto.
    all:
      iIntros "(Hnval & Hnode1 & Hnode2 & Hinv)"; wp_let; wp_pures; 
      iDestruct "Hnval" as %->; wp_pures;
      wp_apply (release_spec with "[Hlked2 Hγ2● Hlkinv2]").
    1,3:
      iFrame; iSplit; auto.
    all:
      iIntros; wp_pures;
      wp_apply (release_spec with "[Hlked1 Hγ1● Hlkinv1]"). 
    1,3:
      iFrame; iSplit; auto.
    all:
      iIntros; wp_pures; iApply "HPost"; iSplit; auto; iFrame; iSplit; auto.
Qed.

  Lemma get_replicas_both_dead_spec : ∀ (n: Z) γ1 γ2 γ3 γ4 lk1 lk2 node1 node2,
      {{{
           (node1 ↦ NONEV ∗ node2 ↦ NONEV)
           ∗ is_lock LockN γ3 lk1 (node_lock_inv γ1)
           ∗ is_lock LockN γ4 lk2 (node_lock_inv γ2)
           ∗ global_inv (Some n) (Some n) γ1 γ2
    }}}
      get_replicas #node1 #node2 lk1 lk2
    {{{ RET #0;
           node1 ↦ SOMEV #(0) ∗ node2 ↦ SOMEV #(0)
           ∗ is_lock LockN γ3 lk1 (node_lock_inv γ1)
           ∗ is_lock LockN γ4 lk2 (node_lock_inv γ2)
           ∗ global_inv (Some 0) (Some 0) γ1 γ2
    }}}.
  Proof.
    iIntros (n γ1 γ2 γ3 γ4 lk1 lk2 node1 node2 ϕ) "(Hnode & #Hlkinv1 & #Hlkinv2 & Hglobalinv) HPost".
    unfold global_inv; unfold node_val_inv; unfold node_lock_inv.
    iDestruct "Hglobalinv" as (n') "(Hown1 & Hown2)".
    iDestruct "Hown1" as (Hn) "Hown1".
    iDestruct "Hown2" as (_) "Hown2".
    destruct Hn; inversion H; subst.
    unfold get_replicas.
    wp_pures.
    wp_apply (acquire_spec with "Hlkinv1");
      iIntros "(Hlked1 & Hγ1●)"; wp_pures;
      wp_apply (acquire_spec with "Hlkinv2");
      iIntros "(Hlked2 & Hγ2●)"; wp_pures.
    wp_apply ((recover_replicas_both_dead_spec n' γ1 γ2)
                with "[- HPost Hlked1 Hlked2]"). 
    iFrame; unfold global_inv; unfold node_lock_inv; unfold node_val_inv; auto.
    iExists n'; iFrame; auto.

    iIntros "(Hnode1 & Hnode2 & Hinv & Hn1inv & Hn2inv)".
    wp_pures.
    wp_apply (release_spec with "[Hlked2 Hlkinv2 Hn2inv]").
    iFrame; auto.
    iIntros; wp_pures.
    wp_apply (release_spec with "[Hlked1 Hlkinv1 Hn1inv]").
    iFrame; auto.
    iIntros; wp_pures.
    iApply "HPost". iFrame. iSplit; auto. 
  Qed.

  Lemma update_replicas_one_alive_spec : ∀ (n: Z) γ1 γ2 γ3 γ4 lk1 lk2 node1 node2,
      {{{
          ⌜ (bool_decide (#n = #(-1)) = false) ⌝
           ∗ ((node1 ↦ SOMEV #n ∗ node2 ↦ SOMEV #n) ∨
           (node1 ↦ NONEV ∗ node2 ↦ SOMEV #n) ∨ 
           (node1 ↦ SOMEV #n ∗ node2 ↦ NONEV))
           ∗ is_lock LockN γ3 lk1 (node_lock_inv γ1)
           ∗ is_lock LockN γ4 lk2 (node_lock_inv γ2)
           ∗ global_inv (Some n) (Some n) γ1 γ2
    }}}
      update_replicas #node1 #node2 lk1 lk2
      {{{ n', RET #();
        ⌜ #n' = #(n+1) ⌝
        ∗ ⌜ (bool_decide (#n' = #(-1)) = false) ⌝
        ∗ node1 ↦ SOMEV #(n') ∗ node2 ↦ SOMEV #(n')
        ∗ is_lock LockN γ3 lk1 (node_lock_inv γ1)
        ∗ is_lock LockN γ4 lk2 (node_lock_inv γ2)
        ∗ global_inv (Some (n+1)) (Some (n+1)) γ1 γ2
    }}}.
  Proof.
    iIntros (n γ1 γ2 γ3 γ4 lk1 lk2 node1 node2 ϕ) "(Hnval & Hnode & #Hlkinv1 & #Hlkinv2 & Hglobalinv) HPost".
    unfold global_inv; unfold node_val_inv; unfold node_lock_inv.
    iDestruct "Hglobalinv" as (n') "(Hown1 & Hown2)".
    iDestruct "Hown1" as (Hn) "Hown1".
    iDestruct "Hown2" as (_) "Hown2".
    destruct Hn; inversion H; subst.
    unfold update_replicas.
    iDestruct "Hnode" as "[(Hnode1 & Hnode2) | Honedead]"; wp_pures;
      wp_apply (acquire_spec with "Hlkinv1");
      iIntros "(Hlked1 & Hγ1●)"; wp_pures;
      wp_apply (acquire_spec with "Hlkinv2");
      iIntros "(Hlked2 & Hγ2●)"; wp_pures.

    - wp_apply (update_node_some_spec with "[Hnode1 Hown1 Hγ1●]").
        unfold node_val_inv.
        iFrame; auto.
        iIntros "(Hnode1 & Hnodelkinv1 & Hvalinv1)". wp_let; wp_pures.

        wp_apply (update_node_some_spec with "[Hnode2 Hown2 Hγ2●]").
        unfold node_val_inv.
        iFrame; auto.
        iIntros "(Hnode2 & Hnodelkinv2 & Hvalinv2)". wp_let; wp_pures.

               wp_apply (release_spec with "[Hnodelkinv2 Hlked2]"); iFrame; auto.
        iIntros; wp_pures.

        wp_apply (release_spec with "[Hnodelkinv1 Hlked1]"); iFrame; auto.
        iIntros; wp_pures.

        iApply "HPost". iSplit; auto. iFrame; auto. iSplit.
        admit.
        (* TODO bool_decide? *)
        iSplit; auto.
        iSplit; auto.
        iExists (n' + 1).
        iFrame; auto.

    - iDestruct "Honedead" as "[(Hnode1 & Hnode2) | (Hnode1 & Hnode2)]".
      * wp_apply (update_node_none_spec with "[Hnode1 Hown1 Hγ1●]").
        unfold node_val_inv.
        iFrame; auto.
        iIntros "(Hnode1 & Hnodelkinv1 & Hvalinv1)". wp_let; wp_pures.

        wp_apply (update_node_some_spec with "[Hnode2 Hown2 Hγ2●]").
        unfold node_val_inv.
        iFrame; auto.
        iIntros "(Hnode2 & Hnodelkinv2 & Hvalinv2)". wp_let; wp_pures.

        wp_apply ((recover_replicas_one_dead_spec (n'+1) γ1 γ2)
                    with "[- HPost Hlked1 Hlked2 Hnodelkinv1 Hnodelkinv2]").
        iFrame; auto.
        unfold global_inv. iFrame; auto. iSplit; iFrame; auto.
        admit. (* TODO bool_decide *)
        admit. (* TODO framing  *)

        iIntros "(Hnval & Hnode1 & Hnode2 & Hinv)".
        wp_pures.

        wp_apply (release_spec with "[Hlkinv2 Hlked2 Hnodelkinv2]"). iSplit; auto. iFrame; auto.
        iIntros; wp_pures.

        wp_apply (release_spec with "[Hlkinv1 Hnodelkinv1 Hlked1]"); iFrame; auto.
        iIntros; wp_pures.
        iApply "HPost"; iSplit; auto. iFrame; iSplit; auto.

      * wp_apply (update_node_some_spec with "[Hnode1 Hown1 Hγ1●]").
        unfold node_val_inv.
        iFrame; auto.
        iIntros "(Hnode1 & Hnodelkinv1 & Hvalinv1)". wp_let; wp_pures.

        wp_apply (update_node_none_spec with "[Hnode2 Hown2 Hγ2●]").
        unfold node_val_inv.
        iFrame; auto.
        iIntros "(Hnode2 & Hnodelkinv2 & Hvalinv2)". wp_let; wp_pures.

        wp_apply ((recover_replicas_one_dead_spec (n'+1) γ1 γ2)
        with "[- HPost Hlked1 Hlked2 Hnodelkinv1 Hnodelkinv2]").
        iFrame; auto.
        unfold global_inv. iFrame; auto. iSplit; iFrame; auto.
        admit. (* TODO bool_decide *)
        admit. (* TODO framing  *)

            iIntros "(Hnval & Hnode1 & Hnode2 & Hinv)".
            wp_pures.

            wp_apply (release_spec with "[Hlkinv2 Hlked2 Hnodelkinv2]"). iSplit; auto. iFrame; auto.
            iIntros; wp_pures.

            wp_apply (release_spec with "[Hlkinv1 Hnodelkinv1 Hlked1]"); iFrame; auto.
            iIntros; wp_pures.
            iApply "HPost"; iSplit; auto. iFrame. iSplit; auto.
  Admitted.

  Lemma update_replicas_both_dead_spec : ∀ (n: Z) γ1 γ2 γ3 γ4 lk1 lk2 node1 node2,
      {{{
           (node1 ↦ NONEV ∗ node2 ↦ NONEV)
           ∗ is_lock LockN γ3 lk1 (node_lock_inv γ1)
           ∗ is_lock LockN γ4 lk2 (node_lock_inv γ2)
           ∗ global_inv (Some n) (Some n) γ1 γ2
    }}}
      update_replicas #node1 #node2 lk1 lk2
    {{{ RET #();
           node1 ↦ SOMEV #(0) ∗ node2 ↦ SOMEV #(0)
           ∗ is_lock LockN γ3 lk1 (node_lock_inv γ1)
           ∗ is_lock LockN γ4 lk2 (node_lock_inv γ2)
           ∗ global_inv (Some 0) (Some 0) γ1 γ2
    }}}.
  Proof.
    iIntros (n γ1 γ2 γ3 γ4 lk1 lk2 node1 node2 ϕ) "((Hnode1 & Hnode2) & #Hlkinv1 & #Hlkinv2 & Hglobalinv) HPost".
    unfold global_inv; unfold node_val_inv; unfold node_lock_inv.
    iDestruct "Hglobalinv" as (n') "(Hown1 & Hown2)".
    iDestruct "Hown1" as (Hn) "Hown1".
    iDestruct "Hown2" as (_) "Hown2".
    destruct Hn; inversion H; subst.
    unfold update_replicas.
    wp_pures.
    wp_apply (acquire_spec with "Hlkinv1");
      iIntros "(Hlked1 & Hγ1●)"; wp_pures;
      wp_apply (acquire_spec with "Hlkinv2");
      iIntros "(Hlked2 & Hγ2●)"; wp_pures.

    wp_apply (update_node_none_spec with "[Hnode1 Hown1 Hγ1●]").
        unfold node_val_inv.
        iFrame; auto.
        iIntros "(Hnode1 & Hnodelkinv1 & Hvalinv1)". wp_let; wp_pures.

    wp_apply (update_node_none_spec with "[Hnode2 Hown2 Hγ2●]").
        unfold node_val_inv.
        iFrame; auto.
        iIntros "(Hnode2 & Hnodelkinv2 & Hvalinv2)". wp_let; wp_pures.

    wp_apply ((recover_replicas_both_dead_spec 0 γ1 γ2)
                with "[- HPost Hlked1 Hlked2]"). 
    iFrame; unfold global_inv; unfold node_lock_inv; unfold node_val_inv; auto.
    iExists 0; iFrame; auto.

    iIntros "(Hnode1 & Hnode2 & Hinv & Hn1inv & Hn2inv)".
    wp_pures.
    wp_apply (release_spec with "[Hlked2 Hlkinv2 Hn2inv]").
    iFrame; auto.
    iIntros; wp_pures.
    wp_apply (release_spec with "[Hlked1 Hlkinv1 Hn1inv]").
    iFrame; auto.
    iIntros; wp_pures.
    iApply "HPost". iFrame. iSplit; auto. 
  Qed.

End proof.
