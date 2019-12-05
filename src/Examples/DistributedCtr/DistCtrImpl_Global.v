From iris.algebra Require Import auth frac_auth excl.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode notation lib.par lib.spin_lock.
Require Import DistributedCtr.Helpers.
Require Import DistributedCtr.DistCtrImpl_Local.

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
  if: "r" < #(0)
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
  if: (("s1" = #0) || ("s2" = #0)) then
    recover_replicas "node1" "node2";;
    release "lk2";;
    release "lk1"
  else 
    release "lk2";;
    release "lk1".

Section proof.
  Context `{!heapG Σ, !spawnG Σ, !lockG Σ, !inG Σ (authR (optionUR (exclR ZO)))}.

  Definition global_inv_unlocked (node1 node2: loc) (optv1 optv2: option Z) (γ1 γ2 γ3 γ4: gname) (lk1 lk2 : val): iProp Σ :=
    is_lock LockN γ3 lk1 (node_lock_inv γ1) ∗ is_lock LockN γ4 lk2 (node_lock_inv γ2)
    ∗ ∃ n, (node_val_inv node1 n optv1 γ1) ∗ (node_val_inv node2 n optv2 γ2).

  Definition global_inv_locked (node1 node2: loc) (optv1 optv2: option Z) (γ1 γ2 : gname): iProp Σ := 
      node_lock_inv γ1 ∗ node_lock_inv γ2
    ∗ ∃ n, (node_val_inv node1 n optv1 γ1) ∗ (node_val_inv node2 n optv2 γ2).

  (* Notes: loc = kind of like a Coq literal number, LitV (LitLoc loc) is an actual value in the language *)

  Lemma alloc_replicas_spec : 
    {{{ True%I }}}
      alloc_replicas #()
      {{{ r1 r2 lk1 lk2 γ1 γ2 γ3 γ4, RET PairV (PairV #r1 lk1) (PairV #r2 lk2);
          global_inv_unlocked r1 r2 (Some 0) (Some 0) γ1 γ2 γ3 γ4 lk1 lk2
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
    unfold global_inv_unlocked; unfold node_val_inv.
    iExists 0; iSplitL "Hnodeinv1"; iFrame; auto.
  Qed.

  Lemma recover_replicas_both_alive_spec : ∀ (n: Z) γ1 γ2 node1 node2,
      {{{
          ⌜ ~n < 0 ⌝
           ∗ global_inv_locked node1 node2 (Some n) (Some n) γ1 γ2
    }}}
      recover_replicas #node1 #node2
      {{{ RET #n;
          ⌜ ~n < 0 ⌝
           ∗ global_inv_locked node1 node2 (Some n) (Some n) γ1 γ2
    }}}.
  Proof.
    iIntros (n γ1 γ2 node1 node2 ϕ) "(Hn & Hγ1● & Hγ2● & Hinv) HPost".
    iDestruct "Hn" as %Hn.
    unfold global_inv_locked; unfold node_val_inv; unfold node_lock_inv.
    iDestruct "Hγ1●" as (nlk1) "Hγ1●";
    iDestruct "Hγ2●" as (nlk2) "Hγ2●".
    iDestruct "Hinv" as (n') "(([(H1 & Hblah1) | (H1 & Hnode1)] & Hγ1◯) & [(H2 & Hblah2) | (H2& Hnode2)] & Hγ2◯)";
      iDestruct "H1" as %H1; inversion H1; subst;
      iDestruct "H2" as %H2; inversion H2; subst.
    iMod (ghost_var_update γ1 n' with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]";
    iMod (ghost_var_update γ2 n' with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".

    unfold recover_replicas.
    wp_pures.
    wp_load.
    wp_pures.
    wp_store.
    iApply "HPost"; iFrame.
    iSplit. iPureIntro; omega.
    iSplitL "Hγ1●". iExists n'; auto.
    iSplitL "Hγ2●". iExists n'; auto.
    iExists n'. iSplitL "Hγ1◯ Hnode1". iFrame; auto.
    iFrame; auto.
  Qed.

  Lemma recover_replicas_one_dead_spec : ∀ (n: Z) γ1 γ2 node1 node2,
      {{{
          ⌜ ~n < 0 ⌝
          ∗ ((global_inv_locked node1 node2 None (Some n) γ1 γ2)
             ∨ global_inv_locked node1 node2 (Some n) None γ1 γ2)
     }}}
      recover_replicas #node1 #node2
    {{{ RET #n;
          ⌜ ~n < 0 ⌝
           ∗ global_inv_locked node1 node2 (Some (n)) (Some (n)) γ1 γ2
     }}}.
  Proof.
    iIntros (n γ1 γ2 node1 node2 ϕ) "(Hnval & [(Hγ1● & Hγ2● & Hinv) | (Hγ1● & Hγ2● & Hinv)]) HPost";
    unfold global_inv_locked; unfold node_val_inv; unfold node_lock_inv;
    iDestruct "Hγ1●" as (nlk1) "Hγ1●";
    iDestruct "Hγ2●" as (nlk2) "Hγ2●";
    iDestruct "Hinv" as (n') "(([(H1 & Hblah1) | (H1 & Hnode1)] & Hγ1◯) & [(H2 & Hblah2) | (H2& Hnode2)] & Hγ2◯)";
    iDestruct "H1" as %H1; inversion H1; subst;
    iDestruct "H2" as %H2; inversion H2; subst;
      [ iMod (ghost_var_update γ2 n' with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]" 
        | iMod (ghost_var_update γ1 n' with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]"];
    unfold recover_replicas;
    wp_pures; wp_load; wp_pures;
    [wp_load; wp_pures | ]; wp_store;
      iApply "HPost"; iFrame;
        unfold node_lock_inv.
    iSplitL "Hγ1●"; auto.
    iSplitL "Hγ2●"; auto.
    iExists n'. iSplitL "Hγ1◯ Hblah1". iFrame; auto. iFrame; auto.
    iSplitL "Hγ1●"; auto.
    iSplitL "Hγ2●"; auto.
    iExists n'. iSplitL "Hγ1◯ Hnode1". iFrame; auto. iFrame; auto.
  Qed.

  Lemma recover_replicas_both_dead_spec : ∀ (n: Z) γ1 γ2 node1 node2, 
      {{{
           global_inv_locked node1 node2 None None γ1 γ2
    }}}
      recover_replicas #node1 #node2
    {{{ RET #(-1);
           global_inv_locked node1 node2 (Some 0) (Some 0) γ1 γ2
    }}}.
  Proof.
    iIntros (n γ1 γ2 node1 node2 ϕ) "(Hnode & Hinv) HPost".
    unfold global_inv_locked; unfold node_val_inv; unfold node_lock_inv.
    iDestruct "Hinv" as "(Hγ1● & Hγ2● & Hown)";
    iDestruct "Hown" as (n1) "(Hown1 & Hown2)";
    iDestruct "Hown1" as (Hsome1) "Hown1";
    iDestruct "Hown2" as (_) "Hown2";
    iDestruct "Hγ1●" as (nlk1) "Hγ1●";
    iDestruct "Hγ2●" as (nlk2) "Hγ2●";
    iMod (ghost_var_update γ1 0 with "Hγ1● Hown1") as "[Hγ1● Hγ1◯]";
    iMod (ghost_var_update γ2 0 with "Hγ2● Hown2") as "[Hγ2● Hγ2◯]";
    destruct Hsome1; [ | inversion H].
    unfold recover_replicas.
    iDestruct "Hnode" as "(Hnode1 & Hnode2)".
    wp_pures. wp_load; wp_pures. wp_load; wp_pures.
    wp_store; wp_store.
    iApply "HPost". iFrame.
    iSplitL "Hγ1●"; auto.
    iSplitL "Hγ2●"; auto.
    iExists 0; iSplitL "Hγ1◯"; auto.
  Qed.

  Lemma get_replicas_one_alive_spec : ∀ (n: Z) γ1 γ2 γ3 γ4 lk1 lk2 node1 node2,
      {{{
          ⌜ ~n < 0 ⌝
           ∗ ((node1 ↦ SOMEV #n ∗ node2 ↦ SOMEV #n) ∨
            (node1 ↦ NONEV ∗ node2 ↦ SOMEV #n) ∨ 
            (node1 ↦ SOMEV #n ∗ node2 ↦ NONEV))
           ∗ global_inv_unlocked (Some n) (Some n) γ1 γ2 γ3 γ4 lk1 lk2
    }}}
      get_replicas #node1 #node2 lk1 lk2
    {{{ RET #n;
          ⌜ ~n < 0 ⌝
        ∗ node1 ↦ SOMEV #(n) ∗ node2 ↦ SOMEV #(n)
        ∗ global_inv_unlocked (Some (n)) (Some (n)) γ1 γ2 γ3 γ4 lk1 lk2
    }}}.
  Proof.
    iIntros (n γ1 γ2 γ3 γ4 lk1 lk2 node1 node2 ϕ) "(Hnval & Hnode & Hglobalinv) HPost".
    iDestruct "Hnval" as %Hnval.
    unfold global_inv_unlocked; unfold node_val_inv; unfold node_lock_inv.
    iDestruct "Hglobalinv" as "(#Hlk1 & #Hlk2 & Hown)".
    iDestruct "Hown" as (n1) "(Hown1 & Hown2)".
    iDestruct "Hown1" as (Hn) "Hγ1◯";
    iDestruct "Hown2" as (_) "Hγ2◯";
    destruct Hn; inversion H; subst.
    unfold get_replicas.
    iDestruct "Hnode" as "[(Hnode1 & Hnode2) | Honedead]";
      wp_pures; 
      wp_apply (acquire_spec with "Hlk1");
      iIntros "(Hlked1 & Hγ1●)"; wp_pures;
      wp_apply (acquire_spec with "Hlk2");
      iIntros "(Hlked2 & Hγ2●)"; wp_pures;
        iDestruct "Hγ1●" as (n1') "Hγ1●";
        iDestruct "Hγ2●" as (n2') "Hγ2●";
        iMod (ghost_var_update γ1 (n1) with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]";
        iMod (ghost_var_update γ2 (n1) with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".

      - wp_apply ((recover_replicas_both_alive_spec n1 γ1 γ2)
                        with "[- HPost Hlked1 Hlked2]").
        unfold global_inv_locked; unfold node_val_inv; unfold node_lock_inv.
        iFrame; iSplit; auto.

        iSplitL "Hγ1●". iExists n1; auto.
        iSplitL "Hγ2●". iExists n1; auto.
        iExists n1; iSplitL "Hγ1◯"; iFrame; auto.

        iIntros "(_ & Hnode1 & Hnode2 & Hinv)".
        unfold global_inv_locked; unfold node_val_inv; unfold node_lock_inv.
        iDestruct "Hinv" as "(Hγ1● & Hγ2● & Hown)".
        iDestruct "Hown" as (n') "(Hown1 & Hown2)".
        iDestruct "Hown1" as (Hn) "Hγ1◯"; iDestruct "Hown2" as (_) "Hγ2◯".
        iDestruct "Hγ1●" as (n3) "Hγ1●";
        iDestruct "Hγ2●" as (n4) "Hγ2●";
        iMod (ghost_var_update γ1 (n1) with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]";
        iMod (ghost_var_update γ2 (n1) with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".

        unfold node_lock_inv.
        wp_let; wp_pures.
        case_bool_decide; try contradiction; wp_pures.

        wp_apply (release_spec with "[Hlked2 Hγ2● Hlk2]").
        iFrame; iSplit; auto.
        iIntros; wp_pures.
        wp_apply (release_spec with "[Hlk1 Hγ1● Hlked1]").
        iFrame; iSplit; auto.
        iIntros; wp_pures.
        iApply "HPost"; iSplit; auto; iFrame; iSplit; auto.
        iSplit; auto. iExists n1; auto.
        iFrame; auto.
      - wp_apply ((recover_replicas_one_dead_spec n1 γ1 γ2)
                            with "[- HPost Hlked1 Hlked2 ]").
        iSplit; auto.
        iDestruct "Honedead" as "[H1dead | H2dead]";
          unfold global_inv_locked; unfold node_val_inv; unfold node_lock_inv.
        iLeft. iFrame; auto. 
        iSplitL "Hγ1●". iExists n1; auto.
        iSplitL "Hγ2●". iExists n1; auto.
        iExists n1; iSplitL "Hγ1◯"; iFrame; auto.
        iRight. iFrame; auto. 
        iSplitL "Hγ1●". iExists n1; auto.
        iSplitL "Hγ2●". iExists n1; auto.
        iExists n1; iSplitL "Hγ1◯"; iFrame; auto.

        iIntros "(_ & Hnode1 & Hnode2 & Hinv)". wp_let; wp_pures.
        iDestruct "Hinv" as "(Hγ1● & Hγ2● & Hown)".
        iDestruct "Hown" as (n') "(Hown1 & Hown2)".
        iDestruct "Hown1" as (Hn) "Hγ1◯"; iDestruct "Hown2" as (_) "Hγ2◯".
        iDestruct "Hγ1●" as (n3) "Hγ1●";
        iDestruct "Hγ2●" as (n4) "Hγ2●";
        iMod (ghost_var_update γ1 (n1) with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]";
        iMod (ghost_var_update γ2 (n1) with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".
        case_bool_decide; try contradiction; wp_pures.
        wp_apply (release_spec with "[Hlked2 Hγ2● Hlk2]").
        iFrame; iSplit; auto.
        iIntros; wp_pures.
        wp_apply (release_spec with "[Hlked1 Hγ1● Hlk1]").
        iFrame; iSplit; auto.
        iIntros; wp_pures.
        iApply "HPost"; iSplit; auto; iFrame; iSplit; auto.
        iSplit; auto.
        iExists n1; iFrame; auto.
  Qed.
  
  Lemma get_replicas_both_dead_spec : ∀ (n: Z) γ1 γ2 γ3 γ4 lk1 lk2 node1 node2,
      {{{
           (node1 ↦ NONEV ∗ node2 ↦ NONEV)
           ∗ global_inv_unlocked (Some n) (Some n) γ1 γ2 γ3 γ4 lk1 lk2
    }}}
      get_replicas #node1 #node2 lk1 lk2
    {{{ RET #0;
           node1 ↦ SOMEV #(0) ∗ node2 ↦ SOMEV #(0)
           ∗ global_inv_unlocked (Some 0) (Some 0) γ1 γ2 γ3 γ4 lk1 lk2
    }}}.
  Proof.
    iIntros (n γ1 γ2 γ3 γ4 lk1 lk2 node1 node2 ϕ) "(Hnode & Hinv) HPost".
    unfold global_inv_unlocked; unfold node_val_inv; unfold node_lock_inv.
    iDestruct "Hinv" as "(#Hlk1 & #Hlk2 & Hown)".
    iDestruct "Hown" as (n') "(Hown1 & Hown2)".
    iDestruct "Hown1" as (Hn) "Hγ1◯"; iDestruct "Hown2" as (_) "Hγ2◯".
    destruct Hn; inversion H; subst.
    unfold get_replicas.
    wp_pures.
    wp_apply (acquire_spec with "Hlk1");
      iIntros "(Hlked1 & Hγ1●)"; wp_pures;
      wp_apply (acquire_spec with "Hlk2");
      iIntros "(Hlked2 & Hγ2●)"; wp_pures.
    iDestruct "Hγ1●" as (nlk1) "Hγ1●".
    iDestruct "Hγ2●" as (nlk2) "Hγ2●".
 
    iMod (ghost_var_update γ1 n' with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]".
    iMod (ghost_var_update γ2 n' with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".

    wp_apply ((recover_replicas_both_dead_spec n' γ1 γ2)
                with "[- HPost Hlked1 Hlked2]"). 
    iFrame; unfold global_inv_unlocked; unfold node_lock_inv; unfold node_val_inv; auto.
    iSplitL "Hγ1●". iExists n'; auto.
    iSplitL "Hγ2●". iExists n'; auto.
    iExists n'; iSplitL "Hγ1◯"; iFrame; auto.

    iIntros "(Hnode1 & Hnode2 & Hγ1● & Hγ2● & Hown)".
    unfold global_inv_locked; unfold node_val_inv; unfold node_lock_inv.
    iDestruct "Hown" as (n1) "(Hown1 & Hown2)".
    iDestruct "Hown1" as (Hn) "Hγ1◯"; iDestruct "Hown2" as (_) "Hγ2◯".
    iDestruct "Hγ1●" as (n3) "Hγ1●";
    iDestruct "Hγ2●" as (n4) "Hγ2●";
    iMod (ghost_var_update γ1 (0) with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]";
    iMod (ghost_var_update γ2 (0) with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".
    wp_pures.
    wp_apply (release_spec with "[Hlk2 Hlked2 Hγ2●]").
    iSplitL "Hlk2"; auto. iSplitL "Hlked2"; auto.

    iIntros; wp_pures.
    wp_apply (release_spec with "[Hlked1 Hlk1 Hγ1●]").
    iSplitL "Hlk1"; auto. iSplitL "Hlked1"; auto.
    iIntros; wp_pures.
    iApply "HPost". iFrame. repeat iSplit; auto.
    iExists 0. iFrame; auto.
  Qed.

   Lemma update_replicas_one_alive_spec : ∀ (n: Z) γ1 γ2 γ3 γ4 lk1 lk2 node1 node2,
      {{{
          ⌜ ~n < 0 ⌝
           ∗ ((node1 ↦ SOMEV #n ∗ node2 ↦ SOMEV #n) ∨
            (node1 ↦ NONEV ∗ node2 ↦ SOMEV #n) ∨ 
            (node1 ↦ SOMEV #n ∗ node2 ↦ NONEV))
           ∗ global_inv_unlocked (Some n) (Some n) γ1 γ2 γ3 γ4 lk1 lk2
    }}}
      update_replicas #node1 #node2 lk1 lk2
      {{{ ret, RET #();
        ⌜ ret = Z.succ n ⌝ ∗ ⌜ ~ret < 0 ⌝
        ∗ node1 ↦ SOMEV #(ret) ∗ node2 ↦ SOMEV #(ret)
        ∗ global_inv_unlocked (Some (n+1)) (Some (n+1)) γ1 γ2 γ3 γ4 lk1 lk2
    }}}.
   Proof.
    iIntros (n γ1 γ2 γ3 γ4 lk1 lk2 node1 node2 ϕ) "(Hnval & Hnode & Hglobalinv) HPost".
    iDestruct "Hnval" as %Hnval.
    unfold global_inv_unlocked; unfold node_val_inv; unfold node_lock_inv.
    iDestruct "Hglobalinv" as "(#Hlk1 & #Hlk2 & Hown)".
    iDestruct "Hown" as (n1) "(Hown1 & Hown2)".
    iDestruct "Hown1" as (Hn) "Hγ1◯";
    iDestruct "Hown2" as (_) "Hγ2◯";
    destruct Hn; inversion H; subst.
    unfold update_replicas.
    iDestruct "Hnode" as "[(Hnode1 & Hnode2) | Honedead]";
      wp_pures; 
      wp_apply (acquire_spec with "Hlk1");
      iIntros "(Hlked1 & Hγ1●)"; wp_pures;
      wp_apply (acquire_spec with "Hlk2");
      iIntros "(Hlked2 & Hγ2●)"; wp_pures;
      iDestruct "Hγ1●" as (n1') "Hγ1●";
      iDestruct "Hγ2●" as (n2') "Hγ2●";
      iMod (ghost_var_update γ1 (n1) with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]";
      iMod (ghost_var_update γ2 (n1) with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".
   
    - wp_apply (update_node_some_spec with "[Hnode1 Hγ1◯ Hγ1●]").
      iFrame. iSplit; auto. unfold node_lock_inv. iExists n1; auto.
      iIntros "(Hnode1 & Hγ1● & Hγ1◯)". wp_let; wp_pures.

      wp_apply (update_node_some_spec with "[Hnode2 Hγ2◯ Hγ2●]").
      iFrame. iSplit; auto. unfold node_lock_inv. iExists n1; auto.
      iIntros "(Hnode2 & Hγ2● & Hγ2◯)". wp_let; wp_pures.
      unfold node_lock_inv; unfold node_val_inv.

      wp_apply (release_spec with "[Hlked2 Hγ2● Hlk2]").
      iFrame; iSplit; auto.
      iIntros; wp_pures.

      wp_apply (release_spec with "[Hlked1 Hγ1● Hlk1]").
      iFrame; iSplit; auto.
      iIntros; wp_pures.

      iApply "HPost"; iSplit; auto; iFrame; iSplit; auto.
      iPureIntro; omega.
      iSplit; auto. iSplit; auto.
      iExists (n1+1); iSplitL "Hγ1◯"; iFrame; auto.

    - iDestruct "Honedead" as "[(Hnode1 & Hnode2) | (Hnode1 & Hnode2)]"; 
        unfold global_inv_unlocked; unfold node_val_inv; unfold node_lock_inv.

      * wp_apply (update_node_none_spec with "[Hnode1 Hγ1◯ Hγ1●]").
        iFrame. iSplit; auto. unfold node_lock_inv. iExists n1; auto.
        iIntros "(Hnode1 & Hγ1● & Hγ1◯)". wp_let; wp_pures.

        wp_apply (update_node_some_spec with "[Hnode2 Hγ2◯ Hγ2●]").
        iFrame. iSplit; auto. unfold node_lock_inv. iExists n1; auto.
        iIntros "(Hnode2 & Hγ2● & Hγ2◯)".
        wp_let; wp_pures.
        unfold node_lock_inv; unfold node_val_inv.
        iDestruct "Hγ1●" as (n3') "Hγ1●";
        iDestruct "Hγ2●" as (n4') "Hγ2●".
        iDestruct "Hγ1◯" as (naf _) "Hγ1◯".
        iDestruct "Hγ2◯" as (_) "Hγ2◯".
        iMod (ghost_var_update γ1 (n1+1) with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]";
        iMod (ghost_var_update γ2 (n1+1) with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".

        wp_apply ((recover_replicas_one_dead_spec (n1+1) γ1 γ2)
                                with "[- HPost Hlked1 Hlked2 ]").
        iSplit; auto.
        iPureIntro; omega.
        iLeft. iFrame; auto.
        unfold global_inv_locked; unfold node_val_inv; unfold node_lock_inv.
        iSplitL "Hγ1●"; auto.
        iSplitL "Hγ2●"; auto.
        iExists (n1 + 1); iSplitL "Hγ1◯"; iFrame; auto.

        iIntros "(_ & Hnode1 & Hnode2 & Hγ1● & Hγ2● & Hinv)". wp_pures.
        wp_apply (release_spec with "[Hlked2 Hγ2● Hlk2]").
        iFrame; iSplit; auto.
        iIntros; wp_pures.
        wp_apply (release_spec with "[Hlked1 Hγ1● Hlk1]").
        iFrame; iSplit; auto.
        iIntros; wp_pures.
        iApply "HPost"; iSplit; auto; iFrame; iSplit; auto.
        iPureIntro; omega.

      * wp_apply (update_node_some_spec with "[Hnode1 Hγ1◯ Hγ1●]").
        iFrame. iSplit; auto. unfold node_lock_inv. iExists n1; auto.
        iIntros "(Hnode1 & Hγ1● & Hγ1◯)". wp_let; wp_pures.

        wp_apply (update_node_none_spec with "[Hnode2 Hγ2◯ Hγ2●]").
        iFrame. iSplit; auto. unfold node_lock_inv. iExists n1; auto.
        iIntros "(Hnode2 & Hγ2● & Hγ2◯)". wp_let; wp_pures.
        unfold node_lock_inv; unfold node_val_inv.
        iDestruct "Hγ1●" as (n5) "Hγ1●";
        iDestruct "Hγ2●" as (n6) "Hγ2●".

        iDestruct "Hγ1◯" as (_) "Hγ1◯".
        iDestruct "Hγ2◯" as (naf _) "Hγ2◯".
        iMod (ghost_var_update γ1 (n1+1) with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]";
        iMod (ghost_var_update γ2 (n1+1) with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".

        wp_apply ((recover_replicas_one_dead_spec (n1+1) γ1 γ2)
                                with "[- HPost Hlked1 Hlked2 ]").
        iSplit; auto.
        iPureIntro; omega.
        unfold global_inv_locked; unfold node_val_inv; unfold node_lock_inv.
        iRight. iFrame; auto.
        unfold global_inv_locked; unfold node_val_inv; unfold node_lock_inv.
        iSplitL "Hγ1●"; auto.
        iSplitL "Hγ2●"; auto.
        iExists (n1 +1); iSplitL "Hγ1◯"; iFrame; auto.

        iIntros "(_ & Hnode1 & Hnode2 & Hγ1● & Hγ2● & Hinv)". wp_pures.
        wp_apply (release_spec with "[Hlked2 Hγ2● Hlk2]").
        iFrame; iSplit; auto.
        iIntros; wp_pures.
        wp_apply (release_spec with "[Hlked1 Hγ1● Hlk1]").
        iFrame; iSplit; auto.
        iIntros; wp_pures.
        iApply "HPost"; iSplit; auto; iFrame; iSplit; auto.
        iPureIntro; omega.
  Qed.

  Lemma update_replicas_both_dead_spec : ∀ (n: Z) γ1 γ2 γ3 γ4 lk1 lk2 node1 node2,
      {{{
           (node1 ↦ NONEV ∗ node2 ↦ NONEV)
           ∗ global_inv_unlocked (Some n) (Some n) γ1 γ2 γ3 γ4 lk1 lk2
    }}}
      update_replicas #node1 #node2 lk1 lk2
    {{{ RET #();
           node1 ↦ SOMEV #(0) ∗ node2 ↦ SOMEV #(0)
           ∗ global_inv_unlocked (Some 0) (Some 0) γ1 γ2 γ3 γ4 lk1 lk2
    }}}.
  Proof.
    iIntros (n γ1 γ2 γ3 γ4 lk1 lk2 node1 node2 ϕ) "((Hnode1 & Hnode2) & Hinv) HPost".
    unfold global_inv_unlocked; unfold node_val_inv; unfold node_lock_inv.
    iDestruct "Hinv" as "(#Hlk1 & #Hlk2 & Hown)".
    iDestruct "Hown" as (n') "(Hown1 & Hown2)".
    iDestruct "Hown1" as (Hn) "Hγ1◯"; iDestruct "Hown2" as (_) "Hγ2◯".
    destruct Hn; inversion H; subst.
    unfold update_replicas.
    wp_pures.
    wp_apply (acquire_spec with "Hlk1");
      iIntros "(Hlked1 & Hγ1●)"; wp_pures;
      wp_apply (acquire_spec with "Hlk2");
      iIntros "(Hlked2 & Hγ2●)"; wp_pures.
    iDestruct "Hγ1●" as (nlk1) "Hγ1●".
    iDestruct "Hγ2●" as (nlk2) "Hγ2●".
 
    iMod (ghost_var_update γ1 0 with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]".
    iMod (ghost_var_update γ2 0 with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".

    wp_apply (update_node_none_spec with "[Hnode1 Hγ1◯ Hγ1●]").
        unfold node_val_inv; unfold node_lock_inv.
        iFrame; auto.
        iIntros "(Hnode1 & Hγ1● & Hγ1◯)". wp_let; wp_pures.

    wp_apply (update_node_none_spec with "[Hnode2 Hγ2◯ Hγ2●]").
        unfold node_val_inv; unfold node_lock_inv.
        iFrame; auto.
        iIntros "(Hnode2 & Hγ2● & Hγ2◯)". wp_let; wp_pures.
        unfold node_lock_inv; unfold node_val_inv.
    iDestruct "Hγ1◯" as (nah01 _) "Hγ1◯".
    iDestruct "Hγ2◯" as (nah02 _) "Hγ2◯".
    iDestruct "Hγ1●" as (nah1) "Hγ1●";
    iDestruct "Hγ2●" as (nah2) "Hγ2●".
    iMod (ghost_var_update γ1 (0) with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]";
    iMod (ghost_var_update γ2 (0) with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".

    wp_apply ((recover_replicas_both_dead_spec 0 γ1 γ2)
                with "[- HPost Hlked1 Hlked2]").
    iFrame; unfold global_inv_locked; unfold node_lock_inv; unfold node_val_inv; auto.
    iSplitL "Hγ1●"; auto.
    iSplitL "Hγ2●"; auto.
    iExists 0; iSplitL "Hγ1◯"; iFrame; auto; iSplit; auto.

    iIntros "(Hnode1 & Hnode2 & Hγ1● & Hγ2● & Hinv)".
    wp_pures.
    wp_apply (release_spec with "[Hlked2 Hlk2 Hγ2●]").
    iFrame; auto.
    iIntros; wp_pures.
    wp_apply (release_spec with "[Hlked1 Hlk1 Hγ1●]").
    iFrame; auto.
    iIntros; wp_pures.
    iApply "HPost". iFrame. iSplit; auto. 
  Qed.
End proof.
