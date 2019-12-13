From iris.algebra Require Import auth frac_auth excl.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode notation lib.par lib.spin_lock.
Require Import DistributedCtr.Helpers.
Require Import DistributedCtr.DistCtrImpl_Local.

Definition alloc_replicas : val := λ: "()",
  let: "master" := alloc_node #() in
  let: "backup" := alloc_node #() in
  Pair "master" "backup".

Definition recover_node : val :=
  λ: "me" "other" "mylk" "otherlk",
  let: "v" := (get_node_val "other" "otherlk") in
  acquire "mylk";;
  "me" <- SOME ("v");;
  release "mylk";;
  "v".

(* Note: this only recovers the 1st node if dead, doesn't check the 2nd if alive *)
Definition get_val: val :=
  λ: "node1" "node2" "lk1" "lk2",
  let: "v" := (get_node_val "node1" "lk1") in
  if: "v" = #0
  then recover_node "node1" "node2" "lk1" "lk2";;
       let: "v" := (get_node_val "node2" "lk2") in
       "v"
  else "v".

Definition update_replicas: val :=
  λ: "node1" "node2" "lk1" "lk2",
  let: "s1" := update_node "node1" "lk1" in
  let: "s2" := update_node "node2" "lk2" in
  if: ("s1" = #0) then
    recover_node "node1" "node2" "mylk" "otherlk"
  else #();;
  if: ("s2" = #0) then
    recover_node "node2" "node1" "mylk" "otherlk"
  else #().

Section proof.
  Context `{!heapG Σ, !spawnG Σ, !lockG Σ, !inG Σ (authR (optionUR (exclR ZO)))}.

  Definition global_inv (n: Z) (node1 node2: loc) (γ1 γ2 γ3 γ4: gname) (lk1 lk2 : val): iProp Σ :=
    is_lock LockN γ3 lk1 (node_lock_inv node1 γ1) ∗ is_lock LockN γ4 lk2 (node_lock_inv node2 γ2)
    ∗ node_own_inv node1 n γ1 ∗ node_own_inv node2 n γ2.

  Definition global_inv_inconsistent (n1 n2: Z) (node1 node2: loc) (γ1 γ2 γ3 γ4: gname) (lk1 lk2 : val): iProp Σ :=
    is_lock LockN γ3 lk1 (node_lock_inv node1 γ1) ∗ is_lock LockN γ4 lk2 (node_lock_inv node2 γ2)
    ∗ node_own_inv node1 n1 γ1 ∗ node_own_inv node2 n2 γ2
    ∗ ⌜n1 = 0 ∨ n2 = 0⌝.
  (* Notes: loc = kind of like a Coq literal number, LitV (LitLoc loc) is an actual value in the language *)

  Lemma alloc_replicas_spec : 
    {{{ True%I }}}
      alloc_replicas #()
      {{{ r1 r2 lk1 lk2 γ1 γ2 γ3 γ4, RET PairV (PairV #r1 lk1) (PairV #r2 lk2);
          global_inv 0 r1 r2 γ1 γ2 γ3 γ4 lk1 lk2
    }}}.
  Proof.
    iIntros (Φ) "_ HPost".
    unfold alloc_replicas.
    wp_pures.
    wp_apply (alloc_node_spec); auto.
    iIntros (node1 lk γ4 γ1) "(#Hislk1 & Hγ1◯)".
    wp_let.
    wp_apply (alloc_node_spec); auto.
    iIntros (node2 lk2 γ3 γ2) "(#Hislk2 & Hγ2◯)".
    wp_let.
    wp_pures.
    iApply "HPost".
    repeat iSplit; auto.
    iFrame; auto.
  Qed.

  Lemma recover_node_spec : ∀ (n1 n2 : Z) γ1 γ2 γ3 γ4 node1 node2 lk1 lk2,
    {{{
           global_inv_inconsistent n1 n2 node1 node2 γ1 γ2 γ3 γ4 lk1 lk2
    }}}
      recover_node #node1 #node2 lk1 lk2
    {{{ ret, RET #ret;
           global_inv ret node1 node2 γ1 γ2 γ3 γ4 lk1 lk2
    }}}.
  Proof.
    iIntros (n1 n2 γ1 γ2 γ3 γ4 node1 node2 lk1 lk2 ϕ) "H Hpost".
    iDestruct "H" as "(#Hislk1 & #Hislk2 & Hγ1◯ & Hγ2◯ & Hn)".
    iDestruct "Hn" as %H.
    unfold global_inv; unfold global_inv_inconsistent; unfold node_lock_inv; unfold node_own_inv.
    unfold recover_node.
    wp_pures.
    wp_apply (get_node_val_spec with "[Hγ2◯]").
    iFrame; auto.

    unfold get_node_val.
    wp_pures.
    iIntros (ret) "(Hlked2 & Hγ12◯)".
    unfold node_own_inv.
    wp_let.
    wp_apply (acquire_spec); auto.

    iIntros "(Hlked1 & Hinv)".
    wp_pures.

    iDestruct "Hinv" as (n') "(Hγ1● & [Halive | Halive])";
      [iMod (ghost_var_update γ1 ret with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]"
      |iMod (ghost_var_update γ1 ret with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]"];
      wp_pures; wp_store;
    wp_apply (release_spec LockN γ3 lk1 (node_lock_inv node1 γ1) with "[Hlked1 Hislk1 Hγ1● Halive]"); auto.
    iSplit; auto.
    iFrame; auto.
    iExists ret.
    iFrame; auto.

    iIntros. wp_pures. iApply "Hpost".
    repeat iSplit; auto.
    iFrame; auto.

    iSplit; auto. iFrame; auto.
    iExists ret; iFrame; auto.

    iIntros. wp_pures.
    iApply "Hpost".
    repeat iSplit; auto.
    iFrame; auto.
  Qed.

  Lemma get_val_spec : ∀ (n: Z) γ1 γ2 γ3 γ4 lk1 lk2 node1 node2,
    {{{
         global_inv n node1 node2 γ1 γ2 γ3 γ4 lk1 lk2
    }}}
      get_val #node1 #node2 lk1 lk2
    {{{ ret, RET #ret;
        global_inv ret node1 node2 γ1 γ2 γ3 γ4 lk1 lk2
    }}}.
  Proof.
    iIntros (n γ1 γ2 γ3 γ4 lk1 lk2 node1 node2 ϕ) "H Hpost".
    iDestruct "H" as "(#Hislk1 & #Hislk2 & Hγ1◯ & Hγ2◯)".
    unfold global_inv; unfold node_lock_inv; unfold node_own_inv.
    unfold get_val.
    wp_pures.
    wp_apply (get_node_val_spec with "[Hγ1◯]").
    iFrame; auto.

    iIntros (ret) "(Hlked1 & Hγ1◯)".
    unfold node_own_inv.
    wp_let.
    destruct (Z_eq_dec ret 0); subst.

    wp_pures.
    wp_apply (recover_node_spec with "[Hγ1◯ Hγ2◯]").
    {
      unfold global_inv. repeat iSplit; auto.
      unfold node_own_inv; iFrame; auto.
    }

    wp_apply (acquire_spec); auto.

    iIntros "(Hlked1 & Hinv)".
    wp_pures.

    iDestruct "Hinv" as (n') "(Hγ1● & [Halive | Halive])";
      [iMod (ghost_var_update γ1 ret with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]"
      |iMod (ghost_var_update γ1 ret with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]"];
      wp_pures; wp_store;
    wp_apply (release_spec LockN γ3 lk1 (node_lock_inv node1 γ1) with "[Hlked1 Hislk1 Hγ1● Halive]"); auto.
    iSplit; auto.
    iFrame; auto.
    iExists ret.
    iFrame; auto.

    iIntros. wp_pures. iApply "Hpost".
    repeat iSplit; auto.
    iFrame; auto.

    iSplit; auto. iFrame; auto.
    iExists ret; iFrame; auto.

    iIntros. wp_pures.
    iApply "Hpost".
    repeat iSplit; auto.
    iFrame; auto.
  Qed.

   Lemma update_replicas_one_alive_spec : ∀ (n: Z) γ1 γ2 γ3 γ4 lk1 lk2 node1 node2,
    {{{
          ⌜ ~n < 0 ⌝
           ∗ (global_inv node1 node2 (Some n) (Some n) γ1 γ2 γ3 γ4 lk1 lk2
                ∨ global_inv node1 node2 None(Some n) γ1 γ2 γ3 γ4 lk1 lk2
                ∨ global_inv node1 node2 (Some n) None γ1 γ2 γ3 γ4 lk1 lk2)
    }}}
      update_replicas #node1 #node2 lk1 lk2
    {{{ RET #();
        global_inv node1 node2 (Some (n+1)) (Some (n+1)) γ1 γ2 γ3 γ4 lk1 lk2
    }}}.
   Proof.
    iIntros (n γ1 γ2 γ3 γ4 lk1 lk2 node1 node2 ϕ) "(Hn & [(#Hlk1 & #Hlk2 & Hinv) | [(#Hlk1 & #Hlk2 & Hinv) | (#Hlk1 & #Hlk2 & Hinv)]]) HPost";
      iDestruct "Hn" as %Hn;
      iDestruct "Hinv" as (n') "(([(H1 & Hblah1) | (H1 & Hnode1)] & Hγ1◯) & [(H2 & Hblah2) | (H2& Hnode2)] & Hγ2◯)";
      unfold global_inv; unfold node_val_inv; unfold node_lock_inv;
        iDestruct "H1" as %H1; inversion H1; subst;
        iDestruct "H2" as %H2; inversion H2; subst;
          unfold update_replicas;
      wp_pures; 
      wp_apply (acquire_spec with "Hlk1");
      iIntros "(Hlked1 & Hγ1●)"; wp_pures;
      wp_apply (acquire_spec with "Hlk2");
      iIntros "(Hlked2 & Hγ2●)"; wp_pures;
        iDestruct "Hγ1●" as (n1') "Hγ1●";
        iDestruct "Hγ2●" as (n2') "Hγ2●";
        iMod (ghost_var_update γ1 (n') with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]";
        iMod (ghost_var_update γ2 (n') with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".
    - wp_apply (update_node_some_spec with "[Hnode1 Hγ1◯ Hγ1●]").
      iFrame. unfold node_lock_inv; iSplitL "Hγ1●"; auto.
      unfold node_lock_inv; unfold node_val_inv.
      iIntros "(Hγ1● & Hnode1 & Hγ1◯)". wp_let; wp_pures.

      wp_apply (update_node_some_spec with "[Hnode2 Hγ2◯ Hγ2●]").
      iFrame. unfold node_lock_inv. iSplitL "Hγ2●"; auto. 
      iIntros "(Hγ2● & Hnode2 & Hγ2◯)". wp_let; wp_pures.
      unfold node_lock_inv; unfold node_val_inv.

      wp_apply (release_spec with "[Hlked2 Hγ2● Hlk2]").
      iFrame; iSplit; auto.
      iIntros; wp_pures.

      wp_apply (release_spec with "[Hlked1 Hγ1● Hlk1]").
      iFrame; iSplit; auto.
      iIntros; wp_pures.

      iApply "HPost"; iSplit; auto; iFrame; iSplit; auto.
      iExists (n'+1); iSplitL "Hγ1◯ Hnode1"; iFrame; auto.

    - wp_apply (update_node_none_spec with "[Hblah1 Hγ1◯ Hγ1●]").
      iFrame. unfold node_lock_inv. iSplitL "Hγ1●"; auto.
      unfold node_lock_inv; unfold node_val_inv.
      iIntros "(Hγ1● & H1)". iDestruct "H1" as (n1) "(Hnode1 & Hγ1◯)". wp_let; wp_pures.

      wp_apply (update_node_some_spec with "[Hnode2 Hγ2◯ Hγ2●]").
      iFrame. unfold node_lock_inv. iSplitL "Hγ2●"; auto. 
      unfold node_lock_inv; unfold node_val_inv.
      iIntros "(Hγ2● & H2)". iDestruct "H2" as "(Hnode2 & Hγ2◯)". wp_let; wp_pures.
        iDestruct "Hγ1●" as (n3') "Hγ1●";
        iDestruct "Hγ2●" as (n4') "Hγ2●".
        iMod (ghost_var_update γ1 (n'+1) with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]";
        iMod (ghost_var_update γ2 (n'+1) with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".

      wp_apply ((recover_replicas_one_dead_spec (n'+1) γ1 γ2)
                            with "[- HPost Hlked1 Hlked2 ]").
      iSplit; auto; unfold global_inv_locked; unfold node_val_inv; unfold node_lock_inv.
      iPureIntro; omega.
        iLeft. iFrame; auto. 
        iSplitL "Hγ1●". iExists (n'+1); auto.
        iSplitL "Hγ2●". iExists (n'+1); auto.
        iExists (n'+1); iSplitL "Hγ1◯ Hnode1"; iFrame; auto.
        iDestruct "Hnode1" as "[(H1 & Hnode1) | (H1 & Hnode1)]"; iDestruct "H1" as %H1'; inversion H1'; subst.
        iLeft; iSplit; auto.

        iIntros "(_ & Hγ1● & Hγ2● & Hinv)".
        unfold global_inv_locked; unfold node_val_inv; unfold node_lock_inv;
        iDestruct "Hγ1●" as (nlk1) "Hγ1●";
        iDestruct "Hγ2●" as (nlk2) "Hγ2●";
        iDestruct "Hinv" as (n0) "(([(H1 & Hblah1) | (H1 & Hnode1)] & Hγ1◯) & [(H2 & Hblah2) | (H2& Hnode2)] & Hγ2◯)";
        iDestruct "H1" as %H1'; inversion H1'; subst;
        iDestruct "H2" as %H2'; inversion H2'; subst;
        iMod (ghost_var_update γ2 (n'+1) with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]";
        iMod (ghost_var_update γ1 (n'+1) with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]".
        wp_apply (release_spec with "[Hlked2 Hγ2● Hlk2]").
        iFrame; iSplit; auto.
        iIntros; wp_pures.
        wp_apply (release_spec with "[Hlk1 Hγ1● Hlked1]").
        iFrame; iSplit; auto.
        iIntros; wp_pures.
        iApply "HPost"; iSplit; auto; iFrame; iSplit; auto.
        iExists (n'+1); auto.
        iFrame; auto.
        iSplitL "Hnode1"; auto.
    - wp_apply (update_node_some_spec with "[Hnode1 Hγ1◯ Hγ1●]").
      iFrame. unfold node_lock_inv. iSplitL "Hγ1●"; auto.
      unfold node_lock_inv; unfold node_val_inv.
      iIntros "(Hγ1● & H1)". iDestruct "H1" as "(Hnode1 & Hγ1◯)". wp_let; wp_pures.

      wp_apply (update_node_none_spec with "[Hblah2 Hγ2◯ Hγ2●]").
      iFrame. unfold node_lock_inv. iSplitL "Hγ2●"; auto. 
      unfold node_lock_inv; unfold node_val_inv.
      iIntros "(Hγ2● & H2)". iDestruct "H2" as (n0) "(Hnode2 & Hγ2◯)". wp_let; wp_pures.
        iDestruct "Hγ1●" as (n3') "Hγ1●";
        iDestruct "Hγ2●" as (n4') "Hγ2●".
        iMod (ghost_var_update γ1 (n'+1) with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]";
        iMod (ghost_var_update γ2 (n'+1) with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".

      wp_apply ((recover_replicas_one_dead_spec (n'+1) γ1 γ2)
                            with "[- HPost Hlked1 Hlked2 ]").
      iSplit; auto; unfold global_inv_locked; unfold node_val_inv; unfold node_lock_inv.
      iPureIntro; omega.
        iRight. iFrame; auto. 
        iSplitL "Hγ1●". iExists (n'+1); auto.
        iSplitL "Hγ2●". iExists (n'+1); auto.
        iExists (n'+1); iSplitL "Hγ1◯ Hnode1"; iFrame; auto.
        iDestruct "Hnode2" as "[(H2 & Hnode2)| (H2 & Hnode2)]"; iDestruct "H2" as %H2'; inversion H2'; subst.
        iLeft; iSplit; auto.

        iIntros "(_ & Hγ1● & Hγ2● & Hinv)".
        unfold global_inv_locked; unfold node_val_inv; unfold node_lock_inv;
        iDestruct "Hγ1●" as (nlk1) "Hγ1●";
        iDestruct "Hγ2●" as (nlk2) "Hγ2●";
        iDestruct "Hinv" as (n5) "(([(H1 & Hblah1) | (H1 & Hnode1)] & Hγ1◯) & [(H2 & Hblah2) | (H2& Hnode2)] & Hγ2◯)";
        iDestruct "H1" as %H1'; inversion H1'; subst;
        iDestruct "H2" as %H2'; inversion H2'; subst;
        iMod (ghost_var_update γ2 (n'+1) with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]";
        iMod (ghost_var_update γ1 (n'+1) with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]".
        wp_apply (release_spec with "[Hlked2 Hγ2● Hlk2]").
        iFrame; iSplit; auto.
        iIntros; wp_pures.
        wp_apply (release_spec with "[Hlk1 Hγ1● Hlked1]").
        iFrame; iSplit; auto.
        iIntros; wp_pures.
        iApply "HPost"; iSplit; auto; iFrame; iSplit; auto.
        iExists (n'+1); auto.
        iFrame; auto.
        iSplitL "Hnode1"; auto.
  Qed.

  Lemma update_replicas_both_dead_spec : ∀ (n: Z) γ1 γ2 γ3 γ4 lk1 lk2 node1 node2,
      {{{
           global_inv node1 node2 (None) (None) γ1 γ2 γ3 γ4 lk1 lk2
    }}}
      update_replicas #node1 #node2 lk1 lk2
    {{{ RET #();
           global_inv node1 node2 (Some 0) (Some 0) γ1 γ2 γ3 γ4 lk1 lk2
    }}}.
  Proof.
    iIntros (n γ1 γ2 γ3 γ4 lk1 lk2 node1 node2 ϕ) "(#Hlk1 & #Hlk2 & Hinv) HPost".
      iDestruct "Hinv" as (n') "(([(H1 & Hblah1) | (H1 & Hnode1)] & Hγ1◯) & [(H2 & Hblah2) | (H2& Hnode2)] & Hγ2◯)";
      unfold global_inv; unfold node_val_inv; unfold node_lock_inv;
        iDestruct "H1" as %H1; inversion H1; subst;
        iDestruct "H2" as %H2; inversion H2; subst;
          unfold update_replicas;
      wp_pures; 
      wp_apply (acquire_spec with "Hlk1");
      iIntros "(Hlked1 & Hγ1●)"; wp_pures;
      wp_apply (acquire_spec with "Hlk2");
      iIntros "(Hlked2 & Hγ2●)"; wp_pures;
        iDestruct "Hγ1●" as (n1') "Hγ1●";
        iDestruct "Hγ2●" as (n2') "Hγ2●";
        iMod (ghost_var_update γ1 0 with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]";
        iMod (ghost_var_update γ2 0 with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".

    wp_apply (update_node_none_spec with "[Hblah1 Hγ1◯ Hγ1●]").
    unfold node_val_inv; unfold node_lock_inv.
    iSplitL "Hγ1●"; auto.
    iSplitR "Hγ1◯"; auto.

    unfold node_lock_inv; unfold node_val_inv.
    iIntros "(Hγ1● & Hinv)". iDestruct "Hinv" as (n0) "(Hnode1 & Hγ1◯)".
    wp_apply (update_node_none_spec with "[Hblah2 Hγ2◯ Hγ2●]").
    unfold node_val_inv; unfold node_lock_inv.
    iFrame; auto.
    iSplitL "Hγ2●"; auto.

    iIntros "(Hγ2● & Hinv)". iDestruct "Hinv" as (n2) "(Hnode2 & Hγ2◯)".
    wp_let; wp_pures.
    iDestruct "Hγ1●" as (nah1) "Hγ1●";
    iDestruct "Hγ2●" as (nah2) "Hγ2●".
    iMod (ghost_var_update γ1 (0) with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]";
    iMod (ghost_var_update γ2 (0) with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".

    wp_apply ((recover_replicas_both_dead_spec 0 γ1 γ2)
                with "[- HPost Hlked1 Hlked2]").
    iFrame; unfold global_inv_locked; unfold node_lock_inv; unfold node_val_inv; auto.
    iSplitL "Hγ1●"; auto.
    iSplitL "Hγ2●"; auto.
    iExists 0; iSplitL "Hγ1◯ Hnode1"; iFrame; auto.
    iLeft; auto.
    iDestruct "Hnode1" as "[(H1 & Hnode1) | (H1 & Hnode1)]"; iDestruct "H1" as %H1'; inversion H1'; subst. iSplit; auto.
    iLeft; auto.
    iDestruct "Hnode2" as "[(H2 & Hnode2) | (H2 & Hnode2)]"; iDestruct "H2" as %H2'; inversion H2'; subst.
    iSplit; auto.

    iIntros "(Hγ1● & Hγ2● & Hown)".
    unfold global_inv_locked; unfold node_val_inv; unfold node_lock_inv.
    iDestruct "Hown" as (n1) "(([(H1' & Hbar1) | (H1' & Hbar1)] & Hγ1◯) & [(H2' & Hbar2) | (H2' & Hbar2)] & Hγ2◯)";
    iDestruct "Hγ1●" as (n3) "Hγ1●";
    iDestruct "Hγ2●" as (n4) "Hγ2●";
    iDestruct "H1'" as %H1'; inversion H1'; subst;
    iDestruct "H2'" as %H2'; inversion H2'; subst.
    iMod (ghost_var_update γ1 (0) with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]";
    iMod (ghost_var_update γ2 (0) with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".
    unfold node_lock_inv.
    wp_pures.

    wp_apply (release_spec with "[Hlked2 Hγ2● Hlk2]").
    iFrame; iSplit; auto.
    iIntros; wp_pures.
    wp_apply (release_spec with "[Hlk1 Hγ1● Hlked1]").
    iFrame; iSplit; auto.
    iIntros; wp_pures.
    iApply "HPost"; iSplit; auto; iFrame; iSplit; auto.
    iExists 0; auto.
    iFrame; auto.
    iSplitL "Hbar1"; auto.
  Qed.
End proof.
