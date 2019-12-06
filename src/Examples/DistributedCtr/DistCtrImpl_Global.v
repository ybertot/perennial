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
    iIntros (n γ1 γ2 node1 node2 ϕ) "(Hγ1● & Hγ2● & Hinv) HPost".
    unfold global_inv_locked; unfold node_val_inv; unfold node_lock_inv;
    iDestruct "Hγ1●" as (nlk1) "Hγ1●";
    iDestruct "Hγ2●" as (nlk2) "Hγ2●";
    iDestruct "Hinv" as (n') "(([(H1 & Hblah1) | (H1 & Hnode1)] & Hγ1◯) & [(H2 & Hblah2) | (H2& Hnode2)] & Hγ2◯)";
    iDestruct "H1" as %H1; inversion H1; subst;
      iDestruct "H2" as %H2; inversion H2; subst;
      iMod (ghost_var_update γ2 0 with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]";
      iMod (ghost_var_update γ1 0 with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]".
    unfold recover_replicas.
    wp_pures. wp_load; wp_pures. wp_load; wp_pures.
    wp_store; wp_store.
    iApply "HPost". iFrame.
    iSplitL "Hγ1●"; auto.
    iSplitL "Hγ2●"; auto.
    iExists 0; iSplitL "Hγ1◯ Hblah1"; iFrame; auto.
  Qed.

  Lemma get_replicas_one_alive_spec : ∀ (n: Z) γ1 γ2 γ3 γ4 lk1 lk2 node1 node2,
      {{{
          ⌜ ~n < 0 ⌝
           ∗ (global_inv_unlocked node1 node2 (Some n) (Some n) γ1 γ2 γ3 γ4 lk1 lk2
            ∨ global_inv_unlocked node1 node2 None(Some n) γ1 γ2 γ3 γ4 lk1 lk2
            ∨ global_inv_unlocked node1 node2 (Some n) None γ1 γ2 γ3 γ4 lk1 lk2)
    }}}
      get_replicas #node1 #node2 lk1 lk2
    {{{ RET #n;
          ⌜ ~n < 0 ⌝
        ∗ global_inv_unlocked node1 node2 (Some (n)) (Some (n)) γ1 γ2 γ3 γ4 lk1 lk2
    }}}.
  Proof.
    iIntros (n γ1 γ2 γ3 γ4 lk1 lk2 node1 node2 ϕ) "(Hn & [(#Hlk1 & #Hlk2 & Hinv) | [(#Hlk1 & #Hlk2 & Hinv) | (#Hlk1 & #Hlk2 & Hinv)]]) HPost";
      iDestruct "Hn" as %Hn;
      iDestruct "Hinv" as (n') "(([(H1 & Hblah1) | (H1 & Hnode1)] & Hγ1◯) & [(H2 & Hblah2) | (H2& Hnode2)] & Hγ2◯)";
      unfold global_inv_unlocked; unfold node_val_inv; unfold node_lock_inv;
        iDestruct "H1" as %H1; inversion H1; subst;
        iDestruct "H2" as %H2; inversion H2; subst;
          unfold get_replicas;
      wp_pures; 
      wp_apply (acquire_spec with "Hlk1");
      iIntros "(Hlked1 & Hγ1●)"; wp_pures;
      wp_apply (acquire_spec with "Hlk2");
      iIntros "(Hlked2 & Hγ2●)"; wp_pures;
        iDestruct "Hγ1●" as (n1') "Hγ1●";
        iDestruct "Hγ2●" as (n2') "Hγ2●";
        iMod (ghost_var_update γ1 (n') with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]";
        iMod (ghost_var_update γ2 (n') with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".

      - wp_apply ((recover_replicas_both_alive_spec n' γ1 γ2)
                        with "[- HPost Hlked1 Hlked2]").
        unfold global_inv_locked; unfold node_val_inv; unfold node_lock_inv.
        iSplit; auto.
        iFrame. 
        iSplitL "Hγ1●". iExists n'; auto.
        iSplitL "Hγ2●". iExists n'; auto. iExists n'; iSplitL "Hγ1◯ Hnode1"; iFrame; iRight; iSplit ; auto.

        iIntros "(_ & Hγ1● & Hγ2● & Hown)".
        unfold global_inv_locked; unfold node_val_inv; unfold node_lock_inv.
        iDestruct "Hown" as (n1) "(([(H1' & Hbar1) | (H1' & Hbar1)] & Hγ1◯) & [(H2' & Hbar2) | (H2' & Hbar2)] & Hγ2◯)";
        iDestruct "Hγ1●" as (n3) "Hγ1●";
        iDestruct "Hγ2●" as (n4) "Hγ2●";
        iDestruct "H1'" as %H1'; inversion H1'; subst;
        iDestruct "H2'" as %H2'; inversion H2'; subst.
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
        iSplitL "Hbar1"; auto.

      - wp_apply ((recover_replicas_one_dead_spec n' γ1 γ2)
                            with "[- HPost Hlked1 Hlked2 ]").
        iSplit; auto; unfold global_inv_locked; unfold node_val_inv; unfold node_lock_inv.
        iLeft. iFrame; auto. 
        iSplitL "Hγ1●". iExists n'; auto.
        iSplitL "Hγ2●". iExists n'; auto.
        iExists n'; iSplitL "Hγ1◯ Hblah1"; iFrame; auto.

        iIntros "(_ & Hγ1● & Hγ2● & Hown)".
        unfold global_inv_locked; unfold node_val_inv; unfold node_lock_inv.
        iDestruct "Hown" as (n1) "(([(H1' & Hbar1) | (H1' & Hbar1)] & Hγ1◯) & [(H2' & Hbar2) | (H2' & Hbar2)] & Hγ2◯)";
        iDestruct "Hγ1●" as (n3) "Hγ1●";
        iDestruct "Hγ2●" as (n4) "Hγ2●";
        iDestruct "H1'" as %H1'; inversion H1'; subst;
        iDestruct "H2'" as %H2'; inversion H2'; subst.
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
        iSplitL "Hbar1"; auto.
        
      - wp_apply ((recover_replicas_one_dead_spec n' γ1 γ2)
                            with "[- HPost Hlked1 Hlked2 ]").
        iSplit; auto;
          unfold global_inv_locked; unfold node_val_inv; unfold node_lock_inv.
        iRight. iFrame; auto. 
        iSplitL "Hγ1●". iExists n'; auto.
        iSplitL "Hγ2●". iExists n'; auto.
        iExists n'; iSplitR "Hγ2◯ Hblah2"; iFrame; auto.

        iIntros "(_ & Hγ1● & Hγ2● & Hown)".
        unfold global_inv_locked; unfold node_val_inv; unfold node_lock_inv.
        iDestruct "Hown" as (n1) "(([(H1' & Hbar1) | (H1' & Hbar1)] & Hγ1◯) & [(H2' & Hbar2) | (H2' & Hbar2)] & Hγ2◯)";
        iDestruct "Hγ1●" as (n3) "Hγ1●";
        iDestruct "Hγ2●" as (n4) "Hγ2●";
        iDestruct "H1'" as %H1'; inversion H1'; subst;
        iDestruct "H2'" as %H2'; inversion H2'; subst.
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
        iSplitL "Hbar1"; auto.
  Qed.
  
  Lemma get_replicas_both_dead_spec : ∀ γ1 γ2 γ3 γ4 lk1 lk2 node1 node2,
      {{{
           global_inv_unlocked node1 node2 None None γ1 γ2 γ3 γ4 lk1 lk2
    }}}
      get_replicas #node1 #node2 lk1 lk2
    {{{ RET #0;
           global_inv_unlocked node1 node2 (Some 0) (Some 0) γ1 γ2 γ3 γ4 lk1 lk2
    }}}.
  Proof.
    iIntros (γ1 γ2 γ3 γ4 lk1 lk2 node1 node2 ϕ) "(#Hlk1 & #Hlk2 & Hinv) HPost";
      iDestruct "Hinv" as (n') "(([(H1 & Hblah1) | (H1 & Hnode1)] & Hγ1◯) & [(H2 & Hblah2) | (H2& Hnode2)] & Hγ2◯)";
      unfold global_inv_unlocked; unfold node_val_inv; unfold node_lock_inv;
        iDestruct "H1" as %H1; inversion H1; subst;
        iDestruct "H2" as %H2; inversion H2; subst;
          unfold get_replicas;
      wp_pures; 
      wp_apply (acquire_spec with "Hlk1");
      iIntros "(Hlked1 & Hγ1●)"; wp_pures;
      wp_apply (acquire_spec with "Hlk2");
      iIntros "(Hlked2 & Hγ2●)"; wp_pures;
        iDestruct "Hγ1●" as (n1') "Hγ1●";
        iDestruct "Hγ2●" as (n2') "Hγ2●";
        iMod (ghost_var_update γ1 n' with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]";
        iMod (ghost_var_update γ2 n' with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".

    wp_apply ((recover_replicas_both_dead_spec n' γ1 γ2)
                with "[- HPost Hlked1 Hlked2]");
    iFrame. 
    iSplitL "Hγ1●". iExists n'; auto.
    iSplitL "Hγ2●". iExists n'; auto.
    unfold global_inv_unlocked; unfold node_lock_inv; unfold node_val_inv; auto.
    iExists n'; iSplitL "Hγ1◯ Hblah1". iFrame; auto. iFrame; auto.

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
    wp_let; wp_pures.

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

   Lemma update_replicas_one_alive_spec : ∀ (n: Z) γ1 γ2 γ3 γ4 lk1 lk2 node1 node2,
    {{{
          ⌜ ~n < 0 ⌝
           ∗ (global_inv_unlocked node1 node2 (Some n) (Some n) γ1 γ2 γ3 γ4 lk1 lk2
                ∨ global_inv_unlocked node1 node2 None(Some n) γ1 γ2 γ3 γ4 lk1 lk2
                ∨ global_inv_unlocked node1 node2 (Some n) None γ1 γ2 γ3 γ4 lk1 lk2)
    }}}
      update_replicas #node1 #node2 lk1 lk2
    {{{ RET #();
        global_inv_unlocked node1 node2 (Some (n+1)) (Some (n+1)) γ1 γ2 γ3 γ4 lk1 lk2
    }}}.
   Proof.
    iIntros (n γ1 γ2 γ3 γ4 lk1 lk2 node1 node2 ϕ) "(Hn & [(#Hlk1 & #Hlk2 & Hinv) | [(#Hlk1 & #Hlk2 & Hinv) | (#Hlk1 & #Hlk2 & Hinv)]]) HPost";
      iDestruct "Hn" as %Hn;
      iDestruct "Hinv" as (n') "(([(H1 & Hblah1) | (H1 & Hnode1)] & Hγ1◯) & [(H2 & Hblah2) | (H2& Hnode2)] & Hγ2◯)";
      unfold global_inv_unlocked; unfold node_val_inv; unfold node_lock_inv;
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
           global_inv_unlocked node1 node2 (None) (None) γ1 γ2 γ3 γ4 lk1 lk2
    }}}
      update_replicas #node1 #node2 lk1 lk2
    {{{ RET #();
           global_inv_unlocked node1 node2 (Some 0) (Some 0) γ1 γ2 γ3 γ4 lk1 lk2
    }}}.
  Proof.
    iIntros (n γ1 γ2 γ3 γ4 lk1 lk2 node1 node2 ϕ) "(#Hlk1 & #Hlk2 & Hinv) HPost".
      iDestruct "Hinv" as (n') "(([(H1 & Hblah1) | (H1 & Hnode1)] & Hγ1◯) & [(H2 & Hblah2) | (H2& Hnode2)] & Hγ2◯)";
      unfold global_inv_unlocked; unfold node_val_inv; unfold node_lock_inv;
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
    iDestruct "Hnode2" as "[(H2 & Hnode2) | (H2 & Hnode2)]"; iDestruct "H2" as %H2'; inversion H2'; subst. iSplit; auto.

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
