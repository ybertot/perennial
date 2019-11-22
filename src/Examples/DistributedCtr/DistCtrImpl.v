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
                        "r" <- #1
  | NONE => "node" <- SOME #0;;
                   "r" <- #0
  end;;
  "r".

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
                         "r" <- "v1"
    | NONE => match: !"node2" with
                SOME "v2" => "node1" <- "v2";;
                               "r" <- "v2"
              | NONE => "node1" <- SOME #0;;
                                "node2" <- SOME #0;;
                                "r" <- #0
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

  Lemma update_replica_some_spec : ∀ n master backup lk v1 v2 γ γ1 γ2,
      {{{
           lock_inv lk γ γ1 γ2
           ∗ value_duplicated_inv n (Some v1) (Some v2) γ1 γ2
           ∗ master ↦ SOMEV #v1
           ∗ backup ↦ SOMEV #v2
      }}}
        update_replicas #master #backup lk
      {{{ RET Pair #master #backup; 
           lock_inv lk γ γ1 γ2
           ∗ value_duplicated_inv (n+1) (Some (v1+1)) (Some (v2+1)) γ1 γ2
           ∗ master ↦ SOMEV #(v1 + 1)
           ∗ backup ↦ SOMEV #(v2 + 1)
      }}}.
  Proof.
    iIntros (n master backup lk v1 v2 γ γ1 γ2 ϕ) "Hvaldup Hϕ".
    unfold update_replicas.
    iDestruct "Hvaldup" as "(#Hlk & HInv & Hm & Hb)".
    unfold value_duplicated_inv.
    iDestruct "HInv" as "[Hv1 [Hγ1◯ [Hv2 Hγ2◯]]]".

    wp_pures.
    wp_apply (acquire_spec with "Hlk").
    iIntros "(Hlked & HInv)".
    iDestruct "HInv" as (n') "(Hγ1● & Hγ2● )".
    iDestruct (ghost_var_agree with "Hγ1● Hγ1◯") as %->.
    iMod (ghost_var_update γ1 (n+1) with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]";
    iMod (ghost_var_update γ2 (n+1) with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".
    wp_pures.
    wp_load. wp_match. wp_store. wp_store.
    wp_apply (release_spec LockN γ lk (update_val_inv γ1 γ2) with "[- $Hlked Hγ1◯ Hγ2◯ Hv1 Hv2 Hm Hb Hϕ]").
    iSplit; auto. unfold update_val_inv.
    iExists (n+1). iFrame; auto.
    iIntros. wp_pures.
    unfold lock_inv.
    iDestruct "Hϕ" as (
    iApply "Hϕ".
      iExists γ, γ1, γ2; iFrame; auto.
  Qed.

  Lemma update_replica_some_none_spec : ∀ n master backup lk (r1: loc),
      {{{ ⌜ (master = SOMEV #r1 ∧ backup = NONEV) ⌝
            ∗ value_duplicated n (Some r1) None lk
      }}}
      update_replica master backup lk
      {{{ nr1 nr2, RET (SOMEV #nr1, SOMEV #nr2) ;
          value_duplicated (n+1) (Some nr1) None lk (* XXX: How can I make this be Some nr1 and Some nr2? *)
      }}}.
  Proof.
    iIntros (n master backup lk r1 ϕ) "Hvaldup Hϕ".
    unfold update_replica.
    iDestruct "Hvaldup" as ([-> ->]) "HInv";
      iDestruct "HInv" as (γ γ1 γ2) "[#Hislk [Hγ1◯ Hγ2◯]]";
      wp_pures;
      wp_apply (acquire_spec with "[$Hislk]");
      iIntros "(Hlked & HInv)";
      wp_pures;
    iDestruct "HInv" as (n' nloc) "(Hr1 & Hr2 & Hγ1● & Hγ2● )";
        iDestruct (ghost_var_agree with "Hγ1● Hγ1◯") as %->;
        iMod (ghost_var_update γ1 (n+1) with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]";
        iMod (ghost_var_update γ2 (n+1) with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".
    wp_load; wp_op; wp_store; wp_match; wp_alloc nr2 as "Hnr2"; wp_let; wp_load; wp_store.
    wp_apply (release_spec LockN γ lk (update_inv (Some r1) None γ1 γ2) with "[- $Hlked Hγ1◯ Hγ2◯ Hϕ]").
    iSplit; auto.
    iExists (n + 1), nr2. iFrame; auto. 
    iIntros. wp_pures.
    iApply "Hϕ".
    iExists γ, γ1, γ2; iFrame; auto.
  Qed.

  Lemma update_replica_none_some_spec : ∀ n master backup lk (r1 r2 : loc),
      {{{ 
           ⌜ (master = NONEV ∧ backup = SOMEV #r1) ⌝
             ∗ value_duplicated n None (Some r1) lk
      }}}
      update_replica master backup lk
      {{{ nr1 nr2, RET (SOMEV #nr1, SOMEV #nr2) ;
          value_duplicated (n+1) None (Some nr2) lk (* XXX: How can I make this be Some nr1 and Some nr2? *)
      }}}.
  Proof.
    iIntros (n master backup lk r1 r2 ϕ) "Hvaldup Hϕ".
    unfold update_replica.
    iDestruct "Hvaldup" as ([-> ->]) "HInv".
    iDestruct "HInv" as (γ γ1 γ2) "[#Hislk [Hγ1◯ Hγ2◯]]";
      wp_pures;
      wp_apply (acquire_spec with "[$Hislk]");
      iIntros "(Hlked & HInv)";
      wp_pures.
    iDestruct "HInv" as (n' nloc) "(Hr1 & Hr2 & Hγ1● & Hγ2● )";
        iDestruct (ghost_var_agree with "Hγ1● Hγ1◯") as %->;
        iMod (ghost_var_update γ1 (n+1) with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]";
        iMod (ghost_var_update γ2 (n+1) with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".
    - wp_alloc nr2 as "Hnr2"; wp_let; wp_load; wp_store.
      wp_load; wp_store.
      wp_apply (release_spec LockN γ lk (update_inv None (Some r1) γ1 γ2) with "[- $Hlked Hγ1◯ Hγ2◯ Hϕ]").
      iSplit; auto.
      iExists (n + 1), nr2. iFrame; auto. 
      iIntros. wp_pures.
      iApply "Hϕ".
      iExists γ, γ1, γ2; iFrame; auto.
  Qed.
 
  Lemma update_replica_none_spec : ∀ master backup lk, 
      {{{ ⌜ master = NONE ∧ backup = NONE ⌝
           ∗ value_duplicated 0 None None lk }}}
      update_replica master backup lk
      {{{ r1 r2, RET (SOMEV #r1, SOMEV #r2) ;
          value_duplicated (0) None None lk
          (*XXX I want to say value_duplicated (0) (Some r1) (Some r2) lk, but I can't because
             the lock invariant can't be changed
           *)
      }}}.
  Proof.
    iIntros (master backup lk ϕ) "Hvaldup Hϕ".
    unfold update_replica.
    wp_pures.
    iDestruct "Hvaldup" as ([-> ->]) "HInv".
    unfold value_duplicated in *.
    iDestruct "HInv" as (γ γ1 γ2) "[#Hislk [Hγ1◯ Hγ2◯]]".

    wp_apply (acquire_spec with "[$Hislk]").
    iIntros "(Hlked & HInv)".
    wp_pures.

    iDestruct "HInv" as (n' nloc nloc2) "(Hnloc1 & Hnloc2 & Hγ1● & Hγ2● )";
      iDestruct (ghost_var_agree with "Hγ1● Hγ1◯") as %->.

    wp_alloc r1 as "Hr1". 
    wp_alloc r2 as "Hr2".
    wp_apply (release_spec LockN γ lk (update_inv None None γ1 γ2) with "[- $Hlked Hγ1◯ Hγ2◯ Hϕ]").
    iSplit; auto. unfold update_inv.
    iExists 0, nloc, nloc2. iFrame; auto.
    iIntros. wp_pures.
    iApply "Hϕ".
    iExists γ, γ1, γ2; iFrame; auto.
  Qed.
End proof.
