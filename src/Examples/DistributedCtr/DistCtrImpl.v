From iris.algebra Require Import auth frac_auth excl.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode notation lib.par lib.spin_lock.

Definition alloc : val := λ: "()",
  let: "master" := ref #0 in
  let: "backup" := ref #0 in
  let: "lk" := newlock #() in
  Pair (Pair (SOME "master") (SOME "backup")) "lk".

Definition update_replica: val :=
  λ: "replica1" "replica2" "lk",
  acquire "lk";;
  match: "replica1" with
    SOME "r1" => 
    "r1" <- !"r1" + #1;;
    match: "replica2" with
      SOME "r2" => "r2" <- !"r2" + #1;;
        release "lk";;
        Pair (SOME "r1") (SOME "r2")
    | NONE =>
      let: "r2" := ref #0 in
      "r2" <- !"r1";;
      release "lk";;
      Pair (SOME "r1") (SOME "r2")
     end
  | NONE =>
    match: "replica2" with
    SOME "r2" =>
      let: "r1" := ref #0 in
      "r2" <- !"r1"
         "r2" <- !"r2" + #1;;
        "r1" <- !"r2";;
        release "lk";;
        Pair (SOME "r1") (SOME "r2")
    | NONE => "r1" <- ref #0;; "r2" <- ref #0
        release "lk";;
        Pair (SOME "r1") (SOME "r2")
    end
  end.

Definition get_replica: val :=
  λ: "replica1" "replica2" "lk",
  acquire "lk";;
  match: "replica1" with
    SOME "r1" => "r" <- !"r1"
    | NONE => 
      match: "replica2" with
        SOME "r2" => 
        let: "r1" := ref #0 in
        "r" <- !"r2";;
        "r1" <- !"r2";;
        release "lk";;
        Pair (Pair (SOME "r1") (SOME "r2")) "r"
       | NONE => "r1" <- ref #0;; "r2" <- ref #0
        release "lk";;
        Pair (Pair (SOME "r1") (SOME "r2")) "r"
     end
  end.

(* wrappers, not doing much right now. can we hide backup from the client? *)
Definition update: val :=
  λ: "master" "backup" "lk",
  update_replica "master" "backup".

Definition get : val :=
  λ: "master" "backup" "lk",
  get_replica "master" "backup".

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
    own γ (● (Excl' n)) -∗ own γ (◯ (Excl' m)) -∗ ⌜ n = m ⌝.
  Proof.
    iIntros "Hγ● Hγ◯".
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

  Definition update_inv (mloc bloc : option loc) (γ1 γ2 : gname) : iProp Σ := ∃ n : Z,
      match mloc, bloc with
      | Some m, Some b => m ↦ #(n) ∗ b ↦ #(n) ∗ own γ1 (● (Excl' n)) ∗ own γ2 (● (Excl' n))%I
      | Some m, None => ∃ nloc, m ↦ #(n) ∗ nloc ↦ #(n) ∗ own γ1 (● (Excl' n)) ∗ own γ2 (● (Excl' n))%I
      | None, Some b => ∃ nloc, nloc ↦ #(n) ∗ b ↦ #(n) ∗ own γ1 (● (Excl' n)) ∗ own γ2 (● (Excl' n))%I
      | None, None => ∃ nloc1 nloc2, nloc1 ↦ #(n) ∗ nloc2 ↦ #(n) ∗ own γ1 (● (Excl' n)) ∗ own γ2 (● (Excl' n))%I
      end.
    (* we need these to tell the value of n *)

  (* Notes: loc = kind of like a Coq literal number, LitV (LitLoc loc) is an actual value in the language *)

  Definition value_duplicated (n : Z) (r1 r2 : option loc) (lk: val) : iProp Σ := ∃ (γ γ1 γ2 : gname), 
    is_lock LockN γ lk (update_inv r1 r2 γ1 γ2) ∗ own γ1 (◯ (Excl' n)) ∗ own γ2 (◯ (Excl' n)).

  Lemma alloc_spec : 
    {{{ True%I }}}
      alloc #()
    {{{ r1 r2 lk, RET PairV (PairV (SOMEV #r1) (SOMEV #r2)) lk;
        value_duplicated 0 (Some r1) (Some r2) lk
    }}}.
  Proof.
    iIntros (Φ) "_ HPost".
    iMod (ghost_var_alloc 0) as (γ1) "[Hγ1● Hγ1◯]".
    iMod (ghost_var_alloc 0) as (γ2) "[Hγ2● Hγ2◯]".

    unfold alloc.
    wp_alloc master as "Hr1".
    wp_alloc backup as "Hr2"; wp_let.
 
    wp_apply (newlock_spec LockN (update_inv (Some master) (Some backup) γ1 γ2) with "[Hr1 Hr2 Hγ1● Hγ2●]").
    unfold update_inv; iFrame; auto.

    iExists 0. iFrame; auto.
    iIntros (lk γ) "HIsLk".
    wp_let.
    wp_pures.
    iApply "HPost". unfold value_duplicated.
    iExists γ, γ1, γ2. iFrame; auto.
  Qed.

  Lemma update_replica_some_spec : ∀ n master backup lk (r1 r2 : loc),
      {{{ ⌜ (master = SOMEV #r1 ∧ backup = SOME #r2)
          ∨ (master = SOMEV #r1 ∧ backup = NONEV)
          ∨ (backup = SOMEV #r2 ∧ master = NONEV) ⌝
          ∗ value_duplicated n r1 r2 lk

      }}}
      update_replica master backup lk
      {{{ nr1 nr2, RET (SOMEV #nr1, SOMEV #nr2) ;
          value_duplicated (n+1) nr1 nr2 lk
      }}}.
  Proof.
    iIntros (n master backup lk r1 r2 ϕ) "Hvaldup Hϕ".
    unfold update_replica.
    iDestruct "Hvaldup" as ([[-> ->] | [[-> ->] | [-> ->]]]) "HInv";
      iDestruct "HInv" as (γ γ1 γ2) "[#Hislk [Hγ1◯ Hγ2◯]]";
      wp_pures;
      wp_apply (acquire_spec with "[$Hislk]");
      iIntros "(Hlked & HInv)";
      wp_pures;
      iDestruct "HInv" as (n') "(Hr1 & Hr2 & Hγ1● & Hγ2● )";
        iDestruct (ghost_var_agree with "Hγ1● Hγ1◯") as %->;
        iMod (ghost_var_update γ1 (n+1) with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]";
        iMod (ghost_var_update γ2 (n+1) with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".
    - wp_load; wp_op; wp_store.
      wp_load; wp_op; wp_store.
      wp_apply (release_spec LockN γ lk (update_inv r1 r2 γ1 γ2) with "[- $Hlked Hγ1◯ Hγ2◯ Hϕ]").
      iSplit; auto. unfold update_inv.
      iExists (n + 1). iFrame; auto.
      iIntros. wp_pures.
      iApply "Hϕ".
      iExists γ, γ1, γ2; iFrame; auto.
    - wp_load; wp_op; wp_store.
      wp_match.
      wp_alloc r3 as "Hr3".
      wp_let.
      wp_load. wp_store.
      wp_load. wp_store.
      wp_load. 
      wp_apply (release_spec LockN γ lk (update_inv r1 r2 γ1 γ2) with "[- $Hlked Hγ1◯ Hγ2◯ Hϕ]").
      iSplit; auto. unfold update_inv.
      iExists (n + 1). iFrame; auto.
      iIntros. wp_pures.
      iApply "Hϕ".
      iExists γ, γ1, γ2; iFrame; auto.

  Qed.
 
  Lemma update_replica_none_spec : ∀ n master backup lk (r1 r2 : loc),
      {{{ ⌜ master = NONE ∧ backup = SOMEV #r2 ⌝ ∗ value_duplicated n r1 r2 lk }}}
      update_replica master backup lk
      {{{ RET (SOMEV #r1, SOMEV #r2) ; value_duplicated (n+1) r1 r2 lk }}}.
  Proof.
    iIntros (n master backup lk r1 r2 ϕ) "Hvaldup Hϕ".
    unfold update_replica.
    wp_pures.
    iDestruct "Hvaldup" as ([-> ->]) "HInv".
    unfold value_duplicated in *.
    iDestruct "HInv" as (γ γ1 γ2) "[#Hislk [Hγ1◯ Hγ2◯]]".

    wp_apply (acquire_spec with "[$Hislk]").
    iIntros "(Hlked & HInv)".
    wp_pures.

    iDestruct "HInv" as (n') "(Hr1 & Hr2 & Hγ1● & Hγ2● )".
    iDestruct (ghost_var_agree with "Hγ1● Hγ1◯") as %->.
    iMod (ghost_var_update γ1 (n+1) with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]".
    iMod (ghost_var_update γ2 (n+1) with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".

    wp_load; wp_op; wp_store.
    wp_load; wp_op; wp_store.
    wp_apply (release_spec LockN γ lk (update_inv r1 r2 γ1 γ2) with "[- $Hlked Hγ1◯ Hγ2◯ Hϕ]").
    iSplit; auto. unfold update_inv.
    iExists (n + 1). iFrame; auto.

    iIntros. wp_pures.
    iApply "Hϕ".
    iExists γ, γ1, γ2; iFrame; auto.
  Qed.
  
  Lemma update_spec : ∀ n r1 r2 lk, (*should γ be forall? *)
    {{{ value_duplicated n r1 r2 lk }}}
      update #r1 #r2 lk
    {{{ RET #() ; value_duplicated (n+1) r1 r2 lk }}}.
  Proof.
    iIntros (n r1 r2 lk ϕ) "Hvaldup Hϕ".
    unfold update.
    wp_pures.
    unfold value_duplicated in *.
    iDestruct "Hvaldup" as (γ γ1 γ2) "[Hislk [Hγ1◯ Hγ2◯]]".
    wp_apply (acquire_spec with "[Hislk]"). iApply "Hislk".
    iIntros "(Hlked & HInv)".
    wp_pures.
    unfold update_replica. wp_pures.
    induction r1.
    induction r1.
    iDestruct #r1 as "HR1". simpl.
    iDestruct "HInv" as "(_ & Hr1 & Hr2 & Hγ1● & Hγ2● )"; simpl in *.
    wp_apply (wp_par (λ _, own γ1 (◯ Excl' (n+1))) (λ _, own γ2 (◯ Excl' (n+1)))
                with "[Hr1 Hγ1◯ Hγ1●] [Hr2 Hγ2◯ Hγ2●]").
    - iMod (ghost_var_update γ1 (n+1) with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]".
      wp_load; wp_op; wp_store; auto.
    - iMod (ghost_var_update γ2 (n+1) with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".
      wp_load; wp_op; wp_store; auto.
    - iIntros (v1 v2) "(Hγ1◯ & Hγ2◯)".
      iNext.
      wp_pures.
      Check release_spec.

      auto.
  Admitted.

  Lemma sum_spec : ∀ n rpair lpair,
    {{{ pair_eq n rpair }}}
      sum (#(fst rpair), #(snd rpair)) lpair
    {{{ z, RET #z; ⌜ z = (n + n)%Z ⌝ }}}.
  Proof.
  Admitted.
End proof.
