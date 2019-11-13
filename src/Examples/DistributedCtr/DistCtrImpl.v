From iris.algebra Require Import auth frac_auth excl.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode notation lib.par lib.spin_lock.

Definition alloc : val := λ: "()",
  let: "master" := ref #0 in
  let: "backup" := ref #0 in
  let: "lk" := newlock #() in
  Pair (Pair (SOME "master") (SOME "backup")) "lk".

Definition update_replica: val :=
  λ: "replica1" "replica2",
  match: "replica1" with
    SOME "r1" => 
     match: "replica2" with
       SOME "r2" => 
            "r1" <- !"r1" + #1;;
            "r2" <- !"r2" + #1
       | NONE =>                       
            "r1" <- !"r1" + #1;;
            "r2" <- !"r1"
     end
  | NONE =>
    match: "replica2" with
       SOME "r2" => 
            "r2" <- !"r2" + #1;;
            "r1" <- !"r2"
    | NONE => #()
    end
   end.

Definition get_replica: val :=
  λ: "replica1" "replica2",
  match: "replica1" with
    SOME "r1" => !"r1"
    | NONE => 
     match: "replica2" with
       SOME "r2" => 
            !"r2"
       | NONE => #()
     end
  end.

Definition update: val :=
  λ: "master" "backup" "lk",
  acquire "lk";;
  update_replica "master";;
  update_replica "backup";;
  release "lk".

Definition get : val :=
  λ: "master" "backup" "lk",
  acquire "lk";;
  get_replica "master" "backup";;
  release "lk";;
  "r".

Section proof.
  (** Come up with a suitable invariant and prove the spec **)
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

  Definition parallel_inc_inv (n1 n2 : Z) (rpair : loc * loc) (γ1 γ2 : gname) : iProp Σ :=
    ⌜#n1 = #n2⌝
    ∗ (fst rpair) ↦ #(n1)
    ∗ (snd rpair) ↦ #(n2)
    ∗ own γ1 (● (Excl' n1)) ∗ own γ2 (● (Excl' n2))%I.
    (* we need these to tell the value of n1 and n2 *)

  (* Notes: loc = kind of like a Coq literal number, LitV (LitLoc loc) is an actual value in the language *)

  Definition value_duplicated (n : Z) (r1 r2 : loc) (lk: val) : iProp Σ := ∃ (γ γ1 γ2 : gname), 
    is_lock LockN γ lk (parallel_inc_inv n n (r1, r2) γ1 γ2) ∗ own γ1 (◯ (Excl' n)) ∗ own γ2 (◯ (Excl' n)).

  Lemma alloc_spec : 
    {{{ True%I }}}
      alloc #()
    {{{ r1 r2 lk, RET PairV (PairV #r1 #r2) lk;
        value_duplicated 0 r1 r2 lk 
    }}}.
  Proof.
    iIntros (Φ) "_ HPost".
    iMod (ghost_var_alloc 0) as (γ1) "[Hγ1● Hγ1◯]".
    iMod (ghost_var_alloc 0) as (γ2) "[Hγ2● Hγ2◯]".

    unfold alloc.
    wp_alloc r1 as "Hr1".
    wp_alloc r2 as "Hr2"; wp_let.
 
    wp_apply (newlock_spec LockN (parallel_inc_inv 0 0 (r1, r2) γ1 γ2) with "[Hr1 Hr2 Hγ1● Hγ2●]").
    unfold parallel_inc_inv; iFrame; auto.

    iIntros (lk γ) "HIsLk".
    wp_let.
    wp_pures.
    iApply "HPost". unfold value_duplicated. 
    iExists γ, γ1, γ2. iFrame; auto.
  Qed.

  Lemma inc_spec : ∀ n r1 r2 lk, (*should γ be forall? *)
    {{{ value_duplicated n r1 r2 lk }}}
      inc (#r1, #r2) lk
    {{{ RET #() ; value_duplicated (n+1) r1 r2 lk }}}.
  Proof.
    iIntros (n r1 r2 lk ϕ) "Hvaldup Hϕ".
    unfold inc.
    wp_pures.
    unfold value_duplicated in *.
    iDestruct "Hvaldup" as (γ γ1 γ2) "[Hislk [Hγ1◯ Hγ2◯]]".
    wp_apply (acquire_spec with "[Hislk]"). iApply "Hislk".
    iIntros "(Hlked & HInv)".
    wp_pures.
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
      wp_apply ((release_spec LockN γ lk (parallel_inc_inv (n+1) (n+1) (r1, r2) γ1 γ2)) with "[Hlked Hγ1◯ Hγ2◯]").

      auto.
  Admitted.

  Lemma sum_spec : ∀ n rpair lpair,
    {{{ pair_eq n rpair }}}
      sum (#(fst rpair), #(snd rpair)) lpair
    {{{ z, RET #z; ⌜ z = (n + n)%Z ⌝ }}}.
  Proof.
  Admitted.
End proof.
