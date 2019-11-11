From iris.algebra Require Import auth frac_auth excl.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode notation lib.par lib.spin_lock.

Definition alloc : val :=
  λ: "()",
  let: "r1" := ref #0 in
  let: "r2" := ref #0 in
  let: "lk" := newlock #() in
  Pair (Pair "r1" "r2") "lk".

(* precondition: r1 r2 are an alloced pair *)
Definition inc : val :=
  λ: "rpair" "lk",
  let: "r1" := Fst "rpair" in
  let: "r2" := Snd "rpair" in
  acquire "lk";;
  (("r1" <- !"r1" + #1)
  |||
  ("r2" <- !"r2" + #1))
  release "lk".

Definition sum : val :=
  λ: "rpair" "lk",
  let: "r1" := Fst "rpair" in
  let: "r2" := Snd "rpair" in
  acquire "lk";;
  "r" <-!"r1" + !"r2";;
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
    (* XXX What is this last line doing??? *)
  Qed.

  Lemma ghost_var_update γ n' n m :
    own γ (● (Excl' n)) -∗ own γ (◯ (Excl' m)) ==∗
      own γ (● (Excl' n')) ∗ own γ (◯ (Excl' n')).
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (● Excl' n' ⋅ ◯ Excl' n') with "Hγ● Hγ◯") as "[$$]".
    { apply auth_update. apply option_local_update. apply exclusive_local_update. done. }
    (* ??? *)
    done.
  Qed.

  Definition parallel_inc_inv (n1 n2 : Z) (rpair : loc * loc) (γ1 γ2 : gname) : iProp Σ :=
    ⌜#n1 = #n2⌝
    ∗ (fst rpair) ↦ #(n1)
    ∗ (snd rpair) ↦ #(n2)
    ∗ own γ1 (● (Excl' n1)) ∗ own γ2 (● (Excl' n2))%I.
    (* we need these to tell the value of n1 and n2 *)

  (* Notes: loc = kind of like a Coq literal number, LitV (LitLoc loc) is an actual value in the language *)

  Lemma alloc_spec : 
    {{{ True%I }}}
      alloc #()
      {{{ r1 r2 lk γ1 γ2, RET PairV (PairV #r1 #r2) lk; ∃ γ, is_lock LockN γ lk (parallel_inc_inv 0 0 (r1, r2) γ1 γ2)}}}.
  (* DO I NEED FORALL OR EXISTS GAMMA *)
  (* parallel_inc_inv (r1, r2) ∗ not needed because held in lock? *)
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
    iApply "HPost". iExists γ; auto.
  Qed.

  Lemma inc_spec : ∀ n r1 r2 lk1 lk2 R1 R2 γ, (*should γ be forall? *)
    {{{ is_lock LockN γ lk (parallel_inc_inv(r1, r2)) }}}
      inc (#r1, #r2) lk
    {{{ z, RET #z; pair_eq (n+1) (r1, r2)}}}.
  Proof.
    iIntros (n r1 r2 lk1 lk2 ϕ) "HPair Hϕ".
    unfold inc.
    unfold pair_eq in *.
    wp_pures.
    destruct r1; destruct r2.
    wp_apply (wp_par (λ _, True%I) (λ _, True%I)).
    Print acquire_spec.
    - wp_apply (acquire_spec). iDestruct 1 as (n) "[Hr %]"
    unfold acquire in *.
    wp_pures.
    wp_alloc r1 as "Hr1".
  Admitted.

  Lemma sum_spec : ∀ n rpair lpair,
    {{{ pair_eq n rpair }}}
      sum (#(fst rpair), #(snd rpair)) lpair
    {{{ z, RET #z; ⌜ z = (n + n)%Z ⌝ }}}.
  Proof.
  Admitted.
End proof.
