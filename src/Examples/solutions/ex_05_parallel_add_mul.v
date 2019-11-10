(**
In this exercise we consider a variant of the previous exercise. We have a
reference which is initially 0 and two threads running in parallel. One thread
increases the value of the reference by 2, whereas the other multiples the
value of the reference by two. An interesting aspect of this exercise is that
the outcome of this program is non-deterministic. Depending on which thread runs
first, the outcome is either 2 or 4.

Contrary to the earlier exercises, this exercise is nearly entirely open.
*)
From iris.algebra Require Import auth frac_auth excl.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode notation lib.par.
Require Import solutions.ex_03_spinlock.

Definition parallel_add_mul : expr :=
  let: "r" := ref #0 in
  let: "l" := newlock #() in
  (
    (acquire "l";; "r" <- !"r" + #2;; release "l")
  |||
    (acquire "l";; "r" <- !"r" * #2;; release "l")
  );;
  acquire "l";;
  !"r".

(** In this proof we will make use of Boolean ghost variables. *)
Section proof.
  Context `{!heapG Σ, !spawnG Σ, !inG Σ (authR (optionUR (exclR boolO)))}.

  (** The same helping lemmas for ghost variables that we have already seen in
  the previous exercise. *)
  Lemma ghost_var_alloc b :
    (|==> ∃ γ, own γ (● (Excl' b)) ∗ own γ (◯ (Excl' b)))%I.
  Proof.
    iMod (own_alloc (● (Excl' b) ⋅ ◯ (Excl' b))) as (γ) "[??]".
    - by apply auth_both_valid.
    - by eauto with iFrame.
  Qed.

  Lemma ghost_var_agree γ b c :
    own γ (● (Excl' b)) -∗ own γ (◯ (Excl' c)) -∗ ⌜ b = c ⌝.
  Proof.
    iIntros "Hγ● Hγ◯".
    by iDestruct (own_valid_2 with "Hγ● Hγ◯")
      as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid.
  Qed.

  Lemma ghost_var_update γ b' b c :
    own γ (● (Excl' b)) -∗ own γ (◯ (Excl' c)) ==∗
      own γ (● (Excl' b')) ∗ own γ (◯ (Excl' b')).
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (● Excl' b' ⋅ ◯ Excl' b') with "Hγ● Hγ◯") as "[$$]".
    { by apply auth_update, option_local_update, exclusive_local_update. }
    done.
  Qed.

  (** *Difficult exercise*: come up with a suitable invariant and prove the spec
  of [parallel_add_mul]. In this proof, you should use Boolean ghost variables,
  and the rules for those as given above. You are allowed to use any number of
  Boolean ghost variables. *)
  Definition parallel_add_mul_inv (r : loc) (γ1 γ2 : gname) : iProp Σ :=
    (∃ (b1 b2 : bool) (z : Z),
        own γ1 (● Excl' b1) ∗ own γ2 (● Excl' b2) ∗ r ↦ #z ∗
       ⌜match b1, b2 with
        | true,  true  => z = 2 ∨ z = 4
        | true,  false => z = 2
        | false, _     => z = 0
        end⌝)%I.

  Lemma parallel_add_mul_spec :
    {{{ True }}} parallel_add_mul {{{ z, RET #z; ⌜ z = 2 ∨ z = 4 ⌝ }}}.
  Proof.
    iIntros (Φ) "_ Post".
    unfold parallel_add_mul. wp_alloc r as "Hr". wp_let.
    iMod (ghost_var_alloc false) as (γ1) "[Hγ1● Hγ1◯]".
    iMod (ghost_var_alloc false) as (γ2) "[Hγ2● Hγ2◯]".
    wp_apply (newlock_spec (parallel_add_mul_inv r γ1 γ2) with "[Hr Hγ1● Hγ2●]").
    { iExists false, false, 0. iFrame. done. }
    iIntros (l) "#Hl". wp_let.
    wp_apply (wp_par (λ _, own γ1 (◯ Excl' true)) (λ _, own γ2 (◯ Excl' true))
                with "[Hγ1◯] [Hγ2◯]").
    - wp_apply (acquire_spec with "Hl").
      iDestruct 1 as (b1 b2 z) "(Hγ1● & Hγ2● & Hr & %)".
      wp_seq. wp_load. wp_op. wp_store.
      iDestruct (ghost_var_agree with "Hγ1● Hγ1◯") as %->. subst z.
      iMod (ghost_var_update γ1 true with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]".
      wp_apply (release_spec with "[- $Hl Hγ1◯]"); [|by auto].
      iExists _, _, _. iFrame "Hγ1● Hγ2● Hr". destruct b2; auto.
    - wp_apply (acquire_spec with "Hl").
      iDestruct 1 as (b1 b2 z) "(Hγ1● & Hγ2● & Hr & %)".
      wp_seq. wp_load. wp_op. wp_store.
      iDestruct (ghost_var_agree with "Hγ2● Hγ2◯") as %->.
      iMod (ghost_var_update γ2 true with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".
      wp_apply (release_spec with "[$Hl Hγ1● Hr Hγ2●]"); [|by auto].
      iExists _, _, _. iFrame "Hγ1● Hγ2● Hr". destruct b1; subst z; auto.
    - iIntros (??) "[Hγ1◯ Hγ2◯] !>". wp_seq.
      wp_apply (acquire_spec with "Hl").
      iDestruct 1 as (b1 b2 z) "(Hγ1● & Hγ2● & Hr & %)".
      wp_seq. wp_load.
      iApply "Post".
      iDestruct (ghost_var_agree with "Hγ1● Hγ1◯") as %->.
      iDestruct (ghost_var_agree with "Hγ2● Hγ2◯") as %->.
      auto.
  Qed.
End proof.
