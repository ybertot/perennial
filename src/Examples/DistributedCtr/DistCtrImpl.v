From iris.algebra Require Import auth frac_auth excl.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode notation lib.par.

(* Remove the lock for now, just want to reason about two different counters *)
Definition parallel_add_mul : expr :=
  let: "r1" := ref #0 in
  let: "r2" := ref #0 in
  (
    ("r1" <- !"r2" + #1;;)
  |||
    ("r2" <- !"r1" + #1;;)
  );;
  !"r1" + !"r2".

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
    True%I. (* exercise: replace [True] with something meaningful. *)

  Lemma parallel_add_mul_spec :
    {{{ True }}} parallel_add_mul {{{ z, RET #z; ⌜ z = 2 ∨ z = 4 ⌝ }}}.
  Proof.
    (* exercise *)
  Admitted.
End proof.