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

  Definition parallel_inc_inv (rpair : loc * loc) : iProp Σ := (*(γ1 γ2 : gname) : iProp Σ :=*)
    (∃ n1 n2:Z, (⌜#n1 = #n2⌝
                  ∗ (fst rpair) ↦ #(n1))
                  ∗ ((snd rpair) ↦ #(n2))%I).
                  (*∗ own γ1 (● (Excl' n1)) ∗ own γ2 (● (Excl' n2)))%I.*)

  (* Notes: loc = kind of like a Coq literal number, LitV (LitLoc loc) is an actual value in the language *)

  Lemma alloc_spec : 
    {{{ True%I }}}
      alloc #()
      {{{ r1 r2 lk, RET PairV (PairV #r1 #r2) lk; ∃ γ, is_lock LockN γ lk (parallel_inc_inv (r1, r2))}}}.
  (* DO I NEED FORALL OR EXISTS GAMMA *)
  (* parallel_inc_inv (r1, r2) ∗ not needed because held in lock? *)
  Proof.
    iIntros (Φ) "_ HPost".
    unfold alloc.
    wp_alloc r1 as "Hr1".
    wp_alloc r2 as "Hr2"; wp_let.
    wp_apply (newlock_spec LockN (parallel_inc_inv (r1, r2)) with "[Hr1 Hr2]"). 
    iExists 0; iExists 0; iFrame; auto.

    iIntros (lk γ) "HIsLk".
    wp_let.
    wp_pures.
    iApply "HPost". iExists γ; auto.
  Qed.

  Print wp_par.
  Print is_lock.
  Lemma inc_spec : ∀ n r1 r2 lk1 lk2 R1 R2,
    {{{ is_lock lk1 R1 ∗ is_lock lk2 R2 ∗ pair_eq n (r1, r2)}}}
      inc (#r1, #r2) (#lk1, #lk2) 
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
