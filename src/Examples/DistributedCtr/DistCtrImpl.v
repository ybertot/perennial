From iris.algebra Require Import auth frac_auth excl.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode notation lib.par lib.spin_lock.

Definition alloc : expr :=
  let: "r1" := ref #0 in
  let: "r2" := ref #0 in
  let: "lk1" := newlock #() in
  let: "lk2" := newlock  #() in
  Pair (Pair "r1" "r2") (Pair "lk1" "lk2").

(* precondition: r1 r2 are an alloced pair *)
Definition inc (rpair : expr) (lkpair: expr) : expr :=
  let: "r1" := Fst rpair in
  let: "r2" := Snd rpair in
  let: "lk1" := Fst lkpair in
  let: "lk2" := Snd lkpair in
  (
    (acquire "lk1";; "r1" <- !"r1" + #1;; release "lk1")
  |||
    (acquire "lk2";; "r2" <- !"r2" + #2;; release "lk2")
  ).

Definition sum (rpair : expr) (lkpair: expr) : expr :=
  let: "r1" := Fst rpair in
  let: "r2" := Snd rpair in
  let: "lk1" := Fst lkpair in
  let: "lk2" := Snd lkpair in
  acquire "lk1";; acquire "lk2";;
  "r" <-!"r1" + !"r2";;
  release "lk2";; release "lk1";;
  "r".

Section proof.
  (** Come up with a suitable invariant and prove the spec **)
  Context `{!heapG Σ, !spawnG Σ, !inG Σ (authR (optionUR (exclR ZO)))}.

  Definition parallel_add_inv (rpair : loc * loc) : iProp Σ := (*(γ1 γ2 : gname) : iProp Σ :=*)
    (∃ n1 n2:Z, (⌜#n1 = #n2⌝
                  ∗ (fst rpair) ↦ #(n1))
                  ∗ ((snd rpair) ↦ #(n2))%I).
                  (*∗ own γ1 (● (Excl' n1)) ∗ own γ2 (● (Excl' n2)))%I.*)

  (* Notes: loc = kind of like a Coq literal number, LitV (LitLoc loc) is an actual value in the language *)
  Definition pair_eq (n: Z) (rpair : loc * loc) : iProp Σ := ∃ n, (fst rpair) ↦ #n ∗ (snd rpair) ↦ #n.

  Print val . 
  Locate "#".
  Print base_lit. 

  Implicit Types (l: loc).
  Lemma alloc_spec : 
    {{{ True%I }}}
      alloc
    {{{ '(l1,l2,lk1,lk2), RET Pair ((Pair #l1 #l2) (Pair lk1 lk2)); l1 ↦ #0 ∗ l2 ↦ #0 }}}.
  Proof.
    (* exercise *)
  Admitted.

  Lemma inc_spec : ∀ n rpair lpair,
    {{{ pair_eq n rpair }}}
      inc (#(fst rpair), #(snd rpair)) lpair
    {{{ z, RET #z; pair_eq (n+1) rpair }}}.
  Proof.
    (* exercise *)
  Admitted.

  Lemma sum_spec : ∀ n rpair lpair,
    {{{ pair_eq n rpair }}}
      sum (#(fst rpair), #(snd rpair)) lpair
    {{{ z, RET #z; ⌜ z = (n + n)%Z ⌝ }}}.
  Proof.
    (* exercise *)
  Admitted.
End proof.
