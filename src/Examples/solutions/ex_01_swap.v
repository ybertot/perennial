(*
This exercise introduces the basic Iris Proof Mode tactics by proving a simple
example: a function that swaps the contents of two pointers. We will use this
function to implement two other functions.
*)
From iris.heap_lang Require Import proofmode notation.

(* The swap function, defined as a heap-lang value. This looks like an ordinary
Coq function, but it is not: heap-lang is a deeply embedded language in Coq. It
uses strings for name binding and notations close to Coq's (but typically
augmented with a colon to avoid ambiguity) to make it easy to read and write
programs. *)
Definition swap : val := λ: "x" "y",
  let: "tmp" := !"x" in
  "x" <- !"y";;
  "y" <- "tmp".

(* Using swap, we can define functions that rotate three pointers in left and
right direction. *)
Definition rotate_r : val := λ: "x" "y" "z",
  swap "y" "z";; swap "x" "y".

Definition rotate_l : val := λ: "x" "y" "z",
  swap "x" "y";; swap "y" "z".

Section proof.
(* Iris is parameterized by the type of ghost state that is needed to carry out
a proof. As such, the type of Iris propositions [iProp] is indexed by a [Σ]: a
list of cameras (actually, functors from OFEs to cameras). To make our proofs
generic, we abstract over any such [Σ] and use type classes to ensure that the
necessary cameras are present in [Σ].

For this proof, we do not need any special ghost state (i.e. cameras) apart from
the ghost state that's the heap-lang uses internally for modeling the [l ↦ v]
connective. The cameras for this ghost state is provided by the class [heapG].
*)
Context `{!heapG Σ}.

Lemma swap_spec x y v1 v2 :
  {{{ x ↦ v1 ∗ y ↦ v2 }}} swap #x #y {{{ RET #(); x ↦ v2 ∗ y ↦ v1 }}}.

  (* The "Texan triple" [ {{{ P }}} e {{{ RET v, Q }}} ] is syntactic sugar for:

         ∀ Φ, P -∗ (Q -∗ Φ v) -∗ WP e {{ v, Φ v }}

     Which is logically equivalent to [ P -∗ WP e {{ x, x = v ∗ Q }} ]

     In practice, the "Texan triple" is not more difficult to prove, but usually
     easier to use in other proofs, because the post-condition does not have to
     syntactically match [Q]. Using this way of stating specifications, the
     consequence and framing rule is implicitly applied on the post-condition.

     Note that [ # v ] is the embedding of values ([bool], [Z], [loc]) into
     heap-lang values.*)
Proof.
  iIntros (Φ) "[Hx Hy] Post".
  unfold swap.
  wp_lam. wp_let.
  wp_load. wp_let.
  wp_load. wp_store.
  wp_store.
  iApply "Post".
  iSplitL "Hx".
  - iApply "Hx".
  - iApply "Hy".
Qed.

(* Same lemma, but using a bit of automation to shorten the proof. *)
Lemma swap_spec_2 x y v1 v2 :
  {{{ x ↦ v1 ∗ y ↦ v2 }}} swap #x #y {{{ RET #(); x ↦ v2 ∗ y ↦ v1 }}}.
Proof.
  iIntros (Φ) "[??] Post".
  wp_lam. wp_let. wp_load. wp_let. wp_load. wp_store. wp_store.
  iApply "Post". iFrame.
Qed.

(* We can further automate the lemma by defining a simple Ltac tactic for
symbolic executing. *)
Ltac wp_exec := repeat (wp_lam || wp_pure _ || wp_load || wp_store).

(* This tactic repeatedly tries to symbolically execute pure redexes, loads and
stores. It makes use of the tactic [wp_pure t], which tries to find the redex
[t] in the goal, and executes that redex. The redex [t] may contain holes, and
as such, tactics like [wp_seq] are actually defined as [wp_pure (_ ;; _)%E]. By
using [wp_pure _] it will symbolically execute *any* pure redex. *)

(* Same lemma again, but now using the tactic we just defined. *)
Lemma swap_spec_2_more_automation x y v1 v2 :
  {{{ x ↦ v1 ∗ y ↦ v2 }}} swap #x #y {{{ RET #(); x ↦ v2 ∗ y ↦ v1 }}}.
Proof.
  iIntros (Φ) "[??] Post". wp_exec.
  iApply "Post". iFrame.
Qed.

Lemma rotate_r_spec x y z v1 v2 v3 :
  {{{ x ↦ v1 ∗ y ↦ v2 ∗ z ↦ v3 }}}
    rotate_r #x #y #z
  {{{ RET #(); x ↦ v3 ∗ y ↦ v1 ∗ z ↦ v2 }}}.
Proof.
  (* As in Coq, the IPM introduction pattern (p1 & p2 & .. & pn) ] is syntactic
  sugar for [ [p1 [p2 [... pn]]] ]. *)
  iIntros (Φ) "(Hx & Hy & Hz) Post".
  unfold rotate_r. wp_lam. do 2 wp_let.
  wp_bind (swap _ _).
  iApply (swap_spec with "[Hy Hz]").
  { iFrame. }
  (* Inspired by ssreflect, the IPM introduction pattern [ /= ] performs
  [simpl]. *)
  iNext. iIntros "[Hy Hz] /=". wp_seq.
  (* We can also immediately frame hypothesis when using a lemma: *)
  iApply (swap_spec with "[$Hx $Hy]"); iNext; iIntros "[Hx Hy]".
  iApply "Post". iFrame.
Qed.

Lemma rotate_r_spec_again x y z v1 v2 v3 :
  {{{ x ↦ v1 ∗ y ↦ v2 ∗ z ↦ v3 }}}
    rotate_r #x #y #z
  {{{ RET #(); x ↦ v3 ∗ y ↦ v1 ∗ z ↦ v2 }}}.
Proof.
  iIntros (Φ) "(Hx & Hy & Hz) Post". wp_lam. do 2 wp_let.
  (* We can shorten the above a bit: Instead of using the [iApply] tactic, we
  can use [wp_apply] which automatically uses [wp_bind] first. Also, it strips
  the later [▷] by calling [iNext] afterwards. *)
  wp_apply (swap_spec with "[$Hy $Hz]"); iIntros "[Hy Hz] /="; wp_seq.
  wp_apply (swap_spec with "[$Hx $Hy]"); iIntros "[Hx Hy] /=".
  iApply "Post". iFrame.
Qed.

(* *Exercise*: Do this proof yourself. Try a couple of variations of the tactics
we have seen before:
- Do the whole proof explicitly by proving [swap] inline,
- Use the specification of [swap] in combination with [iApply],
- Use the specification of [swap] in combination with [wp_apply]
*)
Lemma rotate_l_spec x y z v1 v2 v3 :
  {{{ x ↦ v1 ∗ y ↦ v2 ∗ z ↦ v3 }}}
    rotate_l #x #y #z
  {{{ RET #(); x ↦ v2 ∗ y ↦ v3 ∗ z ↦ v1 }}}.
Proof.
  iIntros (Φ) "(Hx & Hy & Hz) Post". unfold rotate_l. wp_lam. do 2 wp_let.
  wp_apply (swap_spec with "[$Hx $Hy]"); iIntros "[Hx Hy]"; wp_seq.
  wp_apply (swap_spec with "[$Hy $Hz]"); iIntros "[Hy Hz]".
  iApply ("Post" with "[$]").
Qed.
End proof.
