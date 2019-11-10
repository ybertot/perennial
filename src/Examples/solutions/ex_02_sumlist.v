(**
This exercise shows how to use representation predicates in Iris. We consider
some basic operations on linked lists. Although heap-lang is untyped, our
representation of lists intuitively corresponds to the following (rec-) type
in an ML-style language:

  list A := option (ref (A * list A))
*)
From iris.heap_lang Require Import proofmode notation.

(** A function that sums all elements of a list, defined as a heap-lang value: *)
Definition sum_list : val :=
  rec: "sum_list" "l" :=
    match: "l" with           (* A list is either... *)
      NONE => #0              (* ... the empty list *)
    | SOME "p" =>             (* ... or [SOME p], where [p] points to a pair ... *)
      let: "x" := Fst !"p" in (* ... whose first component is the head of the list *)
      let: "l" := Snd !"p" in (* ... and whose second component is the rest of the list. *)
      "x" + "sum_list" "l"
    end.

(** A function that increases all elements of a list in-place: *)
Definition inc_list : val :=
  rec: "inc_list" "n" "l" :=
    match: "l" with
      NONE => #()
    | SOME "p" =>
      let: "x" := Fst !"p" in
      let: "l" := Snd !"p" in
      "p" <- ("n" + "x", "l");;
      "inc_list" "n" "l"
    end.

(** The previous functions combined. *)
Definition sum_inc_list : val := λ: "n" "l",
  inc_list "n" "l";;
  sum_list "l".

(** A function that maps a function over all elements of a list: *)
Definition map_list : val :=
  rec: "map_list" "f" "l" :=
    match: "l" with
      NONE => #()
    | SOME "p" =>
      let: "x" := Fst !"p" in
      let: "l" := Snd !"p" in
      "p" <- ("f" "x", "l");;
      "map_list" "f" "l"
    end.

Section proof.
Context `{!heapG Σ}.

(** Representation predicate in separation logic for a list of integers [l]: *)
Fixpoint is_list (l : list Z) (v : val) : iProp Σ :=
  match l with
  | [] => ⌜ v = NONEV ⌝
  | x :: l' => ∃ (p : loc), ⌜ v = SOMEV #p ⌝ ∗
                 ∃ v' : val, p ↦ (#x, v') ∗ is_list l' v'
  end%I.

(**
In order to give a specification of [sum_list] we relate its result to the
sum defined as a pure Coq function.
*)
Definition sum_list_coq (l : list Z) : Z :=
  fold_right Z.add 0 l.

(**
The proof of the recursive function [sum_list] requires some form of recursion.
We can either do the induction over the list [l], or use the Löb induction
principle, given by the step-indexed nature of Iris. *)

(** The proof using induction over [l]: *)
Lemma sum_list_spec_induction l v :
  {{{ is_list l v }}} sum_list v {{{ RET #(sum_list_coq l); is_list l v }}}.
Proof.
  iIntros (Φ) "Hl Post".
  iInduction l as [|x l] "IH" forall (v Φ); simpl.
  (**
  Note that the option type is in fact encoded using sum types.
  Hence, [NONE] is syntactic sugar for [InjL #()] (or [InjLV #()]
  for values), and [SOME x] is syntactic sugar for [InjR x].
  *)
  - iDestruct "Hl" as %->.
    wp_rec.
    wp_match.
    iApply "Post". iPureIntro. reflexivity.
  - iDestruct "Hl" as (p) "[-> Hl]". iDestruct "Hl" as (v) "[Hp Hl]".
    wp_rec.
    wp_match.
    wp_load. wp_proj. wp_let.
    wp_load. wp_proj. wp_let.
    wp_apply ("IH" with "Hl"). iIntros "Hl". wp_op.
    iApply "Post".
    iExists p. iSplitR; [done|].
    iExists v. iSplitR "Hl"; [iApply "Hp"|iApply "Hl"].
Qed.

(** The proof using Löb induction. The parts which are in common with
[sum_list_spec_induction] are shortened using automation. *)
Lemma sum_list_spec_löb l v :
  {{{ is_list l v }}} sum_list v {{{ RET #(sum_list_coq l); is_list l v }}}.
Proof.
  iIntros (Φ) "Hl Post".
  iLöb as "IH" forall (l v Φ). destruct l as [|x l]; simpl; wp_rec.
  - iDestruct "Hl" as %->. wp_match. by iApply "Post".
  - iDestruct "Hl" as (p -> v) "[Hp Hl]". wp_match.
    do 2 (wp_load; wp_proj; wp_let).
    wp_apply ("IH" with "Hl"). iIntros "Hl". wp_op.
    iApply "Post". eauto with iFrame.
Qed.

(** *Exercise*: Do the proof of [inc_list] yourself. Use ordinary induction. *)
Lemma inc_list_spec_induction n l v :
  {{{ is_list l v }}}
    inc_list #n v
  {{{ RET #(); is_list (map (Z.add n) l) v }}}.
Proof.
  iIntros (Φ) "Hl Post".
  iInduction l as [|x l] "IH" forall (v Φ); simpl.
  - iDestruct "Hl" as %->.
    wp_rec. wp_let. wp_match.
    by iApply "Post".
  - iDestruct "Hl" as (p) "[-> Hl] /=". iDestruct "Hl" as (v) "[Hp Hl]".
    wp_rec. wp_let.
    wp_match.
    wp_load. wp_proj. wp_let.
    wp_load. wp_proj. wp_let.
    wp_op. wp_store.
    wp_apply ("IH" with "Hl"). iIntros "Hl".
    iApply "Post".
    iExists p. iSplitR; [done|].
    iExists v. iSplitR "Hl"; [iApply "Hp"|iApply "Hl"].
Qed.

(** *Exercise*: Now do the proof again using Löb induction. *)
Lemma inc_list_spec_löb n l v :
  {{{ is_list l v }}}
    inc_list #n v
  {{{ RET #(); is_list (map (Z.add n) l) v }}}.
Proof.
  iIntros (Φ) "Hl Post".
  iLöb as "IH" forall (l v Φ). destruct l as [|x l]; simpl; wp_rec; wp_let.
  - iDestruct "Hl" as %->. wp_match. by iApply "Post".
  - iDestruct "Hl" as (p -> v) "[Hp Hl] /=". wp_match.
    do 2 (wp_load; wp_proj; wp_let). wp_op. wp_store.
    wp_apply ("IH" with "Hl"). iIntros "Hl".
    iApply "Post". eauto with iFrame.
Qed.

(** *Exercise*: Do the proof of [sum_inc_list] by making use of the lemmas of
[sum_list] and [inc_list] we just proved. Make use of [wp_apply]. *)
Lemma sum_inc_list_spec n l v :
  {{{ is_list l v }}}
    sum_inc_list #n v
  {{{ RET #(sum_list_coq (map (Z.add n) l)); is_list (map (Z.add n) l) v }}}.
Proof.
  iIntros (Φ) "Hl Post". wp_lam. wp_let.
  wp_apply (inc_list_spec_induction with "Hl"); iIntros "Hl /="; wp_seq.
  wp_apply (sum_list_spec_induction with "Hl"); auto.
Qed.

(** *Optional exercise*: Prove the following spec of [map_list] which makes use
of a nested Texan triple, This spec is rather weak, as it requires [f] to be
pure, if you like, you can try to make it more general. *)
Lemma map_list_spec_induction (f : val) (f_coq : Z → Z) l v :
  (∀ n, {{{ True }}} f #n {{{ RET #(f_coq n); True }}}) -∗
  {{{ is_list l v }}} map_list f v {{{ RET #(); is_list (map f_coq l) v }}}.
Proof.
  iIntros "#Hf" (Φ) "!# Hl Post".
  iLöb as "IH" forall (l v Φ). destruct l as [|x l]; simpl; wp_rec; wp_let.
  - iDestruct "Hl" as %->. wp_match. by iApply "Post".
  - iDestruct "Hl" as (p -> v) "[Hp Hl] /=". wp_match.
    do 2 (wp_load; wp_proj; wp_let).
    wp_apply ("Hf" with "[//]"); iIntros "_ /=".
    wp_store.
    wp_apply ("IH" with "Hl"). iIntros "Hl".
    iApply "Post". eauto with iFrame.
Qed.
End proof.
