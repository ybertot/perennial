From Coq Require Import List.

From Perennial Require Export Lib.
Require Import ExMach.ExMachAPI.
Import RelationNotations.

Module Alloc.

  Inductive Op : Type -> Type :=
  | Alloc : Op (option nat)
  | Free (v : nat) : Op unit.

  Definition State : Type := gset nat.

  Definition dynamics : Dynamics Op State :=
    {| step T (op: Op T) :=
         match op with
         | Alloc =>
            ( v <- such_that (fun s v => v ∈ s);
              _ <- puts (fun s => s ∖ {[v]});
              pure (Some v) ) +
            pure None
         | Free v =>
            puts (fun s => s ∪ {[v]})
         end;
       crash_step := pure tt;
       finish_step := pure tt;
    |}.

  Lemma crash_total_ok (s: State):
    exists s', dynamics.(crash_step) s (Val s' tt).
  Proof. eexists; econstructor. Qed.

  Lemma crash_non_err_ok (s: State) ret:
    dynamics.(crash_step) s ret -> ret ≠ Err.
  Proof. inversion 1; congruence. Qed.

  Definition l : Layer Op :=
    {| Layer.OpState := State;
       sem := dynamics;
       trace_proj := fun _ => nil;
       crash_preserves_trace := fun _ _ _ => eq_refl;
       crash_total := crash_total_ok;
       finish_total := crash_total_ok;
       crash_non_err := crash_non_err_ok;
       finish_non_err := crash_non_err_ok;
       initP := fun s => s = ∅ |}.

End Alloc.

Module Inode.

  Inductive Op : Type -> Type :=
  | Read (i : nat) : Op (nat*nat)
  | Write2 (i : nat) (v0 v1 : nat) : Op unit.

  Definition State : Type := ((nat*nat) * (nat*nat)).

  Definition dynamics : Dynamics Op State :=
    {| step T (op: Op T) :=
         match op with
         | Read 0 =>
            reads (fun s => fst s)
         | Read 1 =>
            reads (fun s => snd s)
         | Read _ => pure (0, 0)
         | Write2 0 v0 v1 =>
            puts (fun s => ((v0, v1), snd s))
         | Write2 1 v0 v1 =>
            puts (fun s => (fst s, (v0, v1)))
         | Write2 _ _ _ => pure tt
         end;
       crash_step := pure tt;
       finish_step := pure tt;
    |}.

  Lemma crash_total_ok (s: State):
    exists s', dynamics.(crash_step) s (Val s' tt).
  Proof. eexists; econstructor. Qed.

  Lemma crash_non_err_ok (s: State) ret:
    dynamics.(crash_step) s ret -> ret ≠ Err.
  Proof. inversion 1; congruence. Qed.

  Definition l : Layer Op :=
    {| Layer.OpState := State;
       sem := dynamics;
       trace_proj := fun _ => nil;
       crash_preserves_trace := fun _ _ _ => eq_refl;
       crash_total := crash_total_ok;
       finish_total := crash_total_ok;
       crash_non_err := crash_non_err_ok;
       finish_non_err := crash_non_err_ok;
       initP := fun s => s = ((0,0),(0,0)) |}.

End Inode.
