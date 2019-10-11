Require Import Logging2.AllocAPI.
Require Import ExMach.ExMachAPI.

Definition txn := nat.
Axiom begin : proc ExMach.Op txn.
Axiom commit : txn -> proc ExMach.Op unit.
Axiom read : txn -> nat -> proc ExMach.Op nat.
Axiom write : txn -> nat -> nat -> proc ExMach.Op unit.

Axiom allocator : nat.

Fixpoint alloc_below (t : txn) (off : nat) (n : nat) :=
  (
    match n with
    | O => Ret None
    | S n' =>
      v <- read t (off+n');
      if decide (v = 0) then
        _ <- write t (off+n') 1;
        Ret (Some n')
      else
        alloc_below t off n'
    end
  )%proc.

Definition alloc (t : txn) :=
  (
    max <- read t allocator;
    alloc_below t (allocator+1) max
  )%proc.

Definition free (t : txn) n :=
  write t (allocator+1+n) 0.
