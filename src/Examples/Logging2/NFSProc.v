Require Import Logging2.RelationsNoErr.
Require Import List.

Global Set Implicit Arguments.
Global Generalizable All Variables.
Global Set Printing Projections.
(* for compatibility with coq master *)
Set Warnings "-undeclared-scope".

Import RelationNotations.

Definition Event : Type := {T: Type & T}.

Section Proc.
  Variable Op : Type -> Type.

  Inductive proc : Type -> Type :=
  | Call : forall T (op : Op T), proc T
  | Ret : forall T (v : T), proc T
  | Bind : forall T (T1 : Type) (p1 : proc T1) (p2 : T1 -> proc T), proc T.

End Proc.

Arguments Call {Op T}.
Arguments Ret {Op T} v.

(* TODO : allow forwarding the recovery value to the next routine *)
Inductive rec_seq (Op: Type -> Type) : Type :=
| Seq_Nil
| Seq_Cons (T : Type) (p : proc Op T) (ps: rec_seq Op).
Arguments Seq_Nil {Op}.
Arguments Seq_Cons {Op T}.

(** A sequence of procedures that a user might wish to run, where for each
    procedure in the sequence they specify a continuation to run on success,
    and an alternate sequence to run if a crash happens. *)

Inductive ExecOutcome : Type :=
| Normal : {T : Type & T} -> ExecOutcome
| Recovered : {T: Type & T} -> ExecOutcome.

Inductive proc_seq (Op: Type -> Type) (T: Type) : Type :=
| Proc_Seq_Nil (v : T) (*  : ExecOutcome) *)
| Proc_Seq_Bind (T0 : Type) (p : proc Op T0) (rx : ExecOutcome -> proc_seq Op T).
Arguments Proc_Seq_Nil {Op _}.
Arguments Proc_Seq_Bind {Op _ _}.

Fixpoint rec_seq_append Op (ps1 ps2: rec_seq Op) :=
  match ps1 with
  | Seq_Nil => ps2
  | Seq_Cons p ps1' => Seq_Cons p (rec_seq_append ps1' ps2)
  end.

Definition rec_seq_snoc Op T (ps: rec_seq Op) (p: proc Op T) :=
  rec_seq_append ps (Seq_Cons p Seq_Nil).

Definition thread_pool (Op: Type -> Type) := list {T : Type & proc Op T}.

Definition OpSemantics Op State := forall T, Op T -> relation State State T.
Definition CrashSemantics State := relation State State unit.
Definition FinishSemantics State := relation State State unit.

Record Dynamics Op State :=
  { step: OpSemantics Op State;
    crash_step: CrashSemantics State;
    finish_step: FinishSemantics State;
  }.

Section Dynamics.

  Context `(sem: Dynamics Op OpState).
  Definition State : Type := nat * OpState.

  Definition lifted_crash_step : CrashSemantics State :=
    fst_lift (puts (fun x => 1));;
    snd_lift (sem.(crash_step)).

  Definition lifted_finish_step : FinishSemantics State :=
    fst_lift (puts (fun x => 1));;
    snd_lift (sem.(finish_step)).

  (** First, we define semantics of running programs with halting (without the
  effect of a crash or recovery) *)

  Fixpoint exec_step {T} (p: proc Op T) {struct p}
    : relation State State (proc Op T * thread_pool Op) :=
    match p with
    | Ret v => none
    | Call op => v <- snd_lift (step sem op); pure (Ret v, nil)
    | @Bind _ T0 _ p p' =>
      match p in (proc _ T1) return
             (T1 -> proc _ T0) -> relation State State (proc _ T0 * thread_pool _)
       with
      | Ret v => fun p' => pure (p' v, nil)
      | _ => fun _ => vp <- exec_step p;
                      pure (Bind (fst vp) p', snd vp)
      end p'
    end.

  (* TODO: need to define this after, otherwise can't use proc in the above *)
  Notation proc := (proc Op).
  Notation rec_seq := (rec_seq Op).
  Notation proc_seq := (proc_seq Op).
  Notation thread_pool := (thread_pool Op).
  Notation step := sem.(step).
  Notation crash_step := lifted_crash_step.
End Dynamics.

Module ProcNotations.
  (* Declare Scope proc_scope. *)
  Delimit Scope proc_scope with proc.
  Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
                               (at level 20, p1 at level 100, p2 at level 200, right associativity)
                             : proc_scope.
  Notation "'let!' x <- p1 ; p2" := (Bind p1 (fun x => p2))
                               (at level 20, x pattern, p1 at level 100, p2 at level 200, right associativity)
                             : proc_scope.
End ProcNotations.
