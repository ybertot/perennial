Require FunctionalExtensionality.

From Transitions Require Import Relations Rewriting.

Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Tactical.ProofAutomation.

Import RelationNotations.

Record Layer Op :=
  { OpState: Type;
    sem: Dynamics Op OpState;
    (* TODO: should these be part of Dynamics instead of Layer? *)
    trace_proj: OpState -> list Event;
    crash_preserves_trace:
      forall s1 s2, sem.(crash_step) s1 (Val s2 tt) -> trace_proj s1 = trace_proj s2;
    crash_total: forall s1, exists s2, sem.(crash_step) s1 (Val s2 tt);
    finish_total: forall s1, exists s2, sem.(finish_step) s1 (Val s2 tt);
    crash_non_err: forall s1 ret, sem.(crash_step) s1 ret -> ret <> Err;
    finish_non_err: forall s1 ret, sem.(finish_step) s1 ret -> ret <> Err;
    initP: OpState -> Prop }.

Definition State `(L: Layer Op) := @Proc.State (L.(OpState)).
Coercion sem : Layer >-> Dynamics.

(* LayerImpl is just the code needed to translate from one layer to another -
   the logical components are in [LayerRefinement] *)
Record LayerImpl C_Op Op :=
  { compile_op `(op: Op T) : proc C_Op T;
    (* TODO: layer implementations should be allowed to return from recovery
         (though it's unclear what purpose that would serve *)
    recover: rec_seq C_Op; }.

Fixpoint compile Op C_Op `(impl: LayerImpl C_Op Op) T (p: proc Op T) : proc C_Op T :=
  match p with
  | Call op => impl.(compile_op) op
  | Ret v => Ret v
  | Bind p p' => Bind (impl.(compile) p) (fun v => impl.(compile) (p' v))
  | Loop b init => Loop (fun mt => impl.(compile) (b mt)) init
  | Unregister => Unregister
  | Wait => Wait
  | Spawn p => Spawn (impl.(compile) p)
  end.

Import ProcNotations.
Definition compile_whole Op C_Op `(impl: LayerImpl C_Op Op) T (p: proc Op T) : proc C_Op T :=
  Bind (compile impl p) (fun v => _ <- Wait; Ret v)%proc.

Fixpoint map_proc_seq {T Op C_Op} (f: forall T, proc Op T -> proc C_Op T) (es: proc_seq Op T) :=
  match es with
  | Proc_Seq_Nil v => (Proc_Seq_Nil v : proc_seq C_Op T)
  | @Proc_Seq_Bind _ _ T0 e es' =>
    Proc_Seq_Bind (f _ (e: proc Op T0)) (fun x => map_proc_seq f (es' x))
  end.

Fixpoint compile_seq Op C_Op `(impl: LayerImpl C_Op Op) (ps: rec_seq Op) :
  rec_seq C_Op :=
  match ps with
  | Seq_Nil => Seq_Nil
  | Seq_Cons p ps' => Seq_Cons (compile_whole impl p) (impl.(compile_seq) ps')
  end.

Definition compile_proc_seq {T} Op C_Op `(impl: LayerImpl C_Op Op) (ps: proc_seq Op T) :=
  map_proc_seq (compile_whole impl) ps.

Definition compile_rec Op C_Op `(impl: LayerImpl C_Op Op) (rec: rec_seq Op) : rec_seq C_Op :=
  rec_seq_append impl.(recover) (compile_seq impl rec).

(* Some translations are not expressable as per-operation mappings. Instead,
   they transform appropriate *sequences* of operations (i.e., procs) into
   procs in the layer below. We represent these translations as relations instead of functions.
   This is fine because we use these for Goose layers, where we don't need to literally
   extract the compile translation as runnable code *)
Record LayerImplRel C_Op Op :=
  {
    compile_rel_val {T1 T2}: T1 -> T2 -> Prop;
    compile_rel_base {T1 T2} : proc Op T1 -> proc C_Op T2 -> Prop;
    recover_rel: rec_seq C_Op;
  }.

Inductive compile_rel Op C_Op `(impl: LayerImplRel C_Op Op): forall T1 T2,
  proc Op T1 -> proc C_Op T2 -> Prop :=
| cr_base {T1 T2} (p1: proc Op T1) (p2: proc C_Op T2):
    impl.(compile_rel_base) p1 p2 ->
    compile_rel impl p1 p2
| cr_ret {T} (v: T): compile_rel impl (Ret v) (Ret v)
| cr_bind {T1 T1' T2 T2'} (p1: proc Op T1) (p1': forall T1, proc Op T1')
                          (p2: proc C_Op T2) (p2': forall T2, proc C_Op T2'):
    compile_rel impl p1 p2 ->
    (forall x y, compile_rel_val impl x y -> compile_rel impl (p1' x) (p2' y)) ->
    compile_rel impl (Bind p1 p1') (Bind p2 p2')
| cr_loop {T1 T2 R1 R2} (b: T1 -> proc Op (LoopOutcome T1 R1))
                    (b': T2 -> proc C_Op (LoopOutcome T2 R2)) init init':
    compile_rel_val impl init init' ->
    (forall mt mt', compile_rel_val impl mt mt' -> compile_rel impl (b mt) (b' mt')) ->
    compile_rel impl (Loop b init) (Loop b' init')
| cr_unregister:
    compile_rel impl Unregister Unregister
| cr_wait:
    compile_rel impl Wait Wait
| cr_spawn {T1 T2} (p: proc Op T1) (p': proc C_Op T2):
    compile_rel impl p p' ->
    compile_rel impl (Spawn p) (Spawn p').

Inductive compile_rel_whole Op C_Op `(impl: LayerImplRel C_Op Op) T1 T2:
  proc Op T1 -> proc C_Op T2 -> Prop :=
| cr_whole p p':
    compile_rel impl p p' ->
    compile_rel_whole impl p (Bind p' (fun v => _ <- Wait; Ret v))%proc.

Inductive compile_rel_proc_seq {T1 T2 Op C_Op} `(impl: LayerImplRel C_Op Op):
  proc_seq Op T1 -> proc_seq C_Op T2 -> Prop :=
| cr_seq_nil (v: T1) (v': T2):
    compile_rel_val impl v v' ->
    compile_rel_proc_seq impl (Proc_Seq_Nil v) (Proc_Seq_Nil v')
| cr_seq_cons {T' T2'} (p: proc Op T') (p': proc C_Op T2') f f':
    compile_rel_whole impl p p' ->
    (forall x y, compile_rel_val impl x y -> compile_rel_proc_seq impl (f x) (f' y)) ->
    compile_rel_proc_seq impl (Proc_Seq_Bind p f) (Proc_Seq_Bind p' f').

Definition compile_rel_val_eq {T1 T2} : T1 -> T2 -> Prop.
Proof.
  intros x y.
  refine (exists (pf: T1 = T2), _).
  subst. apply (x = y).
Defined.

Definition LayerImpl_to_LayerImplRel {C_Op Op} (impl: LayerImpl C_Op Op): LayerImplRel C_Op Op :=
  {|
    compile_rel_val T1 T2 := compile_rel_val_eq;
    compile_rel_base {T1 T2} :=
      fun p p' => exists (pf : T1 = T2) (op: Op T1),
          eq_rect_r _ (fun p' => p = Call op /\ p' = compile impl (Call op)) (eq_sym pf) p';
     recover_rel := recover impl |}.
