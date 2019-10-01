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

Record semTy (base: forall T1 T2, T1 -> T2 -> Prop) :=
  {
    world : Type;
    init : world;
    wimpl : world -> world -> Prop;
    wimpl_PreOrd : RelationClasses.PreOrder wimpl;
    reln : forall T1 T2, world -> T1 -> T2 -> Prop;
    reln_compat:
      forall w1 w2, wimpl w1 w2 -> forall T1 T2 t1 t2, @reln T1 T2 w2 t1 t2 -> reln w1 t1 t2;
    reln_intro:
      forall w T1 T2 v1 v2,
        base _ _ v1 v2 ->
        @reln T1 T2 w v1 v2;
    reln_elim:
      forall w T1 T2 v1 v2 T1' T2' v1' v2',
        @reln T1' T2' w v1' v2' ->
        (base _ _ v1' v2' -> @reln T1 T2 w v1 v2) ->
        @reln T1 T2 w v1 v2
  }.


Record LayerImplRel C_Op Op :=
  {
    compile_rel_val {T1 T2} : T1 -> T2 -> Prop;
    compile_rel_base (sTy : semTy (@compile_rel_val)) {T1 T2} :
      world sTy -> proc Op T1 -> proc C_Op T2 -> Prop;
    recover_rel: rec_seq C_Op;
  }.

Inductive compile_rel Op C_Op `(impl: LayerImplRel C_Op Op) sTy
  : forall T1 T2, world sTy -> proc Op T1 -> proc C_Op T2 -> Prop :=
| cr_base {T1 T2} w (p1: proc Op T1) (p2: proc C_Op T2):
    impl.(compile_rel_base) sTy w p1 p2 ->
    compile_rel impl sTy w p1 p2
| cr_ret {T1 T2} w (v1: T1) (v2: T2):
    reln sTy w v1 v2 ->
    compile_rel impl sTy w (Ret v1) (Ret v2)
| cr_bind {T1 T1' T2 T2'} w (p1: proc Op T1) (p1': forall T1, proc Op T1')
                          (p2: proc C_Op T2) (p2': forall T2, proc C_Op T2'):
    compile_rel impl sTy w p1 p2 ->
    (forall w' x y, wimpl sTy w' w ->
                reln sTy w' x y ->
                compile_rel impl sTy w' (p1' x) (p2' y)) ->
    compile_rel impl sTy w (Bind p1 p1') (Bind p2 p2')
| cr_loop {T1 T2 R1 R2} w (b: T1 -> proc Op (LoopOutcome T1 R1))
                    (b': T2 -> proc C_Op (LoopOutcome T2 R2)) init init':
    reln sTy w init init' ->
    (forall w' mt mt', wimpl sTy w' w ->
                       reln sTy w' mt mt' ->
                       compile_rel impl sTy w' (b mt) (b' mt')) ->
    compile_rel impl sTy w (Loop b init) (Loop b' init')
| cr_unregister w:
    compile_rel impl sTy w Unregister Unregister
| cr_wait w:
    compile_rel impl sTy w Wait Wait
| cr_spawn {T1 T2} w (p: proc Op T1) (p': proc C_Op T2):
    compile_rel impl sTy w p p' ->
    compile_rel impl sTy w (Spawn p) (Spawn p').

Inductive compile_rel_whole Op C_Op `(impl: LayerImplRel C_Op Op) sTy T1 T2 w:
  proc Op T1 -> proc C_Op T2 -> Prop :=
| cr_whole p p':
    compile_rel impl sTy w p p' ->
    compile_rel_whole impl sTy w p (Bind p' (fun v => _ <- Wait; Ret v))%proc.

Inductive compile_rel_proc_seq {T1 T2 Op C_Op} `(impl: LayerImplRel C_Op Op) sTy w:
  proc_seq Op T1 -> proc_seq C_Op T2 -> Prop :=
| cr_seq_nil (v: T1) (v': T2):
    (reln sTy w v v' \/ compile_rel_val impl v v') ->
    compile_rel_proc_seq impl sTy w (Proc_Seq_Nil v) (Proc_Seq_Nil v')
| cr_seq_cons {T' T2'} (p: proc Op T') (p': proc C_Op T2') f f':
    compile_rel_whole impl sTy w p p' ->
    (forall w' x y, wimpl sTy w' w ->
        reln sTy w' x y ->
        compile_rel_proc_seq impl sTy w (f x) (f' y)) ->
    compile_rel_proc_seq impl sTy w (Proc_Seq_Bind p f) (Proc_Seq_Bind p' f').

Definition LayerImpl_to_LayerImplRel {C_Op Op} (impl: LayerImpl C_Op Op): LayerImplRel C_Op Op :=
  {|
    compile_rel_val {T1 T2} v1 v2 := forall pf: T1 = T2, v1 = eq_rect_r _ v2 pf;
    compile_rel_base sTy {T1 T2} :=
      fun w p p' => exists (pf : T1 = T2) (op: Op T1),
          eq_rect_r _ (fun p' => p = Call op /\ p' = compile impl (Call op)) (eq_sym pf) p';
     recover_rel := recover impl |}.
