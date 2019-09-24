From Coq Require Import List.

Require Import ExMach.ExMachAPI.
From Perennial Require Export Lib.


Module DB.

  Definition db := list nat.

  Inductive Op : Type -> Type :=
  | New : Op db
  | Add (d: db) (n:nat) : Op db
  | Avg (d: db) : Op nat.

  Definition State := unit.

  Definition dynamics : Dynamics Op State :=
    {| step T (op: Op T) :=
         match op with
         | New => pure (nil : list nat)
         | Add db n => pure (n :: db)
         | Avg db => pure (fold_right plus 0 db / length db)
         end;
       crash_step :=
         puts (fun _ => tt);
       finish_step :=
         puts (fun _ => tt);
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
       initP := fun s => s = tt |}.
End DB.

Definition new : proc ExMach.Op _ := Ret (0, 0).
Definition add db n : proc ExMach.Op _ := (Ret (n + fst db, 1 + snd db))%proc.
Definition avg db : proc ExMach.Op _ := (Ret (fst db / snd db)).

Inductive compile_stat_base sTy :
  forall T1 T2, world sTy -> proc DB.Op T1 -> proc ExMach.Op T2 -> Prop :=
  | new_compile w : compile_stat_base sTy w (Call DB.New) new
  | add_compile w db db' n:
      reln sTy w db db' ->
      compile_stat_base sTy w (Call (DB.Add db n)) (add db' n)
  | avg_compile w db db':
      reln sTy w db db' ->
      compile_stat_base sTy w (Call (DB.Avg db)) (avg db').

Definition impl : LayerImplRel ExMach.Op DB.Op :=
  {| compile_rel_base := compile_stat_base;
     recover_rel := Seq_Cons (Ret tt) (Seq_Nil); |}.


(* Check that we can actually translate programs *)

Import DB.
Definition test00 :=
  (db <- Call New; db <- Call (Add db 2); db <- Call (Add db 4); Call (Avg db))%proc.

Lemma test00_compile sTy w :
  exists (e': proc _ nat), compile_rel impl sTy w test00 e'.
Proof.
  eexists.
  eapply cr_bind; intros.
  { repeat econstructor. }
  eapply cr_bind; intros.
  { repeat econstructor. eauto. }
  eapply cr_bind; intros.
  { repeat econstructor. eauto. }
  repeat econstructor. eauto.
Qed.
