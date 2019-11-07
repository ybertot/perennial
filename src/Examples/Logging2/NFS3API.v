From Coq Require Import List.

From Perennial Require Export Lib.
Require Import ExMach.ExMachAPI.
Import RelationNotations.

Module NFS3.

  Definition nfs3_fh := nat.
  Context {nfs3_filename : Type}.
  Context `{!EqDecision nfs3_filename}.
  Context `{!Countable nfs3_filename}.
  Context {nfs3_attr : Type}.
  Context {nfs3_buf : Type}.
  Context `{!EqDecision nfs3_buf}.
  Context `{!Countable nfs3_buf}.

  Inductive Op : Type -> Type :=
  | Lookup (d : nfs3_fh) (n : nfs3_filename) : Op (option nfs3_fh)
  | Getattr (f : nfs3_fh) : Op (option nfs3_attr)
  | Read (f : nfs3_fh) (off : nat) (count : nat) : Op (option nfs3_buf)
  | Write (f : nfs3_fh) (off : nat) (buf : nfs3_buf) : Op (option nat)
  | Create (d : nfs3_fh) (n : nfs3_filename) : Op (option nfs3_fh)
  | Commit (f : nfs3_fh) : Op unit
  .

  Record file_state := mkFileState {
    latest:  nfs3_buf;
    pending: gset nfs3_buf;
  }.

  Inductive inode_state :=
  | Dir : gmap nfs3_filename nfs3_fh -> inode_state
  | File : file_state -> inode_state
  .

  Definition State := gmap nfs3_fh inode_state.

  Parameter inode_attrs : inode_state -> nfs3_attr.
  Parameter read_data : nfs3_buf -> nat -> nat -> nfs3_buf.
  Parameter write_data : nfs3_buf -> nat -> nfs3_buf -> nfs3_buf.
  Parameter len_data : nfs3_buf -> nat.
  Parameter empty_data : nfs3_buf.
  Context `{!ElemOf nfs3_fh (gmap nfs3_fh inode_state)}.

  Definition inode_crash (s : option inode_state) (s' : option inode_state) : Prop :=
    match s, s' with
    | None, None => True
    | Some (Dir d), Some (Dir d') => d = d'
    | Some (File (mkFileState latest pending)), Some (File (mkFileState latest' pending')) =>
      latest' ∈ pending ∪ {[latest]} /\ pending' = ∅
    | _, _ => False
    end.

  Definition inode_finish (s : inode_state) : inode_state :=
    match s with
    | Dir d => s
    | File (mkFileState latest pending) =>
      File (mkFileState latest ∅)
    end.

  Definition dynamics : Dynamics Op State :=
    {| step T (op: Op T) :=
          match op with
          | Lookup d n =>
            i <- reads (fun s => s !! d);
            match i with
            | None => pure None
            | Some (File _) => pure None
            | Some (Dir dents) => pure (dents !! n)
            end
          | Getattr fh =>
            i <- reads (fun s => s !! fh);
            match i with
            | None => pure None
            | Some i => pure (Some (inode_attrs i))
            end
          | Read fh off count =>
            i <- reads (fun s => s !! fh);
            match i with
            | None => pure None
            | Some (Dir _) => pure None
            | Some (File (mkFileState latest _)) =>
              pure (Some (read_data latest off count))
            end
          | Write fh off buf =>
            i <- reads (fun s => s !! fh);
            match i with
            | None => pure None
            | Some (Dir _) => pure None
            | Some (File (mkFileState latest pending)) =>
              _ <- puts (fun s =>
                <[fh := File (mkFileState (write_data latest off buf) (pending ∪ {[latest]}))]> s);
              pure (Some (len_data buf))
            end
          | Create d n =>
            i <- reads (fun s => s !! d);
            match i with
            | None => pure None
            | Some (File _) => pure None
            | Some (Dir dents) =>
              fh <- such_that (fun s fh => fh ∉ s);
              _ <- puts (fun s =>
                <[fh := File (mkFileState empty_data ∅)]> s);
              pure (Some fh)
            end
          | Commit fh =>
            i <- reads (fun s => s !! fh);
            match i with
            | None => pure tt
            | Some (Dir _) => pure tt
            | Some (File (mkFileState vbuf pending)) =>
              _ <- puts (fun s =>
                <[fh := File (mkFileState vbuf ∅)]> s);
              pure tt
            end
          end;
       crash_step :=
          s' <- such_that (fun (s s' : State) => forall fh, inode_crash (s !! fh) (s' !! fh));
          _ <- puts (fun _ => s');
          pure tt;
       finish_step :=
          _ <- puts (fun s => fmap inode_finish s);
          pure tt;
    |}.

  Lemma crash_total_ok (s: State):
    exists s', dynamics.(crash_step) s (Val s' tt).
  Proof.
    repeat (eexists; econstructor).
    econstructor. intros.
    instantiate (1 := fmap inode_finish s).
    rewrite lookup_fmap.
    destruct (s !! fh) eqn:He; rewrite He; simpl; auto.
    destruct i; simpl; auto.
    destruct f; simpl; auto.
    intuition.
    eapply elem_of_union; right.
    eapply elem_of_singleton; auto.
  Qed.

  Lemma crash_non_err_ok (s: State) ret:
    dynamics.(crash_step) s ret -> ret ≠ Err.
  Proof.
    intros.
    destruct ret; try congruence.
    inversion H; clear H.
    inversion H0; clear H0.
    inversion H0; clear H0.
    inversion H; clear H.
    inversion H0; clear H0.
    inversion H; clear H.
    inversion H1; clear H1.
    inversion H; clear H.
    inversion H; clear H.
    inversion H1; clear H1.
    inversion H; clear H.
    inversion H5; clear H5.
  Qed.

  Lemma finish_total_ok (s: State):
    exists s', dynamics.(finish_step) s (Val s' tt).
  Proof.
    repeat (eexists; econstructor).
  Qed.

  Lemma finish_non_err_ok (s: State) ret:
    dynamics.(finish_step) s ret -> ret ≠ Err.
  Proof.
    intros.
    destruct ret; try congruence.
    inversion H; clear H.
    inversion H0; clear H0.
    inversion H0; clear H0.
    inversion H; clear H.
    inversion H0; clear H0.
    inversion H; clear H.
    inversion H1; clear H1.
  Qed.

  Definition l : Layer Op :=
    {| Layer.OpState := State;
       sem := dynamics;
       trace_proj := fun _ => nil;
       crash_preserves_trace := fun _ _ _ => eq_refl;
       crash_total := crash_total_ok;
       finish_total := finish_total_ok;
       crash_non_err := crash_non_err_ok;
       finish_non_err := finish_non_err_ok;
       initP := fun s => s = ∅ |}.

End NFS3.
