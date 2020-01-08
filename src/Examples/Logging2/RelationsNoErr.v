Require Import Setoid.
Require Import Morphisms.
Require Classical_Prop.

Require Import Tactical.Propositional.
Require Import Tactical.Misc.
From Classes Require Import Classes.

Set Implicit Arguments.
Generalizable All Variables.
(* for compatibility with coq master *)
Set Warnings "-undeclared-scope".

Section TransitionRelations.
  Inductive Return (B T: Type) : Type :=
  | Val (b: B) (t: T).

  Definition relation A B T := A -> Return B T -> Prop.

  (** Several operations on relations *)
  Definition and_then {A B C} {T1 T2}
             (r1: relation A B T1)
             (r2: T1 -> relation B C T2) :
    relation A C T2 :=
    fun x mz => exists o1 y, r1 x (Val y o1) /\ (r2 o1) y mz.

  Notation "p1 ;; p2" := (and_then p1 (fun _ => p2))
                           (at level 55, p2 at next level, right associativity).
  Notation "x <- p1 ; p2" := (and_then p1 (fun x => p2))
                               (at level 54, right associativity).

  Definition pure A T (o0:T) : relation A A T :=
    fun x y => Val x o0 = y.

  Definition identity {A} {T} : relation A A T :=
    fun x y => exists t, Val x t = y.

  Definition any {A B} {T} : relation A B T :=
    fun x y => True.

  Definition none {A B} {T} : relation A B T :=
    fun x y => False.

  Definition reads {A} {T} (f: A -> T) : relation A A T :=
    fun x y => Val x (f x) = y.

  Definition puts {A} (f: A -> A) : relation A A unit :=
    fun x y => y = Val (f x) tt.

  Definition fst_lift {A1 A2 B T} (r: relation A1 A2 T) : relation (A1 * B) (A2 * B) T :=
    fun '(a, b) y =>
      match y with
      | Val (a', b') t => r a (Val a' t) /\ b = b'
      end.

  Definition snd_lift {A1 A2 B T} (r: relation A1 A2 T) : relation (B * A1) (B * A2) T :=
    fun '(b, a) y =>
      match y with
      | Val (b', a') t => r a (Val a' t) /\ b = b'
      end.

  Definition zoom A C (proj: A -> C) (inj: C -> A -> A) T (r: relation C C T) : relation A A T :=
    fun s y =>
      match y with
      | Val s' t => r (proj s) (Val (proj s') t) /\ s' = inj (proj s') s
      end.

  Inductive such_that {A T} (f: A -> T -> Prop) : relation A A T :=
  | such_that_holds : forall s v, f s v -> such_that f s (Val s v).

  Definition predicate A := A -> Prop.
  (* TODO: should failure of a test be error? *)
  Definition test {A} (P: predicate A) : relation A A unit :=
    fun x y => P x /\ Val x tt = y.

  Definition rel_or A B T (r1 r2: relation A B T) : relation A B T :=
    fun x y => r1 x y \/ r2 x y.

  Infix "+" := rel_or.
End TransitionRelations.

Module RelationNotations.
  (* Declare Scope relation_scope. *)
  Delimit Scope relation_scope with rel.
  Open Scope relation_scope.
  Notation "p1 ;; p2" := (and_then p1 (fun _ => p2))
  (at level 100, p2 at level 200, only parsing, right associativity)
  : relation_scope.
  (* TODO: experiment more with printing boxes *)
  Notation "x <- p1 ; p2" := (and_then p1 (fun x => p2))
                              (at level 20, p1 at level 100, p2 at level 200, right associativity,
                               format "'[' x  <-  '[v    ' p1 ']' ; ']'  '/' p2")
                             : relation_scope.
  Notation "'let!' x <- p1 ; p2" := (and_then p1 (fun x => p2))
                              (at level 20, x pattern, p1 at level 100, p2 at level 200, right associativity,
                               format "'[' 'let!' x  <-  '[v    ' p1 ']' ; ']'  '/' p2")
                             : relation_scope.
  Ltac destruct_return :=
    match goal with
    | [ y : Return _ _  |- _ ] => destruct y
    end.

End RelationNotations.
