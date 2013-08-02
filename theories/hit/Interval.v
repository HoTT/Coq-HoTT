(* -*- mode: coq; mode: visual-line -*- *)

(** * Theorems about the homotopical interval. *)

Require Import Overture PathGroupoids Contractible Equivalences.
Require Import FunextVarieties.
Require Import Sigma Forall Paths.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

Module Export Interval.

Local Inductive interval : Type :=
  | zero : interval
  | one : interval.

Axiom seg : zero = one.

Definition interval_rect (P : interval -> Type)
  (a : P zero) (b : P one) (p : seg # a = b)
  : forall x:interval, P x
  := fun x => match x return P x with
                | zero => a
                | one  => b
              end.

Axiom interval_rect_beta_seg : forall (P : interval -> Type)
  (a : P zero) (b : P one) (p : seg # a = b),
  apD (interval_rect P a b p) seg = p.

End Interval.

Definition interval_rectnd (P : Type) (a b : P) (p : a = b)
  : interval -> P
  := interval_rect (fun _ => P) a b (transport_const _ _ @ p).

Definition interval_rectnd_beta_seg (P : Type) (a b : P) (p : a = b)
  : ap (interval_rectnd P a b p) seg = p.
Proof.
  refine (cancelL (transport_const seg a) _ _ _).
  refine ((apD_const (interval_rect (fun _ => P) a b _) seg)^ @ _).
  refine (interval_rect_beta_seg (fun _ => P) _ _ _).
Defined.

(** *** From an interval type, we can prove function extensionality. *)

Instance funext_from_interval : Funext | 0
  := WeakFunext_implies_Funext (NaiveFunext_implies_WeakFunext
    (fun A P f g p =>
      let h := fun (x:interval) (a:A) =>
        interval_rectnd _ (f a) (g a) (p a) x
        in ap h seg)).

(** *** The interval is contractible. *)

Instance contr_interval : Contr interval | 0.
Proof.
  exists zero.
  refine (interval_rect _ 1 seg _).
  refine (transport_paths_r _ _ @ concat_1p _).
Defined.
