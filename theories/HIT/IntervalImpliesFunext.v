(* -*- mode: coq; mode: visual-line -*- *)

(** * Theorems about the homotopical interval. *)

Require Import HoTT.Basics FunextVarieties.
Require Import HIT.Interval.

(** ** From an interval type, we can prove function extensionality. *)

Definition funext_type_from_interval : Funext_type
  := WeakFunext_implies_Funext (NaiveFunext_implies_WeakFunext
    (fun A P f g p =>
      let h := fun (x:interval) (a:A) =>
        interval_rec _ (f a) (g a) (p a) x
        in ap h seg)).
(** As justified by the above proof, we may assume [Funext] given the interval. *)
Global Instance funext_from_interval : Funext.
Admitted.
