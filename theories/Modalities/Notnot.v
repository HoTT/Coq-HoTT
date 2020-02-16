(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import Modality.

Local Open Scope path_scope.


(** * The double negation modality *)

(** This is Exercise 7.12 in the book.  Note that it is (apparently) *not* accessible unless we assume propositional resizing. *)

Definition NotNot `{Funext} : Modality.
Proof.
  snrapply easy_modality.
  - intros X; exact (~ (~ X)).
  - intros T x nx; exact (nx x).
  - intros A B f z nBz.
    apply z; intros a.
    exact (f a (transport (fun x => ~ (B x))
                          (path_ishprop _ _)
                          nBz)).
  - intros A B f a.
    apply path_ishprop.
  - intros A z z'.
    refine (isequiv_iff_hprop _ _).
    intros; apply path_ishprop.
Defined.
