(* -*- mode: coq; mode: visual-line -*- *)

(** * Theorems about the homotopical interval. *)

Require Import HoTT.Basics.
Require Import types.Sigma types.Forall types.Paths.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

Module Export Interval.

Private Inductive interval : Type1 :=
  | zero : interval
  | one : interval.

Axiom seg : zero = one.

Definition interval_rect (P : interval -> Type)
  (a : P zero) (b : P one) (p : seg # a = b)
  : forall x:interval, P x
  := fun x => (match x return _ -> P x with
                | zero => fun _ => a
                | one  => fun _ => b
              end) p.

Axiom interval_rect_beta_seg : forall (P : interval -> Type)
  (a : P zero) (b : P one) (p : seg # a = b),
  apD (interval_rect P a b p) seg = p.

End Interval.

(*   Should fail:
Lemma test (P : interval -> Type) (a : P zero) (b : P one)
      (p p' : seg # a = b) :
    interval_rect P a b p = interval_rect P a b p'.
reflexivity.
*)


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

(** ** The interval is contractible. *)

Global Instance contr_interval : Contr interval | 0.
Proof.
  exists zero.
  refine (interval_rect _ 1 seg _).
  refine (transport_paths_r _ _ @ concat_1p _).
Defined.
