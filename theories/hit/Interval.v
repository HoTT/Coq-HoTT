(* -*- mode: coq; mode: visual-line -*- *)

(** * Theorems about the homotopical interval. *)

Require Import HoTT.Basics.
Require Import Types.Sigma Types.Forall Types.Paths.
Local Open Scope path_scope.


Module Export Interval.

Private Inductive interval : Type0 :=
  | zero : interval
  | one : interval.

Axiom seg : zero = one.

Definition interval_ind (P : interval -> Type)
  (a : P zero) (b : P one) (p : seg # a = b)
  : forall x:interval, P x
  := fun x => (match x return _ -> P x with
                | zero => fun _ => a
                | one  => fun _ => b
              end) p.

Axiom interval_ind_beta_seg : forall (P : interval -> Type)
  (a : P zero) (b : P one) (p : seg # a = b),
  apD (interval_ind P a b p) seg = p.

End Interval.

(*   Should fail:
Lemma test (P : interval -> Type) (a : P zero) (b : P one)
      (p p' : seg # a = b) :
    interval_ind P a b p = interval_ind P a b p'.
reflexivity.
*)


Definition interval_rec (P : Type) (a b : P) (p : a = b)
  : interval -> P
  := interval_ind (fun _ => P) a b (transport_const _ _ @ p).

Definition interval_rec_beta_seg (P : Type) (a b : P) (p : a = b)
  : ap (interval_rec P a b p) seg = p.
Proof.
  refine (cancelL (transport_const seg a) _ _ _).
  refine ((apD_const (interval_ind (fun _ => P) a b _) seg)^ @ _).
  refine (interval_ind_beta_seg (fun _ => P) _ _ _).
Defined.

(** ** The interval is contractible. *)

Global Instance contr_interval : Contr interval | 0.
Proof.
  exists zero.
  refine (interval_ind _ 1 seg _).
  refine (transport_paths_r _ _ @ concat_1p _).
Defined.
