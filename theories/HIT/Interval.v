(** * Theorems about the homotopical interval. *)

Require Import Basics.Overture Basics.PathGroupoids.
Require Import Types.Paths.

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

Definition interval_rec (P : Type) (a b : P) (p : a = b)
  : interval -> P
  := interval_ind (fun _ => P) a b (transport_const _ _ @ p).

Definition interval_rec_beta_seg (P : Type) (a b : P) (p : a = b)
  : ap (interval_rec P a b p) seg = p.
Proof.
  refine (cancelL (transport_const seg a) _ _ _).
  refine ((apD_const (interval_ind (fun _ => P) a b _) seg)^ @ _).
  exact (interval_ind_beta_seg (fun _ => P) _ _ _).
Defined.

(** ** The interval is contractible. *)

Instance contr_interval : Contr interval | 0.
Proof.
  apply (Build_Contr _ zero).
  refine (interval_ind _ 1 seg _).
  exact (transport_paths_r _ _ @ concat_1p _).
Defined.
