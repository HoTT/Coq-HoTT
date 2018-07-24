(* -*- mode: coq; mode: visual-line -*- *)

(** * Theorems about trunctions *)

Require Import HoTT.Basics FunextVarieties.
Require Import HIT.Truncations HoTT.Types.Bool.

(** ** We can construct an interval type as [Trunc -1 Bool] *)

Local Definition interval := Trunc -1 Bool.

Local Definition interval_rec (P : Type) (a b : P) (p : a = b)
: interval -> P.
Proof.
  unfold interval; intro x.
  cut { pt : P | pt = b }.
  { apply pr1. }
  { strip_truncations.
    refine (if x then a else b; _).
    destruct x; (reflexivity || assumption). }
Defined.

Local Definition seg : tr true = tr false :> interval
  := path_ishprop _ _.

(** ** From an interval type, and thus from truncations, we can prove function extensionality. *)

Definition funext_type_from_trunc : Funext_type
  := WeakFunext_implies_Funext (NaiveFunext_implies_WeakFunext
    (fun A P f g p =>
      let h := fun (x:interval) (a:A) =>
        interval_rec _ (f a) (g a) (p a) x
        in ap h seg)).

(** As justified by the above proof, we may assume [Funext] given [Trunc]. *)
Global Instance funext_from_trunc : Funext.
Admitted.
