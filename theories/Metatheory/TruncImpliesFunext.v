(** * Propositional truncation implies function extensionality *)

Require Import HoTT.Basics HoTT.Truncations HoTT.Types.Bool.
Require Import Metatheory.Core Metatheory.FunextVarieties Metatheory.ImpredicativeTruncation.

(** Assuming that we have a propositional truncation operation with a definitional computation rule, we can prove function extensionality.  Since we can't assume we have a definitional computation rule, we work with the propositional truncation defined as a HIT, which does have a definitional computation rule. *)

(** We can construct an interval type as [Trunc -1 Bool]. *)
Local Definition interval := Trunc (-1) Bool.

Local Definition interval_rec (P : Type) (a b : P) (p : a = b)
  : interval -> P.
Proof.
  (* We define this map by factoring it through the type [{ x : P & x = b}], which is a proposition since it is contractible. *)
  refine ((pr1 : { x : P & x = b } -> P) o _).
  apply Trunc_rec.
  intros [].
  - exact (a; p).
  - exact (b; idpath).
Defined.

Local Definition seg : tr true = tr false :> interval
  := path_ishprop _ _.

(** From an interval type, and thus from truncations, we can prove function extensionality. See IntervalImpliesFunext.v for an approach that works with an interval defined as a HIT. *)
Definition funext_type_from_trunc : Funext_type
  := WeakFunext_implies_Funext (NaiveFunext_implies_WeakFunext
    (fun A P f g p =>
      let h := fun (x:interval) (a:A) =>
        interval_rec _ (f a) (g a) (p a) x
        in ap h seg)).

(** ** Function extensionality implies an interval type *)

(** Assuming [Funext] (and not propositional resizing), the construction [Trm] in ImpredicativeTruncation.v applied to [Bool] gives an interval type with definitional computation on the end points.  So we see that function extensionality is equivalent to the existence of an interval type. *)

Section AssumeFunext.
  Context `{Funext}.

  Definition finterval := Trm Bool.

  Definition finterval_rec (P : Type) (a b : P) (p : a = b)
    : finterval -> P.
  Proof.
    refine ((pr1 : { x : P & x = b } -> P) o _).
    apply Trm_rec.
    intros [].
    - exact (a; p).
    - exact (b; idpath).
  Defined.

  (** As an example, we check that it computes on [true]. *)
  Definition finterval_rec_beta (P : Type) (a b : P) (p : a = b)
    : finterval_rec P a b p (trm true) = a
    := idpath.

  Definition fseg : trm true = trm false :> finterval
    := path_ishprop _ _.

  (** To verify that our interval type is good enough, we use it to prove function extensionality. *)
  Definition funext_type_from_finterval : Funext_type
    := WeakFunext_implies_Funext (NaiveFunext_implies_WeakFunext
      (fun A P f g p =>
        let h := fun (x:finterval) (a:A) =>
          finterval_rec _ (f a) (g a) (p a) x
          in ap h fseg)).

End AssumeFunext.
