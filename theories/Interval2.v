Require Import Basics.Overture Basics.Tactics.
Require Import Basics.PathGroupoids Types.Paths.

Set Universe Minimization ToSet.
Unset Universe Polymorphism.

Symbol Interval : Type0.
Symbol i0 : Interval.
Symbol i1 : Interval.
Symbol seg : i0 = i1.


Symbol Interval_ind@{u}
  : forall (P : Interval -> Type@{u})
      (a : P i0) (b : P i1) (p : seg # a = b),
      forall x, P x.

Symbol Interval_rec@{u} : forall (P : Type@{u}) (a b : P) (p : a = b), Interval -> P.


Rewrite Rule interval_rewrite :=
| Interval_ind ?P ?a ?b ?p i0 => ?a
| Interval_ind ?P ?a ?b ?p i1 => ?b
| apD (Interval_ind ?P ?a ?b ?p) seg => ?p
| ap (Interval_rec ?P ?a ?b ?p) seg => ?p
.


Require Import Metatheory.Core Metatheory.FunextVarieties.

Definition interval_rec (P : Type) (a b : P) (p : a = b)
  : Interval -> P
  := Interval_ind (fun _ => P) a b (transport_const _ _ @ p).

Definition funext_type_from_interval : Funext_type
  := WeakFunext_implies_Funext (NaiveFunext_implies_WeakFunext
    (fun A P f g p =>
      let h := fun (x:Interval) (a:A) =>
        interval_rec _ (f a) (g a) (p a) x
        in ap h seg)).


Definition path_forall {A : Type} {P : A -> Type} (f g : forall x : A, P x)
  : f == g -> f = g.
Proof.
  refine (@apD10 A P f g)^-1.
  apply funext_type_from_interval.
Defined.


Definition path_forall_1 A {P : A -> Type} (f : forall x, P x)
  : (path_forall f f (fun x => 1)) = 1.
Proof.
  cbn.
  unfold htpy_ind.

cbv.
  eflexivity.
  simpl.
  := eta_path_forall f f 1.




