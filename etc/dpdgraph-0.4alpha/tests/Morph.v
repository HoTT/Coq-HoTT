Require Import Setoid.

Parameter F : Type.
Parameter Fequiv : F -> F -> Prop.

Axiom Fequiv_refl : forall f, Fequiv f f.
Axiom Fequiv_sym : forall f1 f2, Fequiv f1 f2 -> Fequiv f2 f1.
Axiom Fequiv_trans : forall f1 f2 f3, Fequiv f1 f2 -> Fequiv f2 f3 -> Fequiv f1 f3.

Add Parametric Relation : F Fequiv
  reflexivity proved by Fequiv_refl
  symmetry proved by Fequiv_sym
  transitivity proved by Fequiv_trans
as FequivR.

Parameter Fsmp : F -> F.

Add Parametric Morphism : Fsmp
  with signature  Fequiv ==> Fequiv
as FsmpM.
Proof.
Admitted.


Theorem rw : forall f1 f2,  Fequiv f2 f1 -> Fequiv f1 (Fsmp f1) -> Fequiv f1 (Fsmp f2).
Proof.
intros f1 f2 He H1.
rewrite He.
trivial.
Qed.


(* Print rw. *)
