From HoTT.Basics Require Import Overture.

Section DependentRewriting.
  Universes a b.
  Context {A : Type@{a}} (x : A)
    (P : forall y : A, x = y -> Type@{b}) (d : P x idpath).

  Definition dependent_rewrite (y : A) (p : x = y) : P y p.
  Proof.
    rewrite <- p.
    exact d.
  Defined.

  Goal dependent_rewrite x idpath = d.
  Proof.
    reflexivity.
  Qed.
End DependentRewriting.

Fail Check internal_paths_rew_dep.

Set Printing Universes.
Print dependent_rewrite.
