From HoTT.Basics Require Import Overture.

Section DependentRewriting.
  Universes a b.
  Context {A : Type@{a}} (x : A)
    (P : forall y : A, x = y -> Type@{b}) (d : P x idpath).

  (** Rewriting must not introduce any universe variables or constraints beyond the section context. *)
  Definition dependent_rewrite@{|} (y : A) (p : x = y) : P y p.
  Proof.
    rewrite <- p.
    exact d.
  Defined.

  Succeed Definition test@{|} : dependent_rewrite x idpath = d := 1.
End DependentRewriting.

Fail Check internal_paths_rew_dep.
