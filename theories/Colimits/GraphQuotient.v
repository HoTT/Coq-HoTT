Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids.

(** * Quotient of a graph *)

Local Unset Elimination Schemes.

Module Export GraphQuotient.

  Private Inductive GraphQuotient@{i j u}
    {A : Type@{i}} (R : A -> A -> Type@{j}) : Type@{u} :=
  | gq : A -> GraphQuotient R.

  Arguments gq {A R} a.

  Axiom gqglue@{i j u}
    : forall {A : Type@{i}} {R : A -> A -> Type@{j}} {a b : A},
    R a b -> paths@{u} (@gq A R a) (gq b).

  Definition GraphQuotient_ind@{i j u k} {A : Type@{i}} {R : A -> A -> Type@{j}}
    (P : GraphQuotient@{i j u} R -> Type@{k})
    (gq' : forall a, P (gq@{i j u} a))
    (gqglue' : forall a b (s : R a b), gqglue@{i j u} s # gq' a = gq' b)
    : forall x, P x := fun x =>
    match x with
    | gq a => fun _ => gq' a
    end gqglue'.

  Axiom GraphQuotient_ind_beta_gqglue@{i j u k}
  : forall  {A : Type@{i}} {R : A -> A -> Type@{j}}
    (P : GraphQuotient@{i j u} R -> Type@{k})
    (gq' : forall a, P (gq a))
    (gqglue' : forall a b (s : R a b), gqglue s # gq' a = gq' b)
    (a b: A) (s : R a b),
    apD (GraphQuotient_ind P gq' gqglue') (gqglue s) = gqglue' a b s.

End GraphQuotient.

Arguments gq {A R} a.


Definition GraphQuotient_rec {A R P} (c : A -> P) (g : forall a b, R a b -> c a = c b)
  : GraphQuotient R -> P.
Proof.
  srapply GraphQuotient_ind.
  1: exact c.
  intros a b s.
  refine (transport_const _ _ @ g a b s).
Defined.

Definition GraphQuotient_rec_beta_gqglue {A R P}
  (c : A -> P) (g : forall a b, R a b -> c a = c b)
  (a b : A) (s : R a b)
  : ap (GraphQuotient_rec c g) (gqglue s) = g a b s.
Proof.
  unfold GraphQuotient_rec.
  refine (cancelL _ _ _ _ ).
  refine ((apD_const _ _)^ @ _).
  rapply GraphQuotient_ind_beta_gqglue.
Defined.
