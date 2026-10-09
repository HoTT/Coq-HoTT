From HoTT Require Import Basics WildCat.Core WildCat.NatTrans.

(** Treat parsing warnings as errors so these tests cannot rely on Rocq's deprecated level tolerance. *)
Local Set Warnings "+parsing".

Section PointedTransformationNotation.
  Context {B C : Type} `{Is1Cat B, Is1Gpd C}
    `{IsPointed B, IsPointed C}.
  Context (F G K : B -->* C).

  Succeed Definition test (h : F $=>* G)
    : h ^*$ = ptransformation_inverse F G h := 1.

  (** Inversion binds more tightly than function application and composes with other postfix notations. *)
  Succeed Definition test (h : F $=>* G) (f : (G $=>* F) -> B)
    : f h ^*$ = f (ptransformation_inverse F G h) := 1.
  Succeed Definition test (h : F $=>* G) (b : B)
    : h ^*$ .1 b = (ptransformation_inverse F G h).1 b := 1.
  Succeed Definition test (h : F $=>* G)
    : h ^*$ ^*$
      = ptransformation_inverse G F (ptransformation_inverse F G h) := 1.

  (** Inversion binds more tightly than composition on either side. *)
  Succeed Definition test (h : G $=>* F) (k : G $=>* K)
    : h ^*$ $@* k
      = ptransformation_compose (ptransformation_inverse G F h) k := 1.
  Succeed Definition test (h : F $=>* G) (k : K $=>* G)
    : h $@* k ^*$
      = ptransformation_compose h (ptransformation_inverse K G k) := 1.
  Succeed Definition test (h : F $=>* G) (k : G $=>* K)
    : (h $@* k) ^*$
      = ptransformation_inverse F K (ptransformation_compose h k) := 1.
End PointedTransformationNotation.
