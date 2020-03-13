(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.
Require Import ooCat.Cat1.

Generalizable Variables m n X A B.

(** * Product categories *)

(** For now, we assume that [A] and [B] have the same invertibility dimension.  We could instead let them be different and take the min for the dimension of the product. *)

CoFixpoint isglob_prod `{IsGlob n A} `{IsGlob n B}
  : IsGlob n (A * B).
Proof.
  unshelve econstructor.
  - intros [a1 b1] [a2 b2]; exact ((a1 $-> a2) * (b1 $-> b2)).
  - intros [a1 b1] [a2 b2]. rapply isglob_prod.
Defined.

Global Existing Instance isglob_prod.

CoFixpoint isfunctor0_prod
           `{IsGlob m A1} `{IsGlob n B1} `{IsGlob m A2} `{IsGlob n B2}
           (F1 : A1 -> B1) (F2 : A2 -> B2)
           `{!IsFunctor0 F1} `{!IsFunctor0 F2}
  : IsFunctor0 (fun z:A1*A2 => (F1 (fst z), F2 (snd z))).
Proof.
  simple notypeclasses refine (Build_IsFunctor0 _ _ _).
  - intros [a1 a2] [b1 b2] [f1 f2]; cbn.
    exact (fmap F1 f1 , fmap F2 f2).
  - intros; cbn; apply isfunctor0_prod; apply isfunctor0_fmap.
Defined.

CoFixpoint iscat0_prod `{IsCat0 n A} `{IsCat0 n B}
  : IsCat0 n (A * B).
Proof.
  unshelve econstructor.
  - intros [a1 b1] [a2 b2] [a3 b3] [f1 g1] [f2 g2].
    exact (f1 $o f2, g1 $o g2).
  - intros [a1 b1].
    exact (cat_id a1, cat_id b1).
  - intros [a1 b1] [a2 b2] [a3 b3] [h k]; cbn.
    apply isfunctor0_prod; apply isfunctor0_postcomp.
  - intros [a1 b1] [a2 b2] [a3 b3] [h k]; cbn.
    refine (isfunctor0_prod (fun g => g $o h) (fun g => g $o k)).
  - intros ? [a1 b1] [a2 b2] [f g]; exact (f^$, g^$).
  - intros; rapply iscat0_prod.
Defined.

Global Existing Instance iscat0_prod.

CoFixpoint isfunctor0_pair `{IsGlob m X} `{IsGlob n A} `{IsGlob n B}
           (F : X -> A) `{!IsFunctor0 F} (G : X -> B) `{!IsFunctor0 G}
  : IsFunctor0 (fun x => (F x, G x)).
Proof.
  simple notypeclasses refine (Build_IsFunctor0 _ _ _).
  - intros x y f; exact (fmap F f, fmap G f).
  - intros x y; rapply isfunctor0_pair.
Defined.

Global Existing Instance isfunctor0_pair.

(** TODO: HasEquivs, 1-coherent categories *)
