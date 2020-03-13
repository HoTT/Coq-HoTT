(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.
Require Import ooCat.Cat1.

(** * Forall oo-groupoids (with plain types as base) *)

(** [forall] preserves globular types. *)
CoFixpoint isglob_forall {n A} (B : A -> Type) `(forall a, IsGlob n (B a))
  : IsGlob n (forall a, B a).
Proof.
  exists (fun f g => forall a, f a $-> g a); intros.
  rapply isglob_forall.
Defined.

Global Existing Instance isglob_forall.

(** Postcomposing and precomposing between [forall] types preserves 0-coherent oo-functors.  (TODO: Should probably be generalized to sections.) *)
CoFixpoint isfunctor0_postcompose {m n A} (B C : A -> Type)
           `{forall a, IsGlob m (B a)} `{forall a, IsGlob n (C a)}
           (F : forall a, B a -> C a) `{!forall a, IsFunctor0 (F a)}
  : IsFunctor0 (fun f a => F a (f a)).
Proof.
  unshelve econstructor.
  - cbn; intros f g p a.
    exact (fmap (F a) (p a)).
  - intros; rapply isfunctor0_postcompose.
Defined.

CoFixpoint isfunctor0_precompose {n A B} (h : A -> B)
           (C : B -> Type) `{forall a, IsGlob n (C a)}
  : IsFunctor0 (fun f a => f (h a)).
Proof.
  unshelve econstructor.
  - cbn; intros f g p a.
    exact (p (h a)).
  - intros; rapply isfunctor0_precompose.
Defined.

Global Existing Instances isfunctor0_postcompose isfunctor0_precompose.

(** [forall] preserves 0-coherent oo-categories. *)
CoFixpoint iscat0_forall {n A} (B : A -> Type)
           {bg : forall a, IsGlob n (B a)} {bc : forall a, IsCat0 n (B a)}
  : IsCat0 n (forall a, B a).
Proof.
  unshelve econstructor; cbn.
  - intros f g h q p a; exact (q a $o p a).
  - intros f a; exact (cat_id (f a)).
  - intros; rapply isfunctor0_postcompose.
  - intros f g h p; rapply isfunctor0_postcompose.
  - intros ? f g p a. apply gpd_inv, p.
  - intros; rapply iscat0_forall.
Defined.

Global Existing Instance iscat0_forall.

(** A pointwise quasi-isomorphism in a [forall] is a quasi-isomorphism. *)
CoFixpoint isqiso_forall {n A} (B : A -> Type)
           {bg : forall a, IsGlob n (B a)} {bc : forall a, IsCat0 n (B a)}
           (f g : forall a, B a)
           (p : f $-> g) `{forall a, IsQIso (p a)}
  : IsQIso p.
Proof.
  unshelve econstructor.
  - exact (fun a => qiso_inv (p a)).
  - cbn; intros a. exact (qiso_issect (p a)).
  - cbn; intros a. exact (qiso_isretr (p a)).
  - rapply isqiso_forall. intros; exact (isqiso_qiso_issect (p a) _).
  - rapply isqiso_forall. intros; exact (isqiso_qiso_isretr (p a) _).
Defined.

(** And conversely. *)
CoFixpoint isqiso_from_forall {n A} (B : A -> Type)
           {bg : forall a, IsGlob n (B a)} {bc : forall a, IsCat0 n (B a)}
           (f g : forall a, B a)
           (p : f $-> g) `{!IsQIso p} (a : A)
  : IsQIso (p a).
Proof.
  unshelve econstructor.
  - exact (qiso_inv p a).
  - exact (qiso_issect p a).
  - exact (qiso_isretr p a).
  - exact (@isqiso_from_forall _ _ _ _ _ _ _ (qiso_issect p) (isqiso_qiso_issect p _) a).
  - exact (@isqiso_from_forall _ _ _ _ _ _ _ (qiso_isretr p) (isqiso_qiso_isretr p _) a).
Defined.

CoFixpoint hasequivs_forall {n A} (B : A -> Type)
           {bg : forall a, IsGlob n (B a)}
           {bc : forall a, IsCat0 n (B a)}
           {bh : forall a, HasEquivs n (B a)}
  : HasEquivs n (forall a, B a).
Proof.
  unshelve econstructor.
  - intros f g p; exact (forall a, CatIsEquiv (p a)).
  - intros f g p pe a; cbn.
    apply catie_isqiso; rapply isqiso_from_forall.
  - intros f g p pe; cbn.
    apply isqiso_forall; intros a.
    apply isqiso_catie, pe.
  - intros; rapply hasequivs_forall.
Defined.

Global Existing Instance hasequivs_forall.

(** TODO: 1-coherent functors and categories *)
