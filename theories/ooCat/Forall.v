(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.
Require Import ooCat.Cat1.

Generalizable Variables m n p A B C.

(** * Forall (oo,n)-categories (with plain types as base) *)

(** ** Forall (oo,n)-categories *)

(** [forall] preserves globular types. *)
CoFixpoint isglob_forall `(B : A -> Type) `(forall a, IsGlob n (B a))
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
           {f g : forall a, B a}
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
           {f g : forall a, B a}
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

(** ** Displayed forall (oo,n)-categories *)

(** Dependent [forall] preserves globular types. *)
CoFixpoint isdglob_forall
           {A : Type} (B : A -> Type) (C : forall a, B a -> Type)
           `(forall a, IsGlob m (B a)) `(forall a, IsDGlob n (C a))
  : IsDGlob n (fun (f:forall a, B a) => forall a, C a (f a)).
Proof.
  unshelve econstructor.
  - intros f g p u v.
    exact (forall a:A, DHom (p a) (u a) (v a)).
  - intros f g u v.
    rapply isdglob_forall.
Defined.

Global Existing Instance isdglob_forall.

(** Postcomposing and precomposing between dependent [forall] types preserves displayed 0-coherent oo-functors. *)
CoFixpoint isdfunctor0_postcompose {m n mm nn A} (B C : A -> Type)
           `{forall a, IsGlob m (B a)} `{forall a, IsGlob n (C a)}
           (BB : forall a, B a -> Type) (CC : forall a, C a -> Type)
           `{!forall a, IsDGlob mm (BB a)} `{!forall a, IsDGlob nn (CC a)}
           (F : forall a, B a -> C a) {Ff : forall a, IsFunctor0 (F a)}
           (FF : forall a b, BB a b -> CC a (F a b))
           {FFf : forall a, IsDFunctor0 (F a) (FF a)}
  : IsDFunctor0 (fun (f:forall a:A, B a) => (fun a:A => F a (f a)))
                (fun (f:forall a:A, B a) (g:forall a, BB a (f a))
                 => (fun a:A => FF a (f a) (g a))).
Proof.
  unshelve econstructor.
  - cbn; intros f g u v p q a.
    exact (dfmap (F a) (FF a) (q a)).
  - intros; rapply isdfunctor0_postcompose.
Defined.

CoFixpoint isdfunctor0_precompose {m n A B}
           (h : A -> B)
           (C : B -> Type) `{forall a, IsGlob m (C a)}
           (D : forall b:B, C b -> Type) `{forall a, IsDGlob n (D a)}
  : IsDFunctor0 (fun (f:forall b:B, C b) => (fun a => f (h a)))
                (fun (f:forall b:B, C b) (g:forall b, D b (f b))
                 => (fun a:A => g (h a))).
Proof.
  unshelve econstructor.
  - cbn; intros f g u v p q a.
    exact (q (h a)).
  - intros; rapply isdfunctor0_precompose.
Defined.

Global Existing Instances isdfunctor0_postcompose isdfunctor0_precompose.

(** Dependent [forall] preserves 0-coherent displayed oo-categories. *)
CoFixpoint isdcat0_forall
           {A : Type} (B : A -> Type) (C : forall a, B a -> Type)
           `(forall a, IsGlob m (B a)) `(forall a, IsCat0 m (B a))
           `(forall a, IsDGlob n (C a)) `(forall a, IsDCat0 n (C a))
  : IsDCat0 n (fun (f:forall a, B a) => forall a, C a (f a)).
Proof.
  unshelve econstructor; cbn.
  - intros f g h u v w q p s r a.
    exact (s a $oD r a).
  - intros f u a.
    exact (dcat_id (u a)).
  - intros; rapply isdfunctor0_postcompose.
  - intros; rapply isdfunctor0_postcompose.
  - intros ? f g u v p pe r a.
    pose (isqiso_from_forall B p a).
    exact (dgpd_inv (r a)).
  - intros; rapply isdcat0_forall.
Defined.

Global Existing Instance isdcat0_forall.
