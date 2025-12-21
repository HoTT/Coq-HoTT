Require Import Basics.Utf8 Basics.Overture Basics.Tactics Basics.Equivalences.
Require Import WildCat.Core.
Require Import WildCat.NatTrans.
Require Import WildCat.Equiv.
Require Import WildCat.Prod.
Require Import WildCat.Opposite.
Require Import WildCat.Yoneda.
Require Import WildCat.FunctorCat.
Require Import WildCat.Universe.
Require Import Types.Prod.

Generalizable Variables C D F G.

(** ** Notions of adjunctions in wild categories. *)

(** We try to capture a wild notion of (oo,1)-adjunctions since these are the ones that commonly appear in practice. Special cases include the standard 1-categorical adjunction.

There are notions of 2-adjunction/biadjunction/higher adjunction but it is not clear if this generality is useful.

We will define an adjunction to be an equivalence (in Type) between corresponding hom-types. This is a more immediately useful definition than others we can consider.

We should also be able to define "F having a left adjoint" as the initial object of a slice category C / F. However this seems like too much work for now, and it is not immediately obvious how it ties back to the adjunction isomorphism.

In the future, it ought to be possible to generalize this definition to live inside a given bicategory, however due to current structural issues in the WildCat library, writing down a usable definition of bicategory requires a lot of effort.
*)

(** * Definition of adjunction *)

(** ** Definition of adjunction *)

Record Adjunction {C D : Type} (F : C -> D) (G : D -> C)
  `{Is1Cat C, Is1Cat D, !Is0Functor F, !Is0Functor G} :=
{
  equiv_adjunction (x : C) (y : D) : (F x $-> y) <~> (x $-> G y) ;
  (** Naturality condition in both variables separately. *)
  (** The left variable is a bit trickier to state since we have opposite categories involved. *)
  is1natural_equiv_adjunction_l (y : D)
    :: Is1Natural (A := C^op) (yon y o F)
        (** We have to explicitly give a witness to the functoriality of [yon y o F]. *)
        (is0functor_F := is0functor_compose (A:=C^op) (B:=D^op) (C:=Type) _ _)
        (yon (G y)) (fun x => equiv_adjunction x y) ;
  (** Naturality in the right variable *)
  is1natural_equiv_adjunction_r (x : C)
    :: Is1Natural (opyon (F x)) (opyon x o G) (equiv_adjunction x) ;
}.

Arguments equiv_adjunction {C D F G
  isgraph_C is2graph_C is01cat_C is1cat_C
  isgraph_D is2graph_D is01cat_D is1cat_D
  is0functor_F is0functor_G} adj x y : rename.
Arguments is1natural_equiv_adjunction_l {C D F G
  isgraph_C is2graph_C is01cat_C is1cat_C
  isgraph_D is2graph_D is01cat_D is1cat_D
  is0functor_F is0functor_G} adj y : rename.
Arguments is1natural_equiv_adjunction_r {C D F G
  isgraph_C is2graph_C is01cat_C is1cat_C
  isgraph_D is2graph_D is01cat_D is1cat_D
  is0functor_F is0functor_G} adj x : rename.

Notation "F ⊣ G" := (Adjunction F G).


(** TODO: move but where? *)
Lemma fun01_profunctor {A B C D : Type} (F : A -> B) (G : C -> D)
  `{Is0Functor A B F, Is0Functor C D G}
  : Fun01 (A^op * C) (B^op * D).
Proof.
  snapply Build_Fun01.
  1: exact (functor_prod (F : A^op -> B^op) G).
  rapply is0functor_prod_functor. (* Typeclass search gets confused by the opposite categories. *)
Defined.

(** ** Natural equivalences coming from adjunctions. *)

(** There are various bits of data we would like to extract from adjunctions. *)
Section AdjunctionData.
  Context {C D : Type} {F : C -> D} {G : D -> C}
    `{Is1Cat C, Is1Cat D, !HasMorExt C, !HasMorExt D,
      !Is0Functor F, !Is0Functor G, !Is1Functor F, !Is1Functor G}
    (adj : Adjunction F G).

  Definition natequiv_adjunction_l (y : D)
    : NatEquiv (A := C^op) (yon y o F)
        (** We have to explicitly give a witness to the functoriality of [yon y o F]. *)
        (is0functor_F := is0functor_compose (A:=C^op) (B:=D^op) (C:=Type) _ _)
        (yon (G y)).
  Proof.
    napply Build_NatEquiv.
    apply (is1natural_equiv_adjunction_l adj).
  Defined.

  Definition natequiv_adjunction_r (x : C)
    : NatEquiv (opyon (F x)) (opyon x o G).
  Proof.
    napply Build_NatEquiv.
    apply (is1natural_equiv_adjunction_r adj).
  Defined.

  (** We also have the natural equivalence in both arguments at the same time. *)
  (** In order to manage the typeclass instances, we have to bundle them up into Fun01. *)
  Definition natequiv_adjunction
    : NatEquiv (A := C^op * D)
        (fun01_compose fun01_hom (fun01_profunctor F idmap))
        (fun01_compose fun01_hom (fun01_profunctor idmap G)).
  Proof.
    snapply Build_NatEquiv.
    1: intros [x y]; exact (equiv_adjunction adj x y).
    snapply Build_Is1Natural.
    intros [a b] [a' b'] [f g] K.
    refine (_ @ ap (fun x : a $-> G b' => x $o f)
      (is1natural_equiv_adjunction_r adj a b b' g K)).
    exact (is1natural_equiv_adjunction_l adj _ _ _ f (g $o K)).
  Defined.

  (** The counit of an adjunction *)
  Definition adjunction_counit : NatTrans idmap (G o F).
  Proof.
    snapply Build_NatTrans.
    { hnf. intros x.
      exact (equiv_adjunction adj x (F x) (Id _)). }
    snapply Build_Is1Natural.
    intros x x' f.
    apply GpdHom_path.
    refine (_^ @ _ @ _).
    1: exact (is1natural_equiv_adjunction_l adj _ _ _ f (Id _)).
    2: exact (is1natural_equiv_adjunction_r adj _ _ _ (fmap F f) (Id _)).
    simpl.
    apply equiv_ap'.
    apply path_hom.
    apply Square.vrefl.
  Defined.

  (** The unit of an adjunction *)
  Definition adjunction_unit : NatTrans (F o G) idmap.
  Proof.
    snapply Build_NatTrans.
    { hnf. intros y.
      exact ((equiv_adjunction adj (G y) y)^-1 (Id _)). }
    snapply Build_Is1Natural.
    intros y y' f.
    apply GpdHom_path.
    refine (_^ @ _ @ _).
    1: exact (is1natural_natequiv (natequiv_inverse
        (natequiv_adjunction_l _)) (G y') _ (fmap G f) _).
    2: exact (is1natural_natequiv (natequiv_inverse
        (natequiv_adjunction_r _)) _ _ _ (Id _)).
    simpl.
    apply equiv_ap_inv'.
    apply path_hom.
    apply Square.vrefl.
  Defined.

  Lemma triangle_helper1 x y f
    : equiv_adjunction adj x y f = fmap G f $o adjunction_counit x.
  Proof.
    refine (_ @ is1natural_equiv_adjunction_r adj _ _ _ _ _).
    by cbv; rewrite (cat_idr_strong f).
  Qed.

  Lemma triangle_helper2 x y g
    : (equiv_adjunction adj x y)^-1 g = adjunction_unit y $o fmap F g.
  Proof.
    epose (n1 := is1natural_natequiv
      (natequiv_inverse (natequiv_adjunction_l _)) _ _ _ _).
    clearbody n1; cbv in n1.
    refine (_ @ n1).
    by rewrite cat_idl_strong.
  Qed.

  Definition adjunction_triangle1
    : Transformation 
        (nattrans_comp
          (nattrans_prewhisker adjunction_unit F)
          (nattrans_postwhisker F adjunction_counit))
        (nattrans_id _).
  Proof.
    intros c.
    change (?x $-> _) with (x $-> Id (F c)).
    rewrite <- (eissect (equiv_adjunction adj _ _) (Id (F c))).
    cbv;rewrite <- (triangle_helper2 _ (F c) (adjunction_counit _)).
    exact (Id _).
  Qed.

  Definition adjunction_triangle2
    : Transformation
        (nattrans_comp
          (nattrans_postwhisker G adjunction_unit)
          (nattrans_prewhisker adjunction_counit G))
        (nattrans_id _).
  Proof.
    intros d.
    change (?x $-> _) with (x $-> Id (G d)).
    rewrite <- (eisretr (equiv_adjunction adj _ _) (Id (G d))).
    cbv;rewrite <- (triangle_helper1 (G d) _ (adjunction_unit _)).
    exact (Id _).
  Qed.

End AdjunctionData.

(** ** Building adjunctions *)

(** There are various ways to build an adjunction. *)

(** A natural equivalence between functors [D -> Type] which is also natural in the left. *)
Definition Build_Adjunction_natequiv_nat_left
  {C D : Type} (F : C -> D) (G : D -> C)
  `{Is1Cat C, Is1Cat D, !Is0Functor F, !Is0Functor G} 
  (e : forall x, NatEquiv (opyon (F x)) (opyon x o G))
  (is1nat_e : forall y, Is1Natural (A := C^op) (yon y o F)
      (** We have to explicitly give a witness to the functoriality of [yon y o F]. *)
      (is0functor_F := is0functor_compose (A:=C^op) (B:=D^op) (C:=Type) _ _)
      (yon (G y)) (fun x => e _ y))
  : Adjunction F G.
Proof.
  snapply Build_Adjunction.
  1: exact (fun x => e x).
  1: exact is1nat_e.
  intros x; exact (is1natural_natequiv (e x)).
Defined.

(** A natural equivalence between functors [C^op -> Type] which is also natural in the left. *)
Definition Build_Adjunction_natequiv_nat_right
  {C D : Type} (F : C -> D) (G : D -> C)
  `{Is1Cat C, Is1Cat D, !Is0Functor F, !Is0Functor G} 
  (e : forall y, NatEquiv (A := C^op) (yon y o F) (yon (G y))
    (is0functor_F := is0functor_compose (A:=C^op) (B:=D^op) (C:=Type) _ _))
  (is1nat_e : forall x, Is1Natural (opyon (F x)) (opyon x o G) (fun y => e y x))
  : Adjunction F G.
Proof.
  snapply Build_Adjunction.
  1: exact (fun x y => e y x).
  1: intros y; exact (is1natural_natequiv (e y)).
  exact is1nat_e.
Defined.

(** TODO: A natural equivalence between functors [C^op * D -> Type] *)

Section UnitCounitAdjunction.

  (** From the data of an adjunction: unit, counit, left triangle, right triangle *)
  Context {C D : Type} (F : C -> D) (G : D -> C)
  `{Is1Cat C, Is1Cat D, !Is0Functor F, !Is0Functor G,
    !Is1Functor F, !Is1Functor G}
  `{!HasMorExt C, !HasMorExt D}
  (ε : NatTrans (F o G) idmap)
  (η : NatTrans idmap (G o F))
  (t1 : Transformation 
    (nattrans_comp (nattrans_prewhisker ε F) (nattrans_postwhisker F η))
    (nattrans_id _))
  (t2 : Transformation
    (nattrans_comp (nattrans_postwhisker G ε) (nattrans_prewhisker η G))
    (nattrans_id _)).

  (** We can construct an equivalence between homs *)
  Local Definition γ a b : (F a $-> b) $<~> (a $-> G b).
  Proof.
    srapply equiv_adjointify.
    1: exact (fun x => fmap G x $o (η : _ $=> _) a).
    1: exact (fun x => (ε : _ $=> _) b $o fmap F x).
    + intros f.
      apply path_hom; simpl.
      refine ((fmap_comp G _ _ $@R _) $@ _).
      refine (cat_assoc _ _ _ $@ _).
      refine ((_ $@L (isnat η f)^$) $@ _).
      refine (cat_assoc_opp _ _ _ $@ _).
      refine (_ $@R _ $@ cat_idl _).
      exact (t2 b).
    + intros g.
      apply path_hom; simpl.
      refine ((_ $@L fmap_comp F _ _) $@ _).
      refine (cat_assoc_opp _ _ _ $@ _).
      refine (((isnat ε g) $@R _) $@ _).
      refine (cat_assoc _ _ _ $@ _).
      refine (_ $@L _ $@ cat_idr _).
      exact (t1 a).
  Defined.

  (** Which is natural in the left *)
  Lemma is1natural_γ_l (y : D)
    : Is1Natural (yon y o F) (yon (G y))
      (is0functor_F := is0functor_compose (A:=C^op) (B:=D^op) (C:=Type) _ _)
      (is0functor_G := is0functor_yon (G y))
      (fun x : C^op => γ x y).
  Proof.
    napply (is1natural_natequiv (natequiv_inverse
      (Build_NatEquiv (yon (G y)) (yon y o F) (fun x => (γ x y)^-1$) _))).
    napply is1natural_yoneda.
    napply is1functor_compose.
    1: napply is1functor_op; exact _.
    napply is1functor_opyon.
    exact hasmorext_op.
  Defined.

  (** And natural in the right. *)
  Lemma is1natural_γ_r x
    : Is1Natural (opyon (F x)) (fun x0 : D => opyon x (G x0)) (γ x).
  Proof.
    napply is1natural_opyoneda.
    exact _.
  Defined.

  (** Together this constructs an adjunction. *)
  Definition Build_Adjunction_unit_counit : Adjunction F G.
  Proof.
    snapply Build_Adjunction.
    - exact γ.
    - exact is1natural_γ_l.
    - exact is1natural_γ_r.
  Defined.

End UnitCounitAdjunction.

(** * Properties of adjunctions *)

(** ** Postcomposition adjunction *)
(** There are at least two easy proofs of the following on paper:
 1. Using ends: Hom(F*x,y) ≃ ∫_c Hom(Fxc,yc) ≃ ∫_c Hom(xc,Gyc) ≃ Hom(x,G*y)
 2. 2-cat theory: postcomp (-)* is a 2-functor so preserves adjunctions.
*)

Lemma adjunction_postcomp (C D J : Type)
  `{HasEquivs C, HasEquivs D, Is01Cat J} (F : Fun11 C D) (G : Fun11 D C)
  `{!HasMorExt C, !HasMorExt D, !HasMorExt (Fun01 J C), !HasMorExt (Fun01 J D)}
  : F ⊣ G -> fun11_fun01_postcomp (A:=J) F ⊣ fun11_fun01_postcomp (A:=J) G.
Proof.
  intros adj.
  srapply Build_Adjunction_unit_counit.
  - snapply Build_NatTrans.
    + intros K.
      exact (nattrans_prewhisker (adjunction_unit adj) K).
    + snapply Build_Is1Natural.
      intros K K' θ j.
      apply GpdHom_path.
      refine (_ @ is1natural_natequiv (natequiv_inverse
        (natequiv_adjunction_r adj _)) _ _ _ _).
      refine ((is1natural_natequiv (natequiv_inverse
        (natequiv_adjunction_l adj _)) _ _ _ _)^ @ _).
      cbn; rapply ap.
      refine(cat_idl_strong _ @ _^).
      apply cat_idr_strong.
  - snapply Build_NatTrans.
    + intros K.
      exact (nattrans_prewhisker (adjunction_counit adj) K).
    + snapply Build_Is1Natural.
      intros K K' θ j.
      apply GpdHom_path.
      refine (_ @ is1natural_natequiv
        (natequiv_adjunction_r adj _) _ _ _ _).
      refine ((is1natural_natequiv
        (natequiv_adjunction_l adj _) _ _ _ _)^ @ _).
      cbn; rapply ap.
      refine(cat_idl_strong _ @ _^).
      apply cat_idr_strong.
  - exact (trans_prewhisker (adjunction_triangle1 adj)).
  - exact (trans_prewhisker (adjunction_triangle2 adj)).
Defined.

(** We can compose adjunctions. Notice how the middle category must have equivalences. *)
Lemma adjunction_compose (A B C : Type)
  (F : A -> B) (G : B -> A) (F' : B -> C) (G' : C -> B)
  `{Is1Cat A, HasEquivs B, Is1Cat C}
  `{!Is0Functor F, !Is0Functor G, !Is0Functor F', !Is0Functor G'}
  : F ⊣ G -> F' ⊣ G' -> F' o F ⊣ G o G'.
Proof.
  intros adj1 adj2.
  snapply Build_Adjunction_natequiv_nat_right.
  { intros y.
    nrefine (natequiv_compose (natequiv_adjunction_l adj1 _) _).
    exact (natequiv_prewhisker (A:=A^op) (B:=B^op)
      (natequiv_adjunction_l adj2 y) F). }
  intros x.
  rapply is1natural_comp.
  + exact (is1natural_prewhisker G' (natequiv_adjunction_r adj1 x)).
  + napply is1natural_equiv_adjunction_r.
Defined.

(** Replace the left functor in an adjunction by a naturally equivalent one. *)
Lemma adjunction_natequiv_left {C D : Type} (F F' : C -> D) (G : D -> C)
  `{Is1Cat C, HasEquivs D, !HasMorExt D,
    !Is0Functor F, !Is0Functor F', !Is0Functor G} 
  : NatEquiv F F' -> F ⊣ G -> F' ⊣ G.
Proof.
  intros e adj.
  snapply Build_Adjunction_natequiv_nat_right.
  { intros y.
    refine (natequiv_compose (natequiv_adjunction_l adj _) _).
    exact (natequiv_postwhisker _ (natequiv_op e)). }
  intros x.
  rapply is1natural_comp.
Defined.

(** Replace the right functor in an adjunction by a naturally equivalent one. *)
Lemma adjunction_natequiv_right {C D : Type} (F : C -> D) (G G' : D -> C)
  `{HasEquivs C, Is1Cat D, !HasMorExt C,
    !Is0Functor F, !Is0Functor G, !Is0Functor G'} 
  : NatEquiv G G' -> F ⊣ G -> F ⊣ G'.
Proof.
  intros e adj.
  snapply Build_Adjunction_natequiv_nat_left.
  { intros x.
    refine (natequiv_compose _ (natequiv_adjunction_r adj _)).
    exact (natequiv_postwhisker _ e). }
  intros y.
  rapply is1natural_comp.
  2: exact _.
  rapply is1natural_yoneda.
Defined.

