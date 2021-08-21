Require Import Basics.
Require Import WildCat.Core.
Require Import WildCat.NatTrans.
Require Import WildCat.Equiv.
Require Import WildCat.Prod.
Require Import WildCat.Opposite.
Require Import WildCat.Yoneda.
Require Import WildCat.FunctorCat.
Require Import WildCat.Cat.
Require Import WildCat.Type.

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
  (** Naturality condition in both varibles seperately *)
  (** The left variable is a bit trickier to state since we have opposite categories involved. *)
  is1natural_equiv_adjunction_l (y : D)
    : Is1Natural (A := C^op) (yon y o F)
        (** We have to explicitly give a witness to the functoriality of [yon y o F]. *)
        (is0functor_F := is0functor_compose (A:=C^op) (B:=D^op) (C:=Type) F (yon y))
        (yon (G y)) (fun x => equiv_adjunction _ y) ;
  (** Naturality in the right variable *)
  is1natural_equiv_adjunction_r (x : C)
    : Is1Natural (opyon (F x)) (opyon x o G) (equiv_adjunction x) ; 
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
Global Existing Instances
  is1natural_equiv_adjunction_l
  is1natural_equiv_adjunction_r.

Notation "F ⊣ G" := (Adjunction F G).

(** ** Natural equivalences coming from adjunctions. *)

(** There are various bits of data we would like to extract from adjunctions. *)
Section AdjunctionData.
  Context {C D : Type} {F : C -> D} {G : D -> C}
    `{Is1Cat C, Is1Cat D, !HasMorExt C, !HasMorExt D,
      !Is0Functor F, !Is0Functor G}
    (adj : Adjunction F G).

  Definition natequiv_adjunction_l (y : D)
    : NatEquiv (A := C^op) (yon y o F)
        (** We have to explicitly give a witness to the functoriality of [yon y o F]. *)
        (is0functor_F := is0functor_compose (A:=C^op) (B:=D^op) (C:=Type) F (yon y))
        (yon (G y)).
  Proof.
    nrapply Build_NatEquiv.
    apply (is1natural_equiv_adjunction_l adj).
  Defined.

  Definition natequiv_adjunction_r (x : C)
    : NatEquiv (opyon (F x)) (opyon x o G).
  Proof.
    nrapply Build_NatEquiv.
    apply (is1natural_equiv_adjunction_r adj).
  Defined.

  (** TODO: *)
  (** We also have the natural equivalence in both arguments at the same time. *)

  (** The counit of an adjunction *)
  Definition adjunction_counit : NatTrans idmap (G o F).
  Proof.
    snrapply Build_NatTrans.
    { hnf. intros x.
      exact (equiv_adjunction adj x (F x) (Id _)). }
    hnf.
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
    snrapply Build_NatTrans.
    { hnf. intros y.
      exact ((equiv_adjunction adj (G y) y)^-1 (Id _)). }
    hnf.
    intros y y' f.
    apply GpdHom_path.
    refine (_^ @ _ @ _).
    1: exact (is1natural_natequiv _ _ (natequiv_inverse _ _
        (natequiv_adjunction_l _)) (G y') _ (fmap G f) _).
    2: exact (is1natural_natequiv _ _ (natequiv_inverse _ _
        (natequiv_adjunction_r _)) _ _ _ (Id _)).
    simpl.
    apply equiv_ap_inv'.
    apply path_hom.
    apply Square.vrefl.
  Defined.

  (** TODO: triangles *)
(*   Definition adjunction_ *)

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
      (is0functor_F := is0functor_compose (A:=C^op) (B:=D^op) (C:=Type) F (yon y))
      (yon (G y)) (fun x => e _ y))
  : Adjunction F G.
Proof.
  snrapply Build_Adjunction.
  1: exact (fun x => e x).
  1: exact is1nat_e.
  intros x; apply (is1natural_natequiv _ _ (e x)).
Defined.

(** A natural equivalence between functors [C^op -> Type] which is also natural in the left. *)
Definition Build_Adjunction_natequiv_nat_right
  {C D : Type} (F : C -> D) (G : D -> C)
  `{Is1Cat C, Is1Cat D, !Is0Functor F, !Is0Functor G} 
  (e : forall y, NatEquiv (A := C^op) (yon y o F) (yon (G y))
    (is0functor_F := is0functor_compose (A:=C^op) (B:=D^op) (C:=Type) F (yon y)))
  (is1nat_e : forall x, Is1Natural (opyon (F x)) (opyon x o G) (fun y => e y x))
  : Adjunction F G.
Proof.
  snrapply Build_Adjunction.
  1: exact (fun x y => e y x).
  1: intros y; apply (is1natural_natequiv _ _ (e y)).
  exact is1nat_e.
Defined.

Section BuildingAdjunctions.
  (** Our assumptions are no longer fully unbundled. We are using the Fun11 and Cat1 bundled versions of wild categories, since the number of typeclass instances we have is growing ever larger. This also helps coq infer which typeclass instances need to be used. *)
  (** It appears that translating between unit-counit and hom equivalence definitions of adjunction requires morphism extensionality. *)
  Context {C D : Cat1} (F : C $-> D) (G : D $-> C)
    `{!HasMorExt C, !HasMorExt D}.

  (** TODO: A natural equivalence between functors [C^op * D -> Type] *)

  (** From the data of an adjunction: unit, counit, left triangle, right triangle *)

  Section HomEquivFromUnitCounit.
    (** A unit-counit adjunction consists of the following data: *)
    Context
      (** A counit *)
      (ε : F $o G $-> Id _)
      (** A unit *)
      (η : Id _ $-> G $o F)
      (** Triangle identities *)
      (** Unfortunately, typeclasses whirls out of control if we don't hint at it the base type of [GpdHom], so we have to be explicit here. *)
      (t1 : GpdHom (A := Hom F F) (cat_comp (A:=Fun11 C D)
        (nattrans_prewhisker ε F : (F $o G $o F) $-> F)
        (nattrans_postwhisker F η : F $-> (F $o G $o F))) (Id F))
      (t2 : GpdHom (A := Hom G G) (cat_comp (A:=Fun11 D C)
        (nattrans_postwhisker G ε : (G $o F $o G) $-> G)
        (nattrans_prewhisker η G : G $-> (G $o F $o G))) (Id G))
      .
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
        (is0functor_F := is0functor_compose (A:=C^op) (B:=D^op) (C:=Type) F (yon y))
        (is0functor_G := is0functor_yon (G y))
        (fun x : C^op => γ x y).
    Proof.
      nrapply (is1natural_natequiv (yon y o F) (yon (G y)) (natequiv_inverse _ _
        (Build_NatEquiv (yon (G y)) (yon y o F) (fun x => (γ x y)^-1$) _))).
      nrapply is1natural_yoneda.
      nrapply is1functor_compose.
      1: nrapply is1functor_op; exact _.
      nrapply is1functor_opyon.
      nrapply hasmorext_op; exact _.
    Defined.

    (** And natural in the right. *)
    Lemma is1natural_γ_r x
      : Is1Natural (opyon (F x)) (fun x0 : D => opyon x (G x0)) (γ x).
    Proof.
      nrapply is1natural_opyoneda.
      exact _.
    Defined.

    (** Together this constructs an adjunction. *)
    Definition Build_Adjunction_unit_counit : Adjunction F G.
    Proof.
      snrapply Build_Adjunction.
      - exact γ.
      - apply is1natural_γ_l.
      - apply is1natural_γ_r.
    Defined.

  End HomEquivFromUnitCounit.

End BuildingAdjunctions.


(** * Properties of adjunctions *)

Lemma adjunction_postcomp `{Funext} (C D J : Type)
  `{Is1Cat C, HasEquivs D, Is01Cat J} (F : Fun11 C D) (G : Fun11 D C)
  `{!HasMorExt D}
  : F ⊣ G -> fun11_fun01_postcomp (A:=J) F ⊣ fun11_fun01_postcomp (A:=J) G.
Proof.
  intros adj. (* 
  srefine (Build_Adjunction_natequiv_nat_left
    (C:=Build_Cat1 _ _ _ _ _) (D:=Build_Cat1 _ _ _ _ _) _ _ _ _).
  { simpl.
    intros x. *)
(*     refine (natequiv_compose _ (natequiv_opyon_equiv _ _ _)). *)
    
Admitted.

(** We can compose adjunctions. Notice how the middle category must have equivalences. *)
Lemma adjunction_compose (A B C : Type)
  (F : A -> B) (G : B -> A) (F' : B -> C) (G' : C -> B)
  `{Is1Cat A, HasEquivs B, Is1Cat C}
  `{!Is0Functor F, !Is0Functor G, !Is0Functor F', !Is0Functor G'}
  : F ⊣ G -> F' ⊣ G' -> F' o F ⊣ G o G'.
Proof.
  intros adj1 adj2.
  snrapply Build_Adjunction_natequiv_nat_right.
  { intros y.
    nrefine (natequiv_compose (natequiv_adjunction_l adj1 _) _).
    exact (natequiv_prewhisker (A:=A^op) (B:=B^op)
      (natequiv_adjunction_l adj2 y) F). }
  intros x.
  rapply is1natural_comp.
  + rapply (is1natural_prewhisker G' (natequiv_adjunction_r adj1 x)).
  + rapply is1natural_equiv_adjunction_r.
Defined.
