Require Import Basics.Overture Basics.Tactics.
Require Import Types.Forall.
Require Import WildCat.Core WildCat.Bifunctor WildCat.Prod WildCat.Equiv WildCat.NatTrans.

(** * Monoidal 1-categories *)

(** ** Typeclasses for common diagrams *)

(** TODO: These should eventually be moved to a separate file in WildCat and used in other places. They can be thought of as a wildcat generalization of the classes in canonical_names.v *)

(** *** Associators *)

(** A natural equivalence witnessing the associativity of a bifunctor. *)
Class Associator {A : Type} `{HasEquivs A}
  (F : A -> A -> A) `{!Is0Bifunctor F, !Is1Bifunctor F} := {   
  (** An isomorphism [associator] witnessing associativity of [F]. *)
  associator a b c : F (F a b) c $<~> F a (F b c);
  
  (** The [associator] is a natural isomorphism. Naturality is stated here in each variable separely. *)
  is1natural_associator_l {b c : A}
    :: Is1Natural
        (flip F c o flip F b)
        (flip F (F b c))
        (fun a => associator a b c);

  is1natural_associator_m {a c : A}
    :: Is1Natural
        (flip F c o F a)
        (F a o flip F c)
        (fun b => associator a b c);

  is1natural_associator_r {a b : A}
    :: Is1Natural
        (F (F a b))
        (F a o F b)
        (fun c => associator a b c);
}.
Coercion associator : Associator >-> Funclass.
Arguments associator {A _ _ _ _ _ F _ _ _} a b c.

(** Alternatively, we can build an associator that is natural in an uncurried form. *)
Definition Build_Associator_uncurried {A : Type} `{HasEquivs A}
  (F : A -> A -> A) `{!Is0Bifunctor F, !Is1Bifunctor F}
  (associator'
    : NatEquiv
      (fun '(a, b, c) => F (F a b) c)
      (fun '(a, b, c) => F a (F b c)))
  : Associator F.
Proof.
  simpl in associator'.
  snrapply Build_Associator.
  - intros a b c.
    exact (associator' (a, b, c)).
  (** Using the curried naturality, we need only subsitute the identity for each pair of variables. However this requires rewriting some functor actions on the identity map which is what most of the work here accomplishes. *)
  - intros b c a a' f.
    pose proof (isnat associator'
      (a := (a, b, c)) (a' := (a', b, c)) (f, Id b, Id c)) as h.
    cbn in h; unfold uncurry, fmap11 in h; cbn in h; unfold fmap11 in h; cbn in h.
    refine ((_ $@L _^$) $@ h $@ _); clear h.
    + refine ((_ $@@ (fmap_id _ _)) $@ cat_idl _).
      exact (fmap2 _ (fmap_id _ _ $@R _  $@ cat_idl _)).
    + refine ((_ $@@ (fmap_id (F a' o F b) _)) $@ cat_idl _ $@R _).
      refine (_ $@R _ $@ cat_idl _).
      exact (fmap_id (F a' o flip F c) b).
  - intros a c b b' f.
    pose proof (isnat associator'
      (a := (a, b, c)) (a' := (a, b', c)) (Id a, f, Id c)) as h.
    cbn in h; unfold uncurry, fmap11 in h; cbn in h; unfold fmap11 in h; cbn in h.
    refine ((_ $@L _^$) $@ h $@ _); clear h.
    + refine ((_ $@@ fmap_id _ _) $@ cat_idl _).
      refine (fmap2 _ ((_ $@L fmap_id _ _) $@ cat_idr _)).
    + refine ((_ $@@ (fmap2 _ (fmap_id _ _) $@ fmap_id _ _)) $@ cat_idl _ $@R _).
      refine (_ $@L _ $@ cat_idr _).
      exact (fmap_id _ _).
  - intros a b c c' f.
    pose proof (isnat associator'
      (a := (a, b, c)) (a' := (a, b, c')) (Id a, Id b, f)) as h.
    cbn in h; unfold uncurry, fmap11 in h; cbn in h; unfold fmap11 in h; cbn in h.
    refine ((_ $@L _^$) $@ h $@ _); clear h.
    + refine ((_ $@L (_ $@ cat_idr _)) $@ cat_idr _).
      refine (fmap_comp _ _ _ $@ _).
      exact (fmap_id (flip F c o flip F b) a $@@ fmap_id (flip F c o F a) b).
    + exact (((_ $@L ((fmap_id (flip F (F b c)) _ $@@ fmap_id (F a o flip F c) _)
        $@ cat_idr _)) $@ cat_idr _) $@R _).
Defined.

(** *** Unitors *)

Class LeftUnitor {A : Type} `{HasEquivs A}
  (F : A -> A -> A) `{!Is0Bifunctor F, !Is1Bifunctor F} (unit : A)
  (** A natural isomorphism [left_unitor] witnessing the left unit law of [F]. *)
  := left_unitor : NatEquiv (F unit) idmap.
Coercion left_unitor : LeftUnitor >-> NatEquiv.
Arguments left_unitor {A _ _ _ _ _ F _ _ unit _}.

Class RightUnitor {A : Type} `{HasEquivs A}
  (F : A -> A -> A) `{!Is0Bifunctor F, !Is1Bifunctor F} (unit : A)
  (** A natural isomorphism [right_unitor] witnessing the right unit law of [F]. *)
  := right_unitor : NatEquiv (flip F unit) idmap.
Coercion right_unitor : RightUnitor >-> NatEquiv.
Arguments right_unitor {A _ _ _ _ _ F _ _ unit _}.

(** *** Triangle and Pentagon identities *)

Class TriangleIdentity {A : Type} `{HasEquivs A}
  (F : A -> A -> A) `{!Is0Bifunctor F, !Is1Bifunctor F, !Associator F}
  (unit : A) `{!LeftUnitor F unit, !RightUnitor F unit}
  (** The triangle identity for an associator and unitors. *)
  := triangle_identity a b
    : fmap01 F a (left_unitor b) $o (associator (F := F) a unit b)
    $== fmap10 F (right_unitor a) b.
Coercion triangle_identity : TriangleIdentity >-> Funclass.
Arguments triangle_identity {A _ _ _ _ _} F {_ _ _} unit {_}.

Class PentagonIdentity {A : Type} `{HasEquivs A}
  (F : A -> A -> A) `{!Is0Bifunctor F, !Is1Bifunctor F, !Associator F}
  (unit : A) `{!LeftUnitor F unit, !RightUnitor F unit}
  (** The pentagon identity for an associator and unitors. *)
  := pentagon_identity a b c d
    : associator a b (F c d) $o associator (F a b) c d
      $== fmap01 F a (associator b c d) $o associator a (F b c) d
        $o fmap10 F (associator a b c) d.
Coercion pentagon_identity : PentagonIdentity >-> Funclass.
Arguments pentagon_identity {A _ _ _ _ _} F {_ _ _} unit {_}.

(** ** Definition *)

(** A monoidal 1-category is a 1-category with equivalences and the following data: *)
Class IsMonoidal (A : Type) `{HasEquivs A} := {
  (** A bifunctor [cat_tensor] called the tensor product. *)
  cat_tensor : A -> A -> A;
  is0bifunctor_cat_tensor :: Is0Bifunctor cat_tensor;
  is1bifunctor_cat_tensor :: Is1Bifunctor cat_tensor;
  (** A natural isomorphism [associator] witnessing the associativity of the tensor product. *)
  cat_tensor_associator :: Associator cat_tensor;
  (** An object [cat_tensor_unit] called the tensor unit. *)
  cat_tensor_unit : A;
  (** A natural isomorphism [left_unitor] witnessing the left unit law. *)
  cat_tensor_left_unitor :: LeftUnitor cat_tensor cat_tensor_unit;
  (** A natural isomorphism [right_unitor] witnessing the right unit law. *)
  cat_tensor_right_unitor :: RightUnitor cat_tensor cat_tensor_unit;
  (** The triangle identity. *)
  cat_tensor_triangle_identity :: TriangleIdentity cat_tensor cat_tensor_unit;
  (** The pentagon identity. *)
  cat_tensor_pentagon_identity :: PentagonIdentity cat_tensor cat_tensor_unit;
}.
