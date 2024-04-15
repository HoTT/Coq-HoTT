Require Import Basics.Overture.
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
  associator a b c : F a (F b c) $<~> F (F a b) c;
  
  (** The [associator] is a natural isomorphism. *)
  is1natural_associator_uncurried
    :: Is1Natural
        (fun '(a, b, c) => F a (F b c))
        (fun '(a, b, c) => F (F a b) c)
        (fun '(a, b, c) => associator a b c);
}.
Coercion associator : Associator >-> Funclass.
Arguments associator {A _ _ _ _ _ F _ _ _} a b c.

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
    : fmap01 F a (left_unitor b)
    $== fmap10 F (right_unitor a) b $o (associator (F := F) a unit b).
Coercion triangle_identity : TriangleIdentity >-> Funclass.
Arguments triangle_identity {A _ _ _ _ _} F {_ _ _} unit {_}.

Class PentagonIdentity {A : Type} `{HasEquivs A}
  (F : A -> A -> A) `{!Is0Bifunctor F, !Is1Bifunctor F, !Associator F}
  (unit : A) `{!LeftUnitor F unit, !RightUnitor F unit}
  (** The pentagon identity for an associator and unitors. *)
  := pentagon_identity a b c d
    : associator (F a b) c d $o associator a b (F c d)
      $== fmap10 F (associator a b c) d $o associator a (F b c) d
        $o fmap01 F a (associator b c d).
Coercion pentagon_identity : PentagonIdentity >-> Funclass.
Arguments pentagon_identity {A _ _ _ _ _} F {_ _ _} unit {_}.

(** ** Definition *)

(** A monoidal 1-category is a 1-category with equivalences together with the following: *)
Class IsMonoidal (A : Type) `{HasEquivs A}
  (** It has a binary operation [cat_tensor] called the tensor product. *)
  (cat_tensor : A -> A -> A)
  (** It has a unit object [cat_tensor_unit] called the tensor unit. *)
  (cat_tensor_unit : A)
  (** These all satisfy the following properties: *)
  := {
  (** A [cat_tensor] is a 1-bifunctor. *)
  is0bifunctor_cat_tensor :: Is0Bifunctor cat_tensor;
  is1bifunctor_cat_tensor :: Is1Bifunctor cat_tensor;
  (** A natural isomorphism [associator] witnessing the associativity of the tensor product. *)
  cat_tensor_associator :: Associator cat_tensor;
  (** A natural isomorphism [left_unitor] witnessing the left unit law. *)
  cat_tensor_left_unitor :: LeftUnitor cat_tensor cat_tensor_unit;
  (** A natural isomorphism [right_unitor] witnessing the right unit law. *)
  cat_tensor_right_unitor :: RightUnitor cat_tensor cat_tensor_unit;
  (** The triangle identity. *)
  cat_tensor_triangle_identity :: TriangleIdentity cat_tensor cat_tensor_unit;
  (** The pentagon identity. *)
  cat_tensor_pentagon_identity :: PentagonIdentity cat_tensor cat_tensor_unit;
}.
