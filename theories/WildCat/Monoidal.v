Require Import Basics.Overture Basics.Tactics.
Require Import Types.Forall.
Require Import WildCat.Core WildCat.Bifunctor WildCat.Prod WildCat.Equiv WildCat.NatTrans.

(** * Monoidal 1-categories *)

(** ** Definition *)

(** A monoidal 1-category is a 1-category with equivalences and the following data: *)
Class IsMonoidal {A : Type} `{HasEquivs A} := {
  (** A bifunctor [cat_tensor] called the tensor product. *)
  cat_tensor : A -> A -> A;
  is0bifunctor_cat_tensor :: Is0Bifunctor cat_tensor;
  is1bifunctor_cat_tensor :: Is1Bifunctor cat_tensor;

  (** An object [cat_tensor_unit] called the tensor unit. *)
  cat_tensor_unit : A;
 
  (** An isomorphism [associator] witnessing associativity of [cat_tensor]. *)
  associator a b c : cat_tensor (cat_tensor a b) c $<~> cat_tensor a (cat_tensor b c);

  (** The [associator] is a natural isomorphism. Naturality is stated here in each variable separely. *)
  is1natural_associator_l {b c : A}
    :: Is1Natural
        (flip cat_tensor c o flip cat_tensor b)
        (flip cat_tensor (cat_tensor b c))
        (fun a => associator a b c);

  is1natural_associator_m {a c : A}
    :: Is1Natural
        (flip cat_tensor c o cat_tensor a)
        (cat_tensor a o flip cat_tensor c)
        (fun b => associator a b c);

  is1natural_associator_r {a b : A}
    :: Is1Natural
        (cat_tensor (cat_tensor a b))
        (cat_tensor a o cat_tensor b)
        (fun c => associator a b c);

  (** A natural isomorphism [left_unitor] witnessing the left unit law. *)
  left_unitor
    : NatEquiv (cat_tensor cat_tensor_unit) idmap;

  (** A natural isomorphism [right_unitor] witnessing the right unit law. *)
  right_unitor
    : NatEquiv (flip cat_tensor cat_tensor_unit) idmap;

  (** The triangle identity. *)
  triangle_identity a b
    : fmap (cat_tensor a) (left_unitor b) $o (associator a cat_tensor_unit b)
      $== fmap (flip cat_tensor b) (right_unitor a);
     
  (** The pentagon identity. *)
  pentagon_identity a b c d
    : associator a b (cat_tensor c d) $o associator (cat_tensor a b) c d
      $== fmap (cat_tensor a) (associator b c d) $o associator a (cat_tensor b c) d
        $o fmap (flip cat_tensor d) (associator a b c);
}.

Arguments IsMonoidal A {_ _ _ _ _}.
