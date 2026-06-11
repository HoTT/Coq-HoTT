(** * Biproducts in categories with zero objects

    Objects that are simultaneously products and coproducts, fundamental
    to additive category theory.
*)

From HoTT Require Import Basics.Overture Basics.Tactics.
From HoTT.Categories Require Import Category.Core.
From HoTT.Categories.Additive Require Import ZeroObjects.

Local Notation fst_type := Basics.Overture.fst.
Local Notation snd_type := Basics.Overture.snd.

Local Open Scope morphism_scope.

(** * Biproduct structures *)

(** ** Biproduct data

    The data of a biproduct consists of an object together with injection
    and projection morphisms.
*)

Record BiproductData {C : PreCategory} (X Y : object C) := {
  biproduct_obj : object C;

  (* Coproduct structure: injections *)
  inl : morphism C X biproduct_obj;
  inr : morphism C Y biproduct_obj;

  (* Product structure: projections *)
  outl : morphism C biproduct_obj X;
  outr : morphism C biproduct_obj Y
}.

Coercion biproduct_obj : BiproductData >-> object.

Arguments biproduct_obj {C X Y} b : rename.
Arguments inl {C X Y} b : rename.
Arguments inr {C X Y} b : rename.
Arguments outl {C X Y} b : rename.
Arguments outr {C X Y} b : rename.

(** ** Biproduct axioms

    The axioms that make biproduct data into an actual biproduct.
    These ensure the projection-injection pairs behave correctly.
*)

Record IsBiproduct {C : PreCategory} `{Z : ZeroObject C} {X Y : object C}
                   (B : BiproductData X Y) := {
  (* Projection-injection identities *)
  beta_l : outl B o inl B = 1;
  beta_r : outr B o inr B = 1;

  (* Mixed terms are zero *)
  mixed_l : outl B o inr B = zero_morphism Y X;
  mixed_r : outr B o inl B = zero_morphism X Y
}.

Arguments beta_l {C Z X Y B} i : rename.
Arguments beta_r {C Z X Y B} i : rename.
Arguments mixed_l {C Z X Y B} i : rename.
Arguments mixed_r {C Z X Y B} i : rename.

(** ** Universal property of biproducts

    The universal property states that morphisms into/out of the biproduct
    are uniquely determined by their components.
*)

Record HasBiproductUniversal {C : PreCategory} {X Y : object C}
  (B : BiproductData X Y) := {
  (* Universal property as a coproduct *)
  coprod_universal : forall (W : object C)
    (f : morphism C X W) (g : morphism C Y W),
    Contr {h : morphism C B W &
           ((h o inl B = f) * (h o inr B = g))};

  (* Universal property as a product *)
  prod_universal : forall (W : object C)
    (f : morphism C W X) (g : morphism C W Y),
    Contr {h : morphism C W B &
           ((outl B o h = f) * (outr B o h = g))}
}.

Arguments coprod_universal {C X Y B} u W f g : rename.
Arguments prod_universal {C X Y B} u W f g : rename.

(** ** Complete biproduct structure

    A biproduct is biproduct data together with the proof that it satisfies
    the biproduct axioms and universal property.  The zero object is an
    explicit argument so that instances can be written [Biproduct Z X Y].
*)

Class Biproduct {C : PreCategory} (Z : ZeroObject C) (X Y : object C) := {
  biproduct_data : BiproductData X Y;
  biproduct_is : IsBiproduct biproduct_data;
  biproduct_universal : HasBiproductUniversal biproduct_data
}.

Coercion biproduct_data : Biproduct >-> BiproductData.

Arguments biproduct_data {C Z X Y} b : rename.
Arguments biproduct_is {C Z X Y} b : rename.
Arguments biproduct_universal {C Z X Y} b : rename.

(** * Biproduct operations *)

Section BiproductOperations.
  Context {C : PreCategory} {Z : ZeroObject C} {X Y : object C}.
  Variable (B : Biproduct Z X Y).

  (** ** Uniqueness from universal property *)

  (** The coproduct universal morphism and its properties. *)
  Definition biproduct_coprod_universal (W : object C)
    (f : morphism C X W) (g : morphism C Y W)
    : {h : morphism C B W & ((h o inl B = f) * (h o inr B = g))}
    := @center _ (coprod_universal (biproduct_universal B) W f g).

  (** Extract the unique morphism from the coproduct universal property. *)
  Definition biproduct_coprod_mor (W : object C)
    (f : morphism C X W) (g : morphism C Y W)
    : morphism C B W
    := (biproduct_coprod_universal W f g).1.

  Definition biproduct_coprod_beta_l (W : object C)
    (f : morphism C X W) (g : morphism C Y W)
    : biproduct_coprod_mor W f g o inl B = f
    := fst_type (biproduct_coprod_universal W f g).2.

  Definition biproduct_coprod_beta_r (W : object C)
    (f : morphism C X W) (g : morphism C Y W)
    : biproduct_coprod_mor W f g o inr B = g
    := snd_type (biproduct_coprod_universal W f g).2.

  Definition biproduct_coprod_unique (W : object C)
    (f : morphism C X W) (g : morphism C Y W)
    (h : morphism C B W)
    (Hl : h o inl B = f)
    (Hr : h o inr B = g)
    : h = biproduct_coprod_mor W f g
    := ap pr1 (contr (h; (Hl, Hr)))^.

  (** The product universal morphism and its properties. *)
  Definition biproduct_prod_universal (W : object C)
    (f : morphism C W X) (g : morphism C W Y)
    : {h : morphism C W B & ((outl B o h = f) * (outr B o h = g))}
    := @center _ (prod_universal (biproduct_universal B) W f g).

  (** Extract the unique morphism from the product universal property. *)
  Definition biproduct_prod_mor (W : object C)
    (f : morphism C W X) (g : morphism C W Y)
    : morphism C W B
    := (biproduct_prod_universal W f g).1.

  Definition biproduct_prod_beta_l (W : object C)
    (f : morphism C W X) (g : morphism C W Y)
    : outl B o biproduct_prod_mor W f g = f
    := fst_type (biproduct_prod_universal W f g).2.

  Definition biproduct_prod_beta_r (W : object C)
    (f : morphism C W X) (g : morphism C W Y)
    : outr B o biproduct_prod_mor W f g = g
    := snd_type (biproduct_prod_universal W f g).2.

  Definition biproduct_prod_unique (W : object C)
    (f : morphism C W X) (g : morphism C W Y)
    (h : morphism C W B)
    (Hl : outl B o h = f)
    (Hr : outr B o h = g)
    : h = biproduct_prod_mor W f g
    := ap pr1 (contr (h; (Hl, Hr)))^.

  (** Pairing with zero on the right is the left injection composed. *)
  Lemma biproduct_prod_zero_r (W : object C) (h : morphism C W X)
    : biproduct_prod_mor W h (zero_morphism W Y)
      = inl B o h.
  Proof.
    symmetry.
    rapply biproduct_prod_unique.
    - rewrite <- associativity.
      rewrite (beta_l (biproduct_is B)).
      apply left_identity.
    - rewrite <- associativity.
      rewrite (mixed_r (biproduct_is B)).
      apply zero_morphism_left.
  Qed.

  (** Pairing with zero on the left is the right injection composed. *)
  Lemma biproduct_prod_zero_l (W : object C) (h : morphism C W Y)
    : biproduct_prod_mor W (zero_morphism W X) h
      = inr B o h.
  Proof.
    symmetry.
    rapply biproduct_prod_unique.
    - rewrite <- associativity.
      rewrite (mixed_l (biproduct_is B)).
      apply zero_morphism_left.
    - rewrite <- associativity.
      rewrite (beta_r (biproduct_is B)).
      apply left_identity.
  Qed.

  (** Pairing is natural in the domain. *)
  Lemma biproduct_prod_mor_nat (V W : object C)
    (f : morphism C W X) (g : morphism C W Y) (h : morphism C V W)
    : biproduct_prod_mor W f g o h
      = biproduct_prod_mor V (f o h) (g o h).
  Proof.
    rapply biproduct_prod_unique.
    - rewrite <- associativity.
      rewrite biproduct_prod_beta_l.
      reflexivity.
    - rewrite <- associativity.
      rewrite biproduct_prod_beta_r.
      reflexivity.
  Qed.

  (** Copairing is natural in the codomain. *)
  Lemma biproduct_coprod_mor_nat (W V : object C)
    (f : morphism C X W) (g : morphism C Y W) (h : morphism C W V)
    : h o biproduct_coprod_mor W f g
      = biproduct_coprod_mor V (h o f) (h o g).
  Proof.
    rapply biproduct_coprod_unique.
    - rewrite associativity.
      rewrite biproduct_coprod_beta_l.
      reflexivity.
    - rewrite associativity.
      rewrite biproduct_coprod_beta_r.
      reflexivity.
  Qed.

End BiproductOperations.

Arguments biproduct_prod_mor {C Z X Y} B {W} f g.

(** * Functoriality of biproducts *)

Section BiproductFunctoriality.
  Context {C : PreCategory} {Z : ZeroObject C} {X Y X' Y' : object C}
    {BXY : Biproduct Z X Y} {BX'Y' : Biproduct Z X' Y'}.

  (** The morphism between biproducts induced by morphisms of the summands. *)
  Definition biproduct_sum_map
    (a : morphism C X X') (b : morphism C Y Y')
    : morphism C BXY BX'Y'
    := biproduct_prod_mor BX'Y' (a o outl BXY) (b o outr BXY).

  (** The biproduct map composed with the left injection is the left
      summand map. *)
  Lemma biproduct_sum_map_inl
    (a : morphism C X X') (b : morphism C Y Y')
    : biproduct_sum_map a b o inl BXY
      = inl BX'Y' o a.
  Proof.
    rhs_V apply (biproduct_prod_zero_r BX'Y').
    rapply (biproduct_prod_unique BX'Y').
    - rewrite <- associativity.
      unfold biproduct_sum_map.
      rewrite (biproduct_prod_beta_l BX'Y').
      rewrite associativity.
      rewrite (beta_l (biproduct_is BXY)).
      apply right_identity.
    - rewrite <- associativity.
      unfold biproduct_sum_map.
      rewrite (biproduct_prod_beta_r BX'Y').
      rewrite associativity.
      rewrite (mixed_r (biproduct_is BXY)).
      apply zero_morphism_right.
  Qed.

  (** The biproduct map composed with the right injection is the right
      summand map. *)
  Lemma biproduct_sum_map_inr
    (a : morphism C X X') (b : morphism C Y Y')
    : biproduct_sum_map a b o inr BXY
      = inr BX'Y' o b.
  Proof.
    rhs_V apply (biproduct_prod_zero_l BX'Y').
    rapply (biproduct_prod_unique BX'Y').
    - rewrite <- associativity.
      unfold biproduct_sum_map.
      rewrite (biproduct_prod_beta_l BX'Y').
      rewrite associativity.
      rewrite (mixed_l (biproduct_is BXY)).
      apply zero_morphism_right.
    - rewrite <- associativity.
      unfold biproduct_sum_map.
      rewrite (biproduct_prod_beta_r BX'Y').
      rewrite associativity.
      rewrite (beta_r (biproduct_is BXY)).
      apply right_identity.
  Qed.

  (** Biproduct maps commute with pairing. *)
  Lemma biproduct_sum_map_prod {W : object C}
    (a : morphism C X X') (b : morphism C Y Y')
    (f : morphism C W X) (g : morphism C W Y)
    : biproduct_prod_mor BX'Y' (a o f) (b o g)
      = biproduct_sum_map a b o biproduct_prod_mor BXY f g.
  Proof.
    symmetry.
    rapply (biproduct_prod_unique BX'Y').
    - rewrite <- associativity.
      unfold biproduct_sum_map.
      rewrite (biproduct_prod_beta_l BX'Y').
      rewrite associativity.
      rewrite (biproduct_prod_beta_l BXY).
      reflexivity.
    - rewrite <- associativity.
      unfold biproduct_sum_map.
      rewrite (biproduct_prod_beta_r BX'Y').
      rewrite associativity.
      rewrite (biproduct_prod_beta_r BXY).
      reflexivity.
  Qed.

  (** Copairing is natural in the domain with respect to biproduct maps. *)
  Lemma biproduct_coprod_sum_map_nat {W : object C}
    (f : morphism C X' W) (g : morphism C Y' W)
    (a : morphism C X X') (b : morphism C Y Y')
    : biproduct_coprod_mor BX'Y' W f g o biproduct_sum_map a b
      = biproduct_coprod_mor BXY W (f o a) (g o b).
  Proof.
    rapply (biproduct_coprod_unique BXY).
    - rewrite associativity.
      rewrite biproduct_sum_map_inl.
      rewrite <- associativity.
      rewrite biproduct_coprod_beta_l.
      reflexivity.
    - rewrite associativity.
      rewrite biproduct_sum_map_inr.
      rewrite <- associativity.
      rewrite biproduct_coprod_beta_r.
      reflexivity.
  Qed.

End BiproductFunctoriality.

(** * Symmetry of biproducts *)

Section BiproductSymmetry.
  Context {C : PreCategory} {Z : ZeroObject C} {X Y : object C}
    {BXY : Biproduct Z X Y} {BYX : Biproduct Z Y X}.

  (** The swap morphism exchanges the two summands of a biproduct. *)
  Definition biproduct_swap
    : morphism C BXY BYX
    := biproduct_prod_mor BYX (outr BXY) (outl BXY).

  (** Swapping the components of a pairing. *)
  Lemma biproduct_prod_swap {W : object C}
    (f : morphism C W X) (g : morphism C W Y)
    : biproduct_prod_mor BYX g f
      = biproduct_swap o biproduct_prod_mor BXY f g.
  Proof.
    symmetry.
    rapply (biproduct_prod_unique BYX).
    - rewrite <- associativity.
      unfold biproduct_swap.
      rewrite (biproduct_prod_beta_l BYX).
      apply (biproduct_prod_beta_r BXY).
    - rewrite <- associativity.
      unfold biproduct_swap.
      rewrite (biproduct_prod_beta_r BYX).
      apply (biproduct_prod_beta_l BXY).
  Qed.

  (** Swapping after the left injection gives the right injection. *)
  Lemma biproduct_swap_inl
    : biproduct_swap o inl BXY = inr BYX.
  Proof.
    unfold biproduct_swap.
    rewrite (biproduct_prod_mor_nat BYX).
    rewrite (mixed_r (biproduct_is BXY)).
    rewrite (beta_l (biproduct_is BXY)).
    rewrite (biproduct_prod_zero_l BYX).
    apply right_identity.
  Qed.

  (** Swapping after the right injection gives the left injection. *)
  Lemma biproduct_swap_inr
    : biproduct_swap o inr BXY = inl BYX.
  Proof.
    unfold biproduct_swap.
    rewrite (biproduct_prod_mor_nat BYX).
    rewrite (beta_r (biproduct_is BXY)).
    rewrite (mixed_l (biproduct_is BXY)).
    rewrite (biproduct_prod_zero_r BYX).
    apply right_identity.
  Qed.

End BiproductSymmetry.

(** Swapping twice is the identity, so [BXY] and [BYX] are isomorphic:
    the biproduct is commutative. *)
Lemma biproduct_swap_swap {C : PreCategory} {Z : ZeroObject C}
  {X Y : object C} {BXY : Biproduct Z X Y} {BYX : Biproduct Z Y X}
  : biproduct_swap (BXY:=BYX) (BYX:=BXY) o biproduct_swap = 1.
Proof.
  transitivity (biproduct_prod_mor BXY (outl BXY) (outr BXY)).
  - rapply (biproduct_prod_unique BXY).
    + rewrite <- associativity.
      unfold biproduct_swap at 1.
      rewrite (biproduct_prod_beta_l BXY).
      apply (biproduct_prod_beta_r BYX).
    + rewrite <- associativity.
      unfold biproduct_swap at 1.
      rewrite (biproduct_prod_beta_r BXY).
      apply (biproduct_prod_beta_l BYX).
  - symmetry.
    rapply (biproduct_prod_unique BXY).
    + apply right_identity.
    + apply right_identity.
Qed.

(** * Self-biproducts *)

Section SelfBiproducts.
  Context {C : PreCategory} {Z : ZeroObject C}.

  (** The codiagonal of a self-biproduct. *)
  Definition biproduct_codiagonal (Y : object C)
    {BYY : Biproduct Z Y Y}
    : morphism C BYY Y
    := biproduct_coprod_mor BYY Y 1 1.

  (** The codiagonal is natural in the codomain. *)
  Lemma biproduct_codiagonal_nat {Y Y' : object C}
    {BYY : Biproduct Z Y Y}
    (a : morphism C Y Y')
    : a o biproduct_codiagonal Y
      = biproduct_coprod_mor BYY Y' a a.
  Proof.
    unfold biproduct_codiagonal.
    rewrite biproduct_coprod_mor_nat.
    repeat rewrite right_identity.
    reflexivity.
  Qed.

  (** The codiagonal of a biproduct map is the corresponding copairing. *)
  Lemma biproduct_codiagonal_factor_through_sum_map {Y Y' : object C}
    {BYY : Biproduct Z Y Y} {BYY' : Biproduct Z Y' Y'}
    (a b : morphism C Y Y')
    : biproduct_codiagonal Y' o biproduct_sum_map a b
      = biproduct_coprod_mor BYY Y' a b.
  Proof.
    unfold biproduct_codiagonal.
    rewrite biproduct_coprod_sum_map_nat.
    rewrite !left_identity.
    reflexivity.
  Qed.

  (** The codiagonal of a pairing with zero on the right recovers the
      left map. *)
  Lemma biproduct_codiagonal_prod_zero_r {X Y : object C}
    {BYY : Biproduct Z Y Y}
    (f : morphism C X Y)
    : biproduct_codiagonal Y
       o biproduct_prod_mor BYY f (zero_morphism X Y) = f.
  Proof.
    unfold biproduct_codiagonal.
    rewrite biproduct_prod_zero_r.
    rewrite <- associativity.
    rewrite biproduct_coprod_beta_l.
    apply left_identity.
  Qed.

  (** The codiagonal of a pairing with zero on the left recovers the
      right map. *)
  Lemma biproduct_codiagonal_prod_zero_l {X Y : object C}
    {BYY : Biproduct Z Y Y}
    (f : morphism C X Y)
    : biproduct_codiagonal Y
       o biproduct_prod_mor BYY (zero_morphism X Y) f = f.
  Proof.
    unfold biproduct_codiagonal.
    rewrite biproduct_prod_zero_l.
    rewrite <- associativity.
    rewrite biproduct_coprod_beta_r.
    apply left_identity.
  Qed.

  (** The codiagonal is invariant under swapping the two summands. *)
  Lemma biproduct_codiagonal_swap_invariant {Y : object C}
    {BYY : Biproduct Z Y Y}
    : biproduct_codiagonal Y o biproduct_swap
      = biproduct_codiagonal Y.
  Proof.
    rapply (biproduct_coprod_unique BYY Y 1 1).
    - rewrite associativity.
      rewrite biproduct_swap_inl.
      apply biproduct_coprod_beta_r.
    - rewrite associativity.
      rewrite biproduct_swap_inr.
      apply biproduct_coprod_beta_l.
  Qed.

End SelfBiproducts.

(** * Export hints *)

Hint Resolve
  biproduct_coprod_beta_l biproduct_coprod_beta_r
  biproduct_prod_beta_l biproduct_prod_beta_r
  : biproduct.

Hint Rewrite
  @zero_morphism_left @zero_morphism_right
  : biproduct_simplify.
