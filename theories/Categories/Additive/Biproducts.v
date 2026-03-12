(** * Biproducts in categories with zero objects

    Objects that are simultaneously products and coproducts, fundamental
    to additive category theory.
*)

From HoTT Require Import Basics.Overture Basics.Tactics.
From HoTT.Categories Require Import Category.Core.
From HoTT.Categories.Additive Require Import ZeroObjects.

Local Notation fst_type := Basics.Overture.fst.
Local Notation snd_type := Basics.Overture.snd.

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
  beta_l : (outl B o inl B = 1)%morphism;
  beta_r : (outr B o inr B = 1)%morphism;
  
  (* Mixed terms are zero *)
  mixed_l : (outl B o inr B)%morphism = zero_morphism Y X;
  mixed_r : (outr B o inl B)%morphism = zero_morphism X Y
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
           ((h o inl B = f)%morphism * (h o inr B = g)%morphism)};
  
  (* Universal property as a product *)
  prod_universal : forall (W : object C) 
    (f : morphism C W X) (g : morphism C W Y),
    Contr {h : morphism C W B & 
           ((outl B o h = f)%morphism * (outr B o h = g)%morphism)}
}.

Arguments coprod_universal {C X Y B} u W f g : rename.
Arguments prod_universal {C X Y B} u W f g : rename.

(** ** Complete biproduct structure
    
    A biproduct is biproduct data together with the proof that it satisfies
    the biproduct axioms and universal property.
*)

Class Biproduct {C : PreCategory} `{Z : ZeroObject C} (X Y : object C) := {
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
  Context {C : PreCategory} `{Z : ZeroObject C} {X Y : object C}.
  Variable (B : Biproduct X Y).

  (** ** Uniqueness from universal property *)

  (** The coproduct universal morphism and its properties. *)
  Definition biproduct_coprod_universal (W : object C) 
    (f : morphism C X W) (g : morphism C Y W)
    : {h : morphism C B W & ((h o inl B = f)%morphism * (h o inr B = g)%morphism)}
    := @center _ (coprod_universal (biproduct_universal B) W f g).

  (** Extract the unique morphism from the coproduct universal property. *)
  Definition biproduct_coprod_mor (W : object C) 
    (f : morphism C X W) (g : morphism C Y W)
    : morphism C B W
    := (biproduct_coprod_universal W f g).1.

  Definition biproduct_coprod_beta_l (W : object C)
    (f : morphism C X W) (g : morphism C Y W)
    : (biproduct_coprod_mor W f g o inl B = f)%morphism
    := fst_type (biproduct_coprod_universal W f g).2.

  Definition biproduct_coprod_beta_r (W : object C)
    (f : morphism C X W) (g : morphism C Y W)
    : (biproduct_coprod_mor W f g o inr B = g)%morphism
    := snd_type (biproduct_coprod_universal W f g).2.

  Definition biproduct_coprod_unique (W : object C)
    (f : morphism C X W) (g : morphism C Y W)
    (h : morphism C B W)
    (Hl : (h o inl B = f)%morphism)
    (Hr : (h o inr B = g)%morphism)
    : h = biproduct_coprod_mor W f g
    := ap pr1 (contr (h; (Hl, Hr)))^.

  (** The product universal morphism and its properties. *)
  Definition biproduct_prod_universal (W : object C) 
    (f : morphism C W X) (g : morphism C W Y)
    : {h : morphism C W B & ((outl B o h = f)%morphism * (outr B o h = g)%morphism)}
    := @center _ (prod_universal (biproduct_universal B) W f g).

  (** Extract the unique morphism from the product universal property. *)
  Definition biproduct_prod_mor (W : object C) 
    (f : morphism C W X) (g : morphism C W Y)
    : morphism C W B
    := (biproduct_prod_universal W f g).1.

  Definition biproduct_prod_beta_l (W : object C)
    (f : morphism C W X) (g : morphism C W Y)
    : (outl B o biproduct_prod_mor W f g = f)%morphism
    := fst_type (biproduct_prod_universal W f g).2.

  Definition biproduct_prod_beta_r (W : object C)
    (f : morphism C W X) (g : morphism C W Y)
    : (outr B o biproduct_prod_mor W f g = g)%morphism
    := snd_type (biproduct_prod_universal W f g).2.
  
  Definition biproduct_prod_unique (W : object C)
    (f : morphism C W X) (g : morphism C W Y)
    (h : morphism C W B)
    (Hl : (outl B o h = f)%morphism)
    (Hr : (outr B o h = g)%morphism)
    : h = biproduct_prod_mor W f g
    := ap pr1 (contr (h; (Hl, Hr)))^.

  (** Product pairing with zero on right equals left injection composed. *)
  Lemma biproduct_prod_zero_r (W : object C) (h : morphism C W X)
    : biproduct_prod_mor W h (zero_morphism W Y)
      = (inl B o h)%morphism.
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

  (** Product pairing with zero on left equals right injection composed. *)
  Lemma biproduct_prod_zero_l (W : object C) (h : morphism C W Y)
    : biproduct_prod_mor W (zero_morphism W X) h
      = (inr B o h)%morphism.
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

  (** Product pairing is natural in the domain. *)
  Lemma biproduct_prod_comp (V W : object C)
    (f : morphism C W X) (g : morphism C W Y) (h : morphism C V W)
    : (biproduct_prod_mor W f g o h)%morphism
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

  (** Coproduct copairing is natural in the codomain. *)
  Lemma biproduct_coprod_comp (W V : object C)
    (f : morphism C X W) (g : morphism C Y W) (h : morphism C W V)
    : (h o biproduct_coprod_mor W f g)%morphism
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

(** * Self-biproduct operations *)

Section SelfBiproductOperations.
  Context {C : PreCategory} `{Z : ZeroObject C}.

  (** Pairing into a self-biproduct. *)
  Definition biproduct_sum_pair {X Y : object C}
    `{BYY : @Biproduct C Z Y Y}
    (f g : morphism C X Y)
    : morphism C X BYY
    := biproduct_prod_mor BYY X f g.

  (** A morphism induced on self-biproducts by maps on the two summands. *)
  Definition biproduct_sum_map {Y Y' : object C}
    `{BY : @Biproduct C Z Y Y} `{BY' : @Biproduct C Z Y' Y'}
    (a b : morphism C Y Y')
    : morphism C BY BY'
    := biproduct_prod_mor BY' BY (a o outl BY) (b o outr BY).

  (** The codiagonal of a self-biproduct. *)
  Definition biproduct_codiagonal (Y : object C)
    `{BYY : @Biproduct C Z Y Y}
    : morphism C BYY Y
    := biproduct_coprod_mor BYY Y 1%morphism 1%morphism.

  (** The left injection is pairing with zero on the right. *)
  Lemma biproduct_inl_sum_pair {Y : object C}
    `{BYY : @Biproduct C Z Y Y}
    : inl BYY = biproduct_sum_pair 1%morphism (zero_morphism Y Y).
  Proof.
    symmetry.
    unfold biproduct_sum_pair.
    rewrite biproduct_prod_zero_r.
    apply right_identity.
  Qed.

  (** The right injection is pairing with zero on the left. *)
  Lemma biproduct_inr_sum_pair {Y : object C}
    `{BYY : @Biproduct C Z Y Y}
    : inr BYY = biproduct_sum_pair (zero_morphism Y Y) 1%morphism.
  Proof.
    symmetry.
    unfold biproduct_sum_pair.
    rewrite biproduct_prod_zero_l.
    apply right_identity.
  Qed.

  (** The codiagonal is natural in the codomain. *)
  Lemma biproduct_codiagonal_natural {Y Y' : object C}
    `{BYY : @Biproduct C Z Y Y}
    (a : morphism C Y Y')
    : (a o biproduct_codiagonal Y)%morphism
      = biproduct_coprod_mor BYY Y' a a.
  Proof.
    unfold biproduct_codiagonal.
    rewrite biproduct_coprod_comp.
    repeat rewrite right_identity.
    reflexivity.
  Qed.

  (** Pairing is natural in the codomain. *)
  Lemma biproduct_sum_pair_natural {X Y Y' : object C}
    `{BYY : @Biproduct C Z Y Y} `{BYY' : @Biproduct C Z Y' Y'}
    (a : morphism C Y Y') (f g : morphism C X Y)
    : biproduct_sum_pair (a o f) (a o g)
      = (biproduct_sum_map a a o biproduct_sum_pair f g)%morphism.
  Proof.
    symmetry.
    unfold biproduct_sum_pair, biproduct_sum_map.
    rapply biproduct_prod_unique.
    - rewrite <- associativity.
      rewrite biproduct_prod_beta_l.
      rewrite associativity.
      rewrite biproduct_prod_beta_l.
      reflexivity.
    - rewrite <- associativity.
      rewrite biproduct_prod_beta_r.
      rewrite associativity.
      rewrite biproduct_prod_beta_r.
      reflexivity.
  Qed.

  (** A self-biproduct map sends the left injection to the left summand map. *)
  Lemma biproduct_sum_map_inl {Y Y' : object C}
    `{BYY : @Biproduct C Z Y Y} `{BYY' : @Biproduct C Z Y' Y'}
    (a b : morphism C Y Y')
    : (biproduct_sum_map a b o inl BYY)%morphism
      = (inl BYY' o a)%morphism.
  Proof.
    etransitivity (biproduct_sum_pair a (zero_morphism Y Y')).
    - rapply biproduct_prod_unique.
      + rewrite <- associativity.
        unfold biproduct_sum_map.
        rewrite biproduct_prod_beta_l.
        rewrite associativity.
        rewrite (beta_l (biproduct_is BYY)).
        apply right_identity.
      + rewrite <- associativity.
        unfold biproduct_sum_map.
        rewrite biproduct_prod_beta_r.
        rewrite associativity.
        rewrite (mixed_r (biproduct_is BYY)).
        apply zero_morphism_right.
    - unfold biproduct_sum_pair.
      apply biproduct_prod_zero_r.
  Qed.

  (** A self-biproduct map sends the right injection to the right summand map. *)
  Lemma biproduct_sum_map_inr {Y Y' : object C}
    `{BYY : @Biproduct C Z Y Y} `{BYY' : @Biproduct C Z Y' Y'}
    (a b : morphism C Y Y')
    : (biproduct_sum_map a b o inr BYY)%morphism
      = (inr BYY' o b)%morphism.
  Proof.
    etransitivity (biproduct_sum_pair (zero_morphism Y Y') b).
    - rapply biproduct_prod_unique.
      + rewrite <- associativity.
        unfold biproduct_sum_map.
        rewrite biproduct_prod_beta_l.
        rewrite associativity.
        rewrite (mixed_l (biproduct_is BYY)).
        apply zero_morphism_right.
      + rewrite <- associativity.
        unfold biproduct_sum_map.
        rewrite biproduct_prod_beta_r.
        rewrite associativity.
        rewrite (beta_r (biproduct_is BYY)).
        apply right_identity.
    - unfold biproduct_sum_pair.
      apply biproduct_prod_zero_l.
  Qed.

  (** The codiagonal of a self-biproduct map is the corresponding copairing. *)
  Lemma biproduct_codiagonal_factor_through_sum_map {Y Y' : object C}
    `{BYY : @Biproduct C Z Y Y} `{BYY' : @Biproduct C Z Y' Y'}
    (a b : morphism C Y Y')
    : (biproduct_codiagonal Y' o biproduct_sum_map a b)%morphism
      = biproduct_coprod_mor BYY Y' a b.
  Proof.
    rapply (biproduct_coprod_unique BYY Y' a b).
    - rewrite associativity.
      rewrite biproduct_sum_map_inl.
      rewrite <- associativity.
      rewrite biproduct_coprod_beta_l.
      apply left_identity.
    - rewrite associativity.
      rewrite biproduct_sum_map_inr.
      rewrite <- associativity.
      rewrite biproduct_coprod_beta_r.
      apply left_identity.
  Qed.

  (** ** Symmetry of self-biproducts *)

  (** The swap morphism exchanges the two summands of a self-biproduct. *)
  Definition biproduct_swap (Y : object C)
    `{BYY : @Biproduct C Z Y Y}
    : morphism C BYY BYY
    := biproduct_sum_pair (outr BYY) (outl BYY).

  (** Swapping components of a self-biproduct pairing. *)
  Lemma biproduct_prod_swap {X Y : object C}
    `{BYY : @Biproduct C Z Y Y}
    (f g : morphism C X Y)
    : biproduct_sum_pair g f
      = (biproduct_swap Y o biproduct_sum_pair f g)%morphism.
  Proof.
    symmetry.
    rapply biproduct_prod_unique.
    - rewrite <- associativity.
      unfold biproduct_swap, biproduct_sum_pair.
      rewrite biproduct_prod_beta_l.
      apply biproduct_prod_beta_r.
    - rewrite <- associativity.
      unfold biproduct_swap, biproduct_sum_pair.
      rewrite biproduct_prod_beta_r.
      apply biproduct_prod_beta_l.
  Qed.

  (** Swapping after the left injection gives the right injection. *)
  Lemma biproduct_swap_inl {Y : object C}
    `{BYY : @Biproduct C Z Y Y}
    : (biproduct_swap Y o inl BYY)%morphism = inr BYY.
  Proof.
    unfold biproduct_swap, biproduct_sum_pair.
    rewrite biproduct_prod_comp.
    rewrite (mixed_r (biproduct_is BYY)).
    rewrite (beta_l (biproduct_is BYY)).
    rewrite biproduct_prod_zero_l.
    rewrite right_identity.
    reflexivity.
  Qed.

  (** Swapping after the right injection gives the left injection. *)
  Lemma biproduct_swap_inr {Y : object C}
    `{BYY : @Biproduct C Z Y Y}
    : (biproduct_swap Y o inr BYY)%morphism = inl BYY.
  Proof.
    unfold biproduct_swap, biproduct_sum_pair.
    rewrite biproduct_prod_comp.
    rewrite (beta_r (biproduct_is BYY)).
    rewrite (mixed_l (biproduct_is BYY)).
    rewrite biproduct_prod_zero_r.
    rewrite right_identity.
    reflexivity.
  Qed.

  (** The codiagonal is invariant under swapping the two summands. *)
  Lemma biproduct_codiagonal_swap_invariant {Y : object C}
    `{BYY : @Biproduct C Z Y Y}
    : (biproduct_codiagonal Y o biproduct_swap Y)%morphism
      = biproduct_codiagonal Y.
  Proof.
    rapply (biproduct_coprod_unique BYY Y 1%morphism 1%morphism).
    - rewrite associativity.
      rewrite biproduct_swap_inl.
      apply biproduct_coprod_beta_r.
    - rewrite associativity.
      rewrite biproduct_swap_inr.
      apply biproduct_coprod_beta_l.
  Qed.

End SelfBiproductOperations.

(** * Export hints *)

Hint Resolve 
  biproduct_coprod_beta_l biproduct_coprod_beta_r
  biproduct_prod_beta_l biproduct_prod_beta_r
  : biproduct.

Hint Rewrite 
  @zero_morphism_left @zero_morphism_right
  : biproduct_simplify.
