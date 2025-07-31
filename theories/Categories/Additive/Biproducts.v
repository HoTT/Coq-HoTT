(** * Biproducts in categories with zero objects

    Objects that are simultaneously products and coproducts, fundamental
    to additive category theory.
*)

From HoTT Require Import Basics Types.
From HoTT.Categories Require Import Category Functor.
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

End BiproductOperations.

(** * Export hints *)

Hint Resolve 
  biproduct_coprod_beta_l biproduct_coprod_beta_r
  biproduct_prod_beta_l biproduct_prod_beta_r
  : biproduct.

Hint Rewrite 
  @zero_morphism_left @zero_morphism_right
  : biproduct_simplify.
