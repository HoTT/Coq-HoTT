Require Import Basics EquivGpd Types.Prod.
Require Import WildCat.Core WildCat.ZeroGroupoid WildCat.Equiv WildCat.Yoneda WildCat.Universe WildCat.NatTrans WildCat.Opposite WildCat.Products.

(** * Categories with coproducts *)

Class BinaryCoproduct (A : Type) `{Is1Cat A} (x y : A) := Build_BinaryCoproduct' {
  prod_co_coprod :: BinaryProduct (x : A^op) y
}.

Arguments Build_BinaryCoproduct' {_ _ _ _ _ x y} _.
Arguments BinaryCoproduct {A _ _ _ _} x y.

Definition cat_coprod {A : Type}  `{Is1Cat  A} (x y : A) `{!BinaryCoproduct x y} : A
  := cat_prod (x : A^op) y.

Definition cat_inl {A : Type} `{Is1Cat A} {x y : A} `{!BinaryCoproduct x y} : x $-> cat_coprod x y.
Proof.
  change (cat_prod (x : A^op) y $-> x).
  exact cat_pr1.
Defined.

Definition cat_inr {A : Type} `{Is1Cat A} {x y : A} `{!BinaryCoproduct x y} : y $-> cat_coprod x y.
Proof.
  change (cat_prod (x : A^op) y $-> y).
  exact cat_pr2.
Defined.

Definition Build_BinaryCoproduct {A : Type} `{Is1Cat A} {x y : A}
  (cat_coprod : A) (cat_inl : x $-> cat_coprod) (cat_inr : y $-> cat_coprod)
  (cat_coprod_rec : forall z : A, (x $-> z) -> (y $-> z) -> cat_coprod $-> z)
  (cat_coprod_beta_inl : forall z (f : x $-> z) (g : y $-> z), cat_coprod_rec z f g $o cat_inl $== f)
  (cat_coprod_beta_inr : forall z (f : x $-> z) (g : y $-> z), cat_coprod_rec z f g $o cat_inr $== g)
  (cat_coprod_in_eta : forall z (f g : cat_coprod $-> z), f $o cat_inl $== g $o cat_inl -> f $o cat_inr $== g $o cat_inr -> f $== g)
  : BinaryCoproduct x y
  := Build_BinaryCoproduct'
    (Build_BinaryProduct
      (cat_coprod : A^op)
      cat_inl
      cat_inr
      cat_coprod_rec
      cat_coprod_beta_inl
      cat_coprod_beta_inr
      cat_coprod_in_eta).

Section Lemmata.

  Context {A : Type} {x y z : A} `{BinaryCoproduct _ x y}.

  Definition cat_equiv_cat_coprod_rec_inv
    : (opyon_0gpd (cat_coprod x y) z)
    $<~> prod_0gpd (opyon_0gpd x z) (opyon_0gpd y z)
    := @cat_equiv_cat_prod_corec_inv A^op x y z _ _ _ _ _.

  Definition cat_equiv_cat_coprod_rec
    : prod_0gpd (opyon_0gpd x z) (opyon_0gpd y z)
    $<~> (opyon_0gpd (cat_coprod x y) z)
    := @cat_equiv_cat_prod_corec A^op x y z _ _ _ _ _.

  Definition cat_coprod_rec (f : x $-> z) (g : y $-> z) : cat_coprod x y $-> z
    := @cat_prod_corec A^op x y z _ _ _ _ _ f g.
  
  Definition cat_coprod_beta_inl (f : x $-> z) (g : y $-> z)
    : cat_coprod_rec f g $o cat_inl $== f
    := @cat_prod_beta_pr1 A^op x y z _ _ _ _ _ f g.
  
  Definition cat_coprod_beta_inr (f : x $-> z) (g : y $-> z)
    : cat_coprod_rec f g $o cat_inr $== g
    := @cat_prod_beta_pr2 A^op x y z _ _ _ _ _ f g.
  
  Definition cat_coprod_eta (f : cat_coprod x y $-> z)
    : cat_coprod_rec (f $o cat_inl) (f $o cat_inr) $== f
    := @cat_prod_eta A^op x y z _ _ _ _ _ f.

  (* TODO: decompose and move *)
  Local Instance is0functor_coprod_0gpd_helper
    : Is0Functor (fun z : A => prod_0gpd (opyon_0gpd x z) (opyon_0gpd y z)).
  Proof.
    snrapply Build_Is0Functor.
    intros a b f.
    snrapply Build_Morphism_0Gpd.
    - intros [g g'].
      exact (f $o g, f $o g').
    - snrapply Build_Is0Functor.
      intros [g g'] [h h'] [p q].
      split.
      + exact (f $@L p).
      + exact (f $@L q).
  Defined.

  (* TODO: decompose and move *)
  Local Instance is1functor_coprod_0gpd_helper
    : Is1Functor (fun z : A => prod_0gpd (opyon_0gpd x z) (opyon_0gpd y z)).
  Proof.
    snrapply Build_Is1Functor.
    - intros a b f g p [r_fst r_snd].
      cbn; split.
      + refine (_ $@R _).
        apply p.
      + refine (_ $@R _).
        apply p.
    - intros a [r_fst r_snd].
      split; apply cat_idl.
    - intros a b c f g [r_fst r_snd].
      split; apply cat_assoc.
  Defined.

  Definition natequiv_cat_coprod_rec_inv
    : NatEquiv (opyon_0gpd (cat_coprod x y)) (fun z => prod_0gpd (opyon_0gpd x z) (opyon_0gpd y z))
    := @natequiv_cat_prod_corec_inv A^op x y _ _ _ _ _.

  Definition cat_coprod_rec_eta {f f' : x $-> z} {g g' : y $-> z}
    : f $== f' -> g $== g' -> cat_coprod_rec f g $== cat_coprod_rec f' g'
    := @cat_prod_corec_eta A^op x y z _ _ _ _ _ f f' g g'.
  
  Definition cat_coprod_in_eta {f f' : cat_coprod x y $-> z}
    : f $o cat_inl $== f' $o cat_inl -> f $o cat_inr $== f' $o cat_inr -> f $== f'
    := @cat_prod_pr_eta A^op x y z _ _ _ _ _ f f'.

End Lemmata.

(** *** Cateogires with binary coproducts *)

Class HasBinaryCoproducts (A : Type) `{Is1Cat A} := {
  binary_coproducts :: forall x y : A, BinaryCoproduct x y;
}.

(** *** Coproduct functor *)

(** TODO: The functoriality argument doesn't follow definitionally from the functoriality of [cat_prod], however after some modification it is close. We need to use appropriate lemmas for opposite functors. *) 
