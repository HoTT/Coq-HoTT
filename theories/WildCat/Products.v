Require Import Basics.Overture Basics.Equivalences Basics.Tactics.
Require Import Types.Bool Types.Prod.
Require Import WildCat.Core WildCat.Bifunctor WildCat.Equiv WildCat.EquivGpd
               WildCat.Forall WildCat.NatTrans WildCat.Opposite
               WildCat.Universe WildCat.Yoneda WildCat.Graph WildCat.ZeroGroupoid
               WildCat.Monoidal WildCat.MonoidalTwistConstruction
               WildCat.FunctorCat.

(** * Categories with products *)

(** ** Indexed products *)

(** For [A] a wild 1-category, [I] a type, and [x : I -> A] an [I]-indexed family of objects in [A], we study the categorical product of this family of objects. *)

(** When [x] is an [I]-indexed family of objects in [A] and [prod] is an object with an [I]-indexed family of projections, we get for each [z] an induced map from the 0-groupoid of morphisms [z $-> prod] to the product of the 0-groupoids [z $-> x i] over [i : I]. *)
Definition cat_prod_corec_inv {A : Type} `{Is1Cat A}
  {I : Type} (x : I -> A) (prod : A) (pr : forall i, prod $-> x i) (z : A)
  : yon_0gpd prod z $-> prod_0gpd I (fun i => yon_0gpd (x i) z).
Proof.
  snapply equiv_prod_0gpd_corec.
  intros i.
  exact (fmap (fun x => yon_0gpd x z) (pr i)).
Defined.

(** An object is a product of an [I]-indexed family of objects of a category if there is an [I]-indexed family of projections such that the induced map defined above is an equivalence. *)
Class IsProduct {A : Type} `{Is1Cat A} {I : Type} (x : I -> A) (cat_prod : A)
  := Build_IsProduct' {
  cat_pr : forall i : I, cat_prod $-> x i;
  cat_isequiv_cat_prod_corec_inv
    :: forall z : A, CatIsEquiv (cat_prod_corec_inv x cat_prod cat_pr z);
}.

Arguments cat_pr {A _ _ _ _ _ x cat_prod isprod} : rename.
Arguments cat_isequiv_cat_prod_corec_inv {A _ _ _ _ _} x cat_prod {isprod} : rename.
Arguments Build_IsProduct' {A _ _ _ _ _} x cat_prod.

(** A product is an object together with the data that it is a product. *)
Class Product {A : Type} `{Is1Cat A} {I : Type} (x : I -> A) := Build_Product' {
  cat_prod : A;
  cat_isprod :: IsProduct x cat_prod;
}.

Arguments Build_Product' {A _ _ _ _ _} x cat_prod cat_isprod.
Arguments cat_prod {A _ _ _ _ _} x {product} : rename.
Arguments cat_isprod {A _ _ _ _ _} x {product} : rename.

Section ProductConstructors.

  Context {A : Type} `{Is1Cat A} {I : Type} (x : I -> A)
    (cat_prod : A) (cat_pr : forall i : I, cat_prod $-> x i)
    (cat_prod_corec : forall z : A,
      (forall i : I, z $-> x i) -> (z $-> cat_prod))
    (cat_prod_beta_pr : forall (z : A) (f : forall i, z $-> x i) (i : I),
      cat_pr i $o cat_prod_corec z f $== f i)
    (cat_prod_eta_pr : forall (z : A) (f g : z $-> cat_prod),
      (forall i : I, cat_pr i $o f $== cat_pr i $o g) -> f $== g).

  (** A convenience wrapper for building [IsProduct]. *)
  Definition Build_IsProduct : IsProduct x cat_prod.
  Proof.
    snapply (Build_IsProduct' x cat_prod cat_pr).
    intros z.
    napply isequiv_0gpd_issurjinj.
    napply Build_IsSurjInj.
    - intros f.
      exists (cat_prod_corec z f).
      intros i.
      napply cat_prod_beta_pr.
    - intros f g p.
      by napply cat_prod_eta_pr.
  Defined.

  (** A convenience wrapper for building products. *)
  Definition Build_Product : Product x
    := Build_Product' x cat_prod Build_IsProduct.

End ProductConstructors.

Section Lemmata.

  Context {A : Type} `{Is1Cat A} {I : Type} {x : I -> A}
    (cat_prod : A) {cat_isprod : IsProduct x cat_prod}.

  Definition cate_cat_prod_corec_inv {z : A}
    : (yon_0gpd cat_prod z) $<~> prod_0gpd I (fun i => yon_0gpd (x i) z)
    := Build_CatEquiv (cat_prod_corec_inv x cat_prod cat_pr z).

  Definition cate_cat_prod_corec {z : A}
    : prod_0gpd I (fun i => yon_0gpd (x i) z) $<~> (yon_0gpd cat_prod z)
    := cate_cat_prod_corec_inv^-1$.

  Definition cat_prod_corec {z : A}
    : (forall i, z $-> x i) -> (z $-> cat_prod)
    := cate_fun cate_cat_prod_corec.

  (** Applying the [i]th projection after a tuple of maps gives the [ith] map. *)
  Definition cat_prod_beta {z : A} (f : forall i, z $-> x i)
    : forall i, cat_pr i $o cat_prod_corec f $== f i
    := cate_isretr cate_cat_prod_corec_inv f.

  (** The pairing map is the unique map that makes the following diagram commute. *)
  Definition cat_prod_eta {z : A} (f : z $-> cat_prod)
    : cat_prod_corec (fun i => cat_pr i $o f) $== f
    := cate_issect cate_cat_prod_corec_inv f.

  Local Instance is0functor_prod_0gpd_helper
    : Is0Functor (fun z : A^op => prod_0gpd I (fun i => yon_0gpd (x i) z)).
  Proof.
    snapply Build_Is0Functor.
    intros a b f.
    snapply Build_Fun01'.
    - intros g i.
      exact (f $o g i).
    - intros g h p i.
      exact (f $@L p i).
  Defined.

  Local Instance is1functor_prod_0gpd_helper
    : Is1Functor (fun z : A^op => prod_0gpd I (fun i => yon_0gpd (x i) z)).
  Proof.
    snapply Build_Is1Functor.
    - intros a b f g p r i.
      refine (_ $@L _).
      exact p.
    - intros a r i.
      napply cat_idl; exact _.
    - intros a b c f g r i.
      napply cat_assoc; exact _.
  Defined.

  Definition natequiv_cat_prod_corec_inv
    : NatEquiv (yon_0gpd cat_prod)
      (fun z : A^op => prod_0gpd I (fun i => yon_0gpd (x i) z)).
  Proof.
    snapply Build_NatEquiv.
    1: intro; exact cate_cat_prod_corec_inv.
    exact (is1natural_yoneda_0gpd cat_prod
      (fun z => prod_0gpd I (fun i => yon_0gpd (x i) z))
      cat_pr).
  Defined.

  Lemma cat_prod_corec_eta {z : A} {f f' : forall i, z $-> x i}
    : (forall i, f i $== f' i) -> cat_prod_corec f $== cat_prod_corec f'.
  Proof.
    intros p.
    unfold cat_prod_corec.
    napply (moveL_equiv_V_0gpd cate_cat_prod_corec_inv).
    nrefine (cate_isretr cate_cat_prod_corec_inv _ $@ _).
    exact p.
  Defined.

  Lemma cat_prod_pr_eta {z : A} {f f' : z $-> cat_prod}
    : (forall i, cat_pr i $o f $== cat_pr i $o f') -> f $== f'.
  Proof.
    intros p.
    refine ((cat_prod_eta _)^$ $@ _ $@ cat_prod_eta _).
    by napply cat_prod_corec_eta.
  Defined.

End Lemmata.

Section InducedFromEquiv.

  Context {A : Type} `{he : HasEquivs A} {I : Type} {x : I -> A}
  (cat_prod : A) `{!IsProduct x cat_prod}
  (y : A) (f : y $<~> cat_prod).

  (** A categorical equivalence into a product induces a product structure on the domain. *)
  Local Instance cat_prod_equiv_prod : IsProduct x y.
  Proof.
    snapply Build_IsProduct.
    - intro i.
      exact (cat_pr i $o f).
    - intros z D.
      exact (f^-1$ $o cat_prod_corec _ D).
    - intros z D i; cbn beta.
      refine (_ $@ cat_prod_beta _ _ _).
      refine (cat_assoc _ _ _ $@ _).
      apply cat_postwhisker.
      apply compose_h_Vh.
    - cbn beta; intros z g g' e.
      napply (cate_monic_equiv f).
      napply cat_prod_pr_eta.
      intro i.
      refine (cat_assoc_opp _ _ _ $@ _).
      refine (_ $@ cat_assoc _ _ _).
      exact (e i).
  Defined.

  (** The induced projection is given by the equivalence. *)
  Definition cat_pr_comp (i : I)
    : cat_pr i $== cat_pr i $o f
    := Id _.

  (** The induced corecursion is given by the equivalence. *)
  Definition cat_prod_corec_comp {z : A} (D : forall i, z $-> x i)
    : f $o cat_prod_corec (cat_isprod:=cat_prod_equiv_prod) y D $== cat_prod_corec _ D
    := compose_h_Vh _ _.

End InducedFromEquiv.

(** *** Diagonal map into the product of a constant family *)

Definition cat_prod_diag {A : Type} {I : Type} (x : A) (cat_prod : A)
  `{IsProduct _ I (fun _ => x) cat_prod}
  : x $-> cat_prod
  := cat_prod_corec cat_prod (fun _ => Id x).

(** *** Uniqueness of products *)

Definition cate_cat_prod {A : Type} `{HasEquivs A} {I J : Type} (ie : I <~> J)
  (x : I -> A) (prod_x : A) `{!IsProduct x prod_x}
  (y : J -> A) (prod_y : A) `{!IsProduct y prod_y}
  (e : forall i : I, x i $<~> y (ie i))
  : prod_x $<~> prod_y.
Proof.
  napply yon_equiv_0gpd.
  refine (natequiv_compose _ (natequiv_cat_prod_corec_inv _)).
  refine (natequiv_compose
            (natequiv_inverse (natequiv_cat_prod_corec_inv _)) _).
  snapply Build_NatEquiv.
  - intros z.
    napply (cate_prod_0gpd ie).
    intros i.
    exact (natequiv_yon_equiv_0gpd (e i) _).
  - snapply Build_Is1Natural.
    intros a b f g j.
    cbn.
    destruct (eisretr ie j).
    exact (cat_assoc_opp _ _ _).
Defined.

(** [I]-indexed products are unique. *)
Definition cat_prod_unique {A : Type} `{HasEquivs A} {I : Type}
  (x : I -> A) (prod_x : A) `{!IsProduct x prod_x}
  (y : I -> A) (prod_y : A) `{!IsProduct y prod_y}
  (e : forall i : I, x i $<~> y i)
  : prod_x $<~> prod_y
  := cate_cat_prod 1 x _ y _ e.

(** *** Existence of products *)

Class HasProducts (A : Type) `{Is1Cat A} (I : Type)
  := has_products :: forall x : I -> A, Product x.

Arguments has_products {A _ _ _ _ I hasproducts} x : rename.

Class HasAllProducts (A : Type) `{Is1Cat A}
  := has_all_products :: forall I : Type, HasProducts A I.

(** *** Product functor *)

Instance is0functor_cat_prod (A : Type) (I : Type) `{HasProducts A I}
  : Is0Functor (fun x : I -> A => cat_prod x).
Proof.
  napply Build_Is0Functor.
  intros x y f.
  exact (cat_prod_corec _ (fun i => f i $o cat_pr i)).
Defined.

Instance is1functor_cat_prod (A : Type) (I : Type) `{HasProducts A I}
  : Is1Functor (fun x : I -> A => cat_prod x).
Proof.
  napply Build_Is1Functor.
  - intros x y f g p.
    exact (cat_prod_corec_eta _ (fun i => p i $@R cat_pr i)).
  - intros x.
    nrefine (_ $@ (cat_prod_eta _ (Id _))).
    exact (cat_prod_corec_eta _ (fun i => cat_idl _ $@ (cat_idr _)^$)).
  - intros x y z f g.
    napply cat_prod_pr_eta.
    intros i.
    nrefine (cat_prod_beta _ _ _ $@ _).
    nrefine (_ $@ cat_assoc _ _ _).
    symmetry.
    nrefine (cat_prod_beta _ _ _ $@R _ $@ _).
    nrefine (cat_assoc _ _ _ $@ _).
    nrefine (_ $@L cat_prod_beta _ _ _ $@ _).
    napply cat_assoc_opp.
Defined.

(** *** An empty product is terminal *)

Definition isterminal_prod_empty {A : Type} {x : Empty -> A} {prod_empty : A}
  `{isprod : IsProduct _ Empty x prod_empty}
  : IsTerminal prod_empty.
Proof.
  intros a.
  srefine (cat_prod_corec _ _; fun f => cat_prod_pr_eta _ _); intros [].
Defined.

(** ** Binary products *)

Class IsBinaryProduct {A : Type} `{Is1Cat A} (x y : A) (cat_binprod : A)
  := is_binary_product :: IsProduct (Bool_rec _ x y) (cat_binprod).

Class BinaryProduct {A : Type} `{Is1Cat A} (x y : A)
  := binary_product :: Product (Bool_rec _ x y).

Instance isbinaryproduct_binaryproduct {A : Type} `{Is1Cat A}
  (x y : A) `{!BinaryProduct x y}
  : IsBinaryProduct x y (cat_prod _)
  := cat_isprod _.

(** A category with binary products is a category with a binary product for each pair of objects. *)
Class HasBinaryProducts (A : Type) `{Is1Cat A}
  := has_binary_products :: forall x y : A, BinaryProduct x y.

Instance hasbinaryproducts_hasproductsbool {A : Type} `{HasProducts A Bool}
  : HasBinaryProducts A
  := fun x y => has_products (Bool_rec _ x y).

Section BinaryProducts.

  Context {A : Type} `{Is1Cat A} {x y : A}
    (cat_binprod : A) {isbinprod : IsBinaryProduct x y cat_binprod}.

  Definition cat_pr1 : cat_binprod $-> x := cat_pr (x:=Bool_rec _ x y) true.

  Definition cat_pr2 : cat_binprod $-> y := cat_pr (x:=Bool_rec _ x y) false.

  Definition cat_binprod_corec {z : A} (f : z $-> x) (g : z $-> y)
    : z $-> cat_binprod.
  Proof.
    apply (cat_prod_corec _).
    intros [|].
    - exact f.
    - exact g.
  Defined.

  Definition cat_binprod_beta_pr1 {z : A} (f : z $-> x) (g : z $-> y)
    : cat_pr1 $o cat_binprod_corec f g $== f
    := cat_prod_beta _ _ true.

  Definition cat_binprod_beta_pr2 {z : A} (f : z $-> x) (g : z $-> y)
    : cat_pr2 $o cat_binprod_corec f g $== g
    := cat_prod_beta _ _ false.

  Definition cat_binprod_eta {z : A} (f : z $-> cat_binprod)
    : cat_binprod_corec (cat_pr1 $o f) (cat_pr2 $o f) $== f.
  Proof.
    unfold cat_binprod_corec.
    rapply cat_prod_pr_eta.
    intros [|].
    - exact (cat_binprod_beta_pr1 _ _).
    - exact (cat_binprod_beta_pr2 _ _).
  Defined.

  Definition cat_binprod_eta_pr {z : A} (f g : z $-> cat_binprod)
    : cat_pr1 $o f $== cat_pr1 $o g -> cat_pr2 $o f $== cat_pr2 $o g -> f $== g.
  Proof.
    intros p q.
    rapply cat_prod_pr_eta.
    intros [|].
    - exact p.
    - exact q.
  Defined.

  Definition cat_binprod_corec_eta {z : A} (f f' : z $-> x) (g g' : z $-> y)
    : f $== f' -> g $== g' -> cat_binprod_corec f g $== cat_binprod_corec f' g'.
  Proof.
    intros p q.
    rapply cat_prod_corec_eta.
    intros [|].
    - exact p.
    - exact q.
  Defined.

End BinaryProducts.

Section BinaryProductConstructors.

  Context {A : Type} `{Is1Cat A} {x y : A}
    (cat_binprod : A) (cat_pr1 : cat_binprod $-> x) (cat_pr2 : cat_binprod $-> y)
    (cat_binprod_corec : forall z : A, z $-> x -> z $-> y -> z $-> cat_binprod)
    (cat_binprod_beta_pr1 : forall (z : A) (f : z $-> x) (g : z $-> y),
      cat_pr1 $o cat_binprod_corec z f g $== f)
    (cat_binprod_beta_pr2 : forall (z : A) (f : z $-> x) (g : z $-> y),
      cat_pr2 $o cat_binprod_corec z f g $== g)
    (cat_binprod_eta_pr : forall (z : A) (f g : z $-> cat_binprod),
      cat_pr1 $o f $== cat_pr1 $o g -> cat_pr2 $o f $== cat_pr2 $o g -> f $== g).

  (** A convenience wrapper for building [IsBinaryProduct]. *)
  Definition Build_IsBinaryProduct : IsBinaryProduct x y cat_binprod.
  Proof.
    snapply (Build_IsProduct _ cat_binprod).
    - intros [|].
      + exact cat_pr1.
      + exact cat_pr2.
    - intros z f.
      napply cat_binprod_corec.
      + exact (f true).
      + exact (f false).
    - intros z f [|].
      + napply cat_binprod_beta_pr1.
      + napply cat_binprod_beta_pr2.
    - intros z f g p.
      napply cat_binprod_eta_pr.
      + exact (p true).
      + exact (p false).
  Defined.

  (** A convenience wrapper for building binary products. *)
  Definition Build_BinaryProduct : BinaryProduct x y
    := Build_Product' _ cat_binprod Build_IsBinaryProduct.

End BinaryProductConstructors.

Definition cat_binprod {A: Type} `{HasBinaryProducts A} (x y : A) : A
  := cat_prod (Bool_rec _ x y).

Definition cat_binprod_eta_pr_x_xx {A : Type} `{HasBinaryProducts A}
  {w x y z : A} (f g : w $-> cat_binprod x (cat_binprod y z))
  : cat_pr1 _ $o f $== cat_pr1 _ $o g
  -> cat_pr1 _ $o cat_pr2 _ $o f $== cat_pr1 _ $o cat_pr2 _ $o g
  -> cat_pr2 _ $o cat_pr2 _ $o f $== cat_pr2 _ $o cat_pr2 _ $o g
  -> f $== g.
Proof.
  intros p q r.
  napply cat_binprod_eta_pr.
  - exact p.
  - napply cat_binprod_eta_pr.
    + exact (cat_assoc_opp _ _ _ $@ q $@ cat_assoc _ _ _).
    + exact (cat_assoc_opp _ _ _ $@ r $@ cat_assoc _ _ _).
Defined.

Definition cat_binprod_eta_pr_xx_x {A : Type} `{HasBinaryProducts A} {w x y z : A}
  (f g : w $-> cat_binprod (cat_binprod x y) z)
  : cat_pr1 _ $o cat_pr1 _ $o f $== cat_pr1 _ $o cat_pr1 _ $o g
  -> cat_pr2 _ $o cat_pr1 _ $o f $== cat_pr2 _ $o cat_pr1 _ $o g
  -> cat_pr2 _ $o f $== cat_pr2 _ $o g
  -> f $== g.
Proof.
  intros p q r.
  napply cat_binprod_eta_pr.
  2: exact r.
  napply cat_binprod_eta_pr.
  1,2: refine (cat_assoc_opp _ _ _ $@ _ $@ cat_assoc _ _ _).
  - exact p.
  - exact q.
Defined.

Definition cat_binprod_eta_pr_x_xx_id {A : Type} `{HasBinaryProducts A} {x y z : A}
  (f : cat_binprod x (cat_binprod y z) $-> cat_binprod x (cat_binprod y z))
  : cat_pr1 _ $o f $== cat_pr1 _
  -> cat_pr1 _ $o cat_pr2 _ $o f $== cat_pr1 _ $o cat_pr2 _
  -> cat_pr2 _ $o cat_pr2 _ $o f $== cat_pr2 _ $o cat_pr2 _
  -> f $== Id _.
Proof.
  intros p q r.
  napply cat_binprod_eta_pr_x_xx.
  - exact (p $@ (cat_idr _)^$).
  - exact (q $@ (cat_idr _)^$).
  - exact (r $@ (cat_idr _)^$).
Defined.

(** From binary products, all [Bool]-shaped products can be constructed. This should not be an instance to avoid a cycle with [hasbinaryproducts_hasproductsbool]. *)
Definition hasproductsbool_hasbinaryproducts {A : Type} `{hbp : HasBinaryProducts A}
  : HasProducts A Bool.
Proof.
  intros x.
  snapply Build_Product.
  - exact (cat_binprod (x true) (x false)).
  - intros [|].
    + exact (cat_pr1 _).
    + exact (cat_pr2 _).
  - intros z f.
    exact (cat_binprod_corec _ (f true) (f false)).
  - intros z f [|].
    + exact (cat_binprod_beta_pr1 _ (f true) (f false)).
    + exact (cat_binprod_beta_pr2 _ (f true) (f false)).
  - intros z f g p.
    napply cat_binprod_eta_pr.
    + exact (p true).
    + exact (p false).
Defined.

(** *** Operations on indexed products *)

(** We can take the disjoint union of the index set of an indexed product if we have all binary products. *)

Definition cat_product_index_sum {A : Type} `{HasBinaryProducts A} {I J : Type}
  (x : I -> A) (prod_x : A) `{!IsProduct x prod_x}
  (y : J -> A) (prod_y : A) `{!IsProduct y prod_y}
  : Product (I:=I + J) (sum_ind _ x y).
Proof.
  srapply Build_Product.
  - exact (cat_binprod prod_x prod_y).
  - intros [i | j].
    + exact (cat_pr i $o cat_pr1 _).
    + exact (cat_pr j $o cat_pr2 _).
  - intros z f.
    rapply cat_binprod_corec.
    + rapply cat_prod_corec.
      exact (f o inl).
    + rapply cat_prod_corec.
      exact (f o inr).
  - intros z f [i | j].
    + nrefine (cat_assoc _ _ _ $@ _).
      nrefine ((_ $@L cat_binprod_beta_pr1 _ _ _) $@ _).
      tapply (cat_prod_beta prod_x).
    + nrefine (cat_assoc _ _ _ $@ _).
      nrefine ((_ $@L cat_binprod_beta_pr2 _ _ _) $@ _).
      tapply (cat_prod_beta prod_y).
  - intros z f g r.
    rapply cat_binprod_eta_pr.
    + rapply cat_prod_pr_eta.
      intros i.
      exact ((cat_assoc _ _ _)^$ $@ r (inl i) $@ cat_assoc _ _ _).
    + rapply cat_prod_pr_eta.
      intros j.
      exact ((cat_assoc _ _ _)^$ $@ r (inr j) $@ cat_assoc _ _ _).
Defined.

(** *** Binary product functor *)

(** We prove bifunctoriality of [cat_binprod : A -> A -> A] by factoring it as [cat_prod Bool o Bool_rec A]. First, we prove that [Bool_rec A : A -> A -> (Bool -> A)] is a bifunctor. *)
Local Instance is0bifunctor_boolrec {A : Type} `{Is1Cat A}
  : Is0Bifunctor (Bool_rec A).
Proof.
  snapply Build_Is0Bifunctor'.
  1,2: exact _.
  snapply Build_Is0Functor.
  intros [a b] [a' b'] [f g] [ | ].
  - exact f.
  - exact g.
Defined.

Local Instance is1bifunctor_boolrec {A : Type} `{Is1Cat A}
  : Is1Bifunctor (Bool_rec A).
Proof.
  snapply Build_Is1Bifunctor'.
  snapply Build_Is1Functor.
  - intros [a b] [a' b'] [f g] [f' g'] [p q] [ | ].
    + exact p.
    + exact q.
  - intros [a b] [ | ]; reflexivity.
  - intros [a b] [a' b'] [a'' b''] [f f'] [g g'] [ | ]; reflexivity.
Defined.

(** As a special case of the product functor, restriction along [Bool_rec A] yields bifunctoriality of [cat_binprod]. *)
Instance is0bifunctor_cat_binprod {A : Type} `{hbp : HasBinaryProducts A}
  : Is0Bifunctor cat_binprod.
Proof.
  pose (p:=has_products (hasproducts:=hasproductsbool_hasbinaryproducts)).
  exact (is0bifunctor_postcompose
          (Bool_rec A) (fun x => cat_prod x (product:=p x))).
Defined.

Instance is1bifunctor_cat_binprod {A : Type} `{hbp : HasBinaryProducts A}
  : Is1Bifunctor cat_binprod.
Proof.
  pose (p:=has_products (hasproducts:=hasproductsbool_hasbinaryproducts)).
  exact (is1bifunctor_postcompose
          (Bool_rec A) (fun x => cat_prod x (product:=p x))).
Defined.

(** [cat_binprod_corec] is also functorial in each morphism. *)

Instance is0functor_cat_binprod_corec_l {A : Type}
  `{HasBinaryProducts A} {x y z : A} (g : z $-> y)
  : Is0Functor (fun f : z $-> x => cat_binprod_corec _ f g).
Proof.
  snapply Build_Is0Functor.
  intros f f' p.
  by napply cat_binprod_corec_eta.
Defined.

Instance is0functor_cat_binprod_corec_r {A : Type}
  `{HasBinaryProducts A} {x y z : A} (f : z $-> x)
  : Is0Functor (fun g : z $-> y => cat_binprod_corec _ f g).
Proof.
  snapply Build_Is0Functor.
  intros g h p.
  by napply cat_binprod_corec_eta.
Defined.

Definition cat_pr1_fmap01_binprod {A : Type} `{HasBinaryProducts A}
  (a : A) {x y : A} (g : x $-> y)
  : cat_pr1 _ $o fmap01 cat_binprod a g $== cat_pr1 _
  := cat_binprod_beta_pr1 _ _ _ $@ cat_idl _.

Definition cat_pr1_fmap10_binprod {A : Type} `{HasBinaryProducts A}
  {x y : A} (f : x $-> y) (a : A)
  : cat_pr1 _ $o fmap10 cat_binprod f a $== f $o cat_pr1 _
  := cat_binprod_beta_pr1 _ _ _.

Definition cat_pr1_fmap11_binprod {A : Type} `{HasBinaryProducts A}
  {w x y z : A} (f : w $-> y) (g : x $-> z)
  : cat_pr1 _ $o fmap11 cat_binprod f g $== f $o cat_pr1 _
  := cat_binprod_beta_pr1 _ _ _.

Definition cat_pr2_fmap01_binprod {A : Type} `{HasBinaryProducts A}
  (a : A) {x y : A} (g : x $-> y)
  : cat_pr2 _ $o fmap01 cat_binprod a g $== g $o cat_pr2 _
  := cat_binprod_beta_pr2 _ _ _.

Definition cat_pr2_fmap10_binprod {A : Type} `{HasBinaryProducts A}
  {x y : A} (f : x $-> y) (a : A)
  : cat_pr2 _ $o fmap10 cat_binprod f a $== cat_pr2 _
  := cat_binprod_beta_pr2 _ _ _ $@ cat_idl _.

Definition cat_pr2_fmap11_binprod {A : Type} `{HasBinaryProducts A}
  {w x y z : A} (f : w $-> y) (g : x $-> z)
  : cat_pr2 _ $o fmap11 cat_binprod f g $== g $o cat_pr2 _
  := cat_binprod_beta_pr2 _ _ _.

(** *** Lemmas about [cat_binprod_corec] *)

Definition cat_binprod_fmap01_corec {A : Type}
  `{Is1Cat A, hbp : !HasBinaryProducts A} {w x y z : A}
  (f : w $-> z) (g : x $-> y) (h : w $-> x)
  : fmap01 cat_binprod z g $o cat_binprod_corec _ f h
    $== cat_binprod_corec _ f (g $o h).
Proof.
  rapply cat_binprod_eta_pr.
  - nrefine (cat_assoc_opp _ _ _ $@ _).
    refine ((_ $@R _) $@ cat_assoc _ _ _ $@ cat_idl _ $@ _ $@ _^$).
    1-3: rapply cat_binprod_beta_pr1.
  - nrefine (cat_assoc_opp _ _ _ $@ _).
    refine ((_ $@R _) $@ cat_assoc _ _ _ $@ (_ $@L _) $@ _^$).
    1-3: rapply cat_binprod_beta_pr2.
Defined.

Definition cat_binprod_fmap10_corec {A : Type}
  `{Is1Cat A, hbp : !HasBinaryProducts A} {w x y z : A}
  (f : x $-> y) (g : w $-> x) (h : w $-> z)
  : fmap10 cat_binprod f z $o cat_binprod_corec _ g h
    $== cat_binprod_corec _ (f $o g) h.
Proof.
  rapply cat_binprod_eta_pr.
  - refine (cat_assoc_opp _ _ _ $@ _).
    refine ((_ $@R _) $@ cat_assoc _ _ _ $@ (_ $@L _) $@ _^$).
    1-3: napply cat_binprod_beta_pr1.
  - refine (cat_assoc_opp _ _ _ $@ _).
    refine ((_ $@R _) $@ cat_assoc _ _ _ $@ cat_idl _ $@ _ $@ _^$).
    1-3: napply cat_binprod_beta_pr2.
Defined.

Definition cat_binprod_fmap11_corec {A : Type}
  `{Is1Cat A, hbp : !HasBinaryProducts A} {v w x y z : A}
  (f : w $-> y) (g : x $-> z) (h : v $-> w) (i : v $-> x)
  : fmap11 cat_binprod f g $o cat_binprod_corec _ h i
    $== cat_binprod_corec _ (f $o h) (g $o i).
Proof.
  rapply cat_binprod_eta_pr.
  - refine (cat_assoc_opp _ _ _ $@ _).
    refine ((_ $@R _) $@ cat_assoc _ _ _ $@ (_ $@L _) $@ _^$).
    1-3: napply cat_binprod_beta_pr1.
  - nrefine (cat_assoc_opp _ _ _ $@ _).
    refine ((_ $@R _) $@ cat_assoc _ _ _ $@ (_ $@L _) $@ _^$).
    1-3: rapply cat_binprod_beta_pr2.
Defined.

(** *** Diagonal *)

(** Annoyingly this doesn't follow directly from the general diagonal since [Bool_rec _ x x] is not definitionally equal to [fun _ => x]. *)
Definition cat_binprod_diag {A : Type} `{Is1Cat A} (x : A)
  (cat_binprod : A) `{isbinprod : !IsBinaryProduct x x cat_binprod}
  : x $-> cat_binprod
  := cat_binprod_corec _ (Id _) (Id _).

Definition cat_binprod_fmap11_diag {A : Type}
  `{HasBinaryProducts A} {x y : A} (f : x $-> y)
  : cat_binprod_diag y _ $o f
    $== fmap11 cat_binprod f f $o cat_binprod_diag x _.
Proof.
  refine (_ $@ _^$).
  2: napply cat_binprod_fmap11_corec.
  napply cat_binprod_eta_pr.
  - refine ((cat_assoc _ _ _)^$ $@ _).
    refine ((_ $@R _) $@ cat_idl _ $@ (cat_idr _)^$ $@ _^$).
    1,2: rapply cat_binprod_beta_pr1.
  - refine ((cat_assoc _ _ _)^$ $@ _).
    refine ((_ $@R _) $@ cat_idl _ $@ (cat_idr _)^$ $@ _^$).
    1,2: rapply cat_binprod_beta_pr2.
Defined.

(** *** Symmetry of binary products *)

Section Symmetry.

  (** The requirement of having all binary products can be weakened further to having specific binary products, but it is not clear this is a useful generality. *)
  Context {A : Type} `{HasEquivs A} `{hbp : !HasBinaryProducts A}.

  Definition cat_binprod_swap (x y : A) : cat_binprod x y $-> cat_binprod y x
    := cat_binprod_corec _ (cat_pr2 _) (cat_pr1 _).

  Lemma cat_binprod_swap_cat_binprod_swap (x y : A)
    : cat_binprod_swap x y $o cat_binprod_swap y x $== Id _.
  Proof.
    napply cat_binprod_eta_pr.
    - refine ((cat_assoc _ _ _)^$ $@ _).
      nrefine (cat_binprod_beta_pr1 _ _ _ $@R _ $@ _).
      exact (cat_binprod_beta_pr2 _ _ _ $@ (cat_idr _)^$).
    - refine ((cat_assoc _ _ _)^$ $@ _).
      nrefine (cat_binprod_beta_pr2 _ _ _ $@R _ $@ _).
      exact (cat_binprod_beta_pr1 _ _ _ $@ (cat_idr _)^$).
  Defined.

  Lemma cate_binprod_swap (x y : A)
    : cat_binprod x y $<~> cat_binprod y x.
  Proof.
    snapply cate_adjointify.
    1,2: napply cat_binprod_swap.
    all: napply cat_binprod_swap_cat_binprod_swap.
  Defined.

  Definition cat_binprod_swap_corec {a b c : A} (f : a $-> b) (g : a $-> c)
    : cat_binprod_swap b c $o cat_binprod_corec _ f g $== cat_binprod_corec _ g f.
  Proof.
    rapply cat_binprod_eta_pr.
    - refine (cat_assoc_opp _ _ _ $@ (_ $@R _) $@ (_ $@ _^$)).
      1,3: napply cat_binprod_beta_pr1.
      napply cat_binprod_beta_pr2.
    - refine (cat_assoc_opp _ _ _ $@ (_ $@R _) $@ (_ $@ _^$)).
      1,3: napply cat_binprod_beta_pr2.
      napply cat_binprod_beta_pr1.
  Defined.

  Definition cat_binprod_swap_nat {a b c d : A} (f : a $-> c) (g : b $-> d)
    : cat_binprod_swap c d $o fmap11 cat_binprod f g
    $== fmap11 cat_binprod g f $o cat_binprod_swap a b
    := cat_binprod_swap_corec _ _ $@ (cat_binprod_fmap11_corec _ _ _ _)^$.

  Local Instance symmetricbraiding_binprod
    : SymmetricBraiding cat_binprod.
  Proof.
    snapply Build_SymmetricBraiding.
    - snapply Build_NatTrans.
      + intros [x y].
        exact (cat_binprod_swap x y).
      + snapply Build_Is1Natural.
        intros [a b] [c d] [f g]; cbn in f, g.
        exact(cat_binprod_swap_nat f g).
    - exact cat_binprod_swap_cat_binprod_swap.
  Defined.

    (** The swap map preserves the diagonal. *)
  Definition cat_binprod_swap_diag (x : A)
    : cat_binprod_swap x x $o cat_binprod_diag x _ $== cat_binprod_diag x _.
  Proof.
    napply cat_binprod_eta_pr.
    - refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      1: napply cat_binprod_beta_pr1.
      refine (cat_binprod_beta_pr2 _ _ _ $@ _^$).
      napply cat_binprod_beta_pr1.
    - refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      1: napply cat_binprod_beta_pr2.
      refine (cat_binprod_beta_pr1 _ _ _ $@ _^$).
      napply cat_binprod_beta_pr2.
  Defined.

End Symmetry.

(** *** Binary product gives a symmetric monoidal structure *)

Section Associativity.

  Context {A : Type} `{HasEquivs A} `{hbp : !HasBinaryProducts A}.

  Definition cat_binprod_twist (x y z : A)
    : cat_binprod x (cat_binprod y z) $-> cat_binprod y (cat_binprod x z).
  Proof.
    rapply cat_binprod_corec.
    - exact (cat_pr1 _ $o cat_pr2 _).
    - exact (fmap01 cat_binprod x (cat_pr2 _)).
  Defined.

  Definition cat_binprod_pr1_twist (x y z : A)
    : cat_pr1 _ $o cat_binprod_twist x y z $== cat_pr1 _ $o cat_pr2 _
    := cat_binprod_beta_pr1 _ _ _.

  Definition cat_binprod_pr1_pr2_twist (x y z : A)
    : cat_pr1 _ $o cat_pr2 _ $o cat_binprod_twist x y z $== cat_pr1 _.
  Proof.
    nrefine (cat_assoc _ _ _ $@ _).
    nrefine ((_ $@L cat_binprod_beta_pr2 _ _ _) $@ _).
    napply cat_pr1_fmap01_binprod.
  Defined.

  Definition cat_binprod_pr2_pr2_twist (x y z : A)
    : cat_pr2 _ $o cat_pr2 _ $o cat_binprod_twist x y z $== cat_pr2 _ $o cat_pr2 _.
  Proof.
    nrefine (cat_assoc _ _ _ $@ _).
    nrefine ((_ $@L cat_binprod_beta_pr2 _ _ _) $@ _).
    napply cat_pr2_fmap01_binprod.
  Defined.

  Definition cat_binprod_twist_corec {w x y z : A}
    (f : w $-> x) (g : w $-> y) (h : w $-> z)
    : cat_binprod_twist x y z $o cat_binprod_corec _ f (cat_binprod_corec _ g h)
      $== cat_binprod_corec _ g (cat_binprod_corec _ f h).
  Proof.
    napply cat_binprod_eta_pr.
    - nrefine (cat_assoc_opp _ _ _ $@ _).
      refine ((_ $@R _) $@ cat_assoc _ _ _ $@ (_ $@L _) $@ (_ $@ _^$)).
      1: napply cat_binprod_pr1_twist.
      1: napply cat_binprod_beta_pr2.
      1,2: napply cat_binprod_beta_pr1.
    - refine (cat_assoc_opp _ _ _ $@ (_ $@R _) $@ _ $@ (cat_binprod_beta_pr2 _ _ _)^$).
      1: napply cat_binprod_beta_pr2.
      nrefine (cat_binprod_fmap01_corec _ _ _ $@ _).
      napply cat_binprod_corec_eta.
      1: exact (Id _).
      napply cat_binprod_beta_pr2.
  Defined.

  Lemma cat_binprod_twist_cat_binprod_twist (x y z : A)
    : cat_binprod_twist x y z $o cat_binprod_twist y x z $== Id _.
  Proof.
    napply cat_binprod_eta_pr_x_xx_id.
    - nrefine (cat_assoc_opp _ _ _ $@ (cat_binprod_pr1_twist _ _ _ $@R _) $@ _).
      napply cat_binprod_pr1_pr2_twist.
    - nrefine (cat_assoc_opp _ _ _ $@ (cat_binprod_pr1_pr2_twist _ _ _ $@R _) $@ _).
      napply cat_binprod_pr1_twist.
    - nrefine (cat_assoc_opp _ _ _ $@ (cat_binprod_pr2_pr2_twist _ _ _ $@R _) $@ _).
      napply cat_binprod_pr2_pr2_twist.
  Defined.

  Definition cate_binprod_twist (x y z : A)
    : cat_binprod x (cat_binprod y z) $<~> cat_binprod y (cat_binprod x z).
  Proof.
    snapply cate_adjointify.
    1,2: napply cat_binprod_twist.
    1,2: napply cat_binprod_twist_cat_binprod_twist.
  Defined.

  Definition cat_binprod_twist_nat {a a' b b' c c' : A}
    (f : a $-> a') (g : b $-> b') (h : c $-> c')
    : cat_binprod_twist a' b' c'
        $o fmap11 cat_binprod f (fmap11 cat_binprod g h)
      $== fmap11 cat_binprod g (fmap11 cat_binprod f h)
        $o cat_binprod_twist a b c.
  Proof.
    napply cat_binprod_eta_pr.
    - refine (cat_assoc_opp _ _ _ $@ _).
      nrefine ((cat_binprod_beta_pr1 _ _ _ $@R _) $@ _).
      nrefine (cat_assoc _ _ _ $@ _).
      nrefine ((_ $@L _) $@ _).
      1: napply cat_pr2_fmap11_binprod.
      nrefine (cat_assoc_opp _ _ _ $@ _).
      nrefine ((_ $@R _) $@ _).
      1: napply cat_pr1_fmap11_binprod.
      nrefine (_ $@ cat_assoc _ _ _).
      refine (_ $@ (_^$ $@R _)).
      2: napply cat_pr1_fmap11_binprod.
      refine (cat_assoc _ _ _ $@ (_ $@L _^$) $@ (cat_assoc _ _ _)^$).
      napply cat_binprod_beta_pr1.
    - nrefine (cat_assoc_opp _ _ _ $@ (cat_binprod_beta_pr2 _ _ _ $@R _) $@ _).
      nrefine (_ $@ cat_assoc _ _ _).
      refine (_ $@ (_^$ $@R _)).
      2: napply cat_pr2_fmap11_binprod.
      refine (_ $@ (_ $@L _^$) $@ (cat_assoc _ _ _)^$).
      2: napply cat_binprod_beta_pr2.
      refine (_^$ $@ _ $@ _).
      1,3: tapply fmap11_comp.
      rapply fmap22.
      1: exact (cat_idl _ $@ (cat_idr _)^$).
      napply cat_binprod_beta_pr2.
  Defined.

  Local Existing Instance symmetricbraiding_binprod.

  #[export] Instance associator_cat_binprod : Associator cat_binprod.
  Proof.
    snapply associator_twist.
    - exact _.
    - exact cat_binprod_twist.
    - exact cat_binprod_twist_cat_binprod_twist.
    - intros ? ? ? ? ? ?; exact cat_binprod_twist_nat.
  Defined.

  Definition cat_pr1_pr1_associator_binprod x y z
    : cat_pr1 _ $o cat_pr1 _ $o associator_cat_binprod x y z $== cat_pr1 _.
  Proof.
    nrefine ((_ $@L associator_twist'_unfold _ _ _ _ _ _ _ _) $@ _).
    nrefine (cat_assoc _ _ _ $@ (_ $@L (cat_assoc_opp _ _ _ $@ (_ $@R _))) $@ _).
    1: napply cat_binprod_beta_pr1.
    do 2 nrefine (cat_assoc_opp _ _ _ $@ _).
    nrefine ((cat_binprod_pr1_pr2_twist _ _ _ $@R _) $@ _).
    napply cat_pr1_fmap01_binprod.
  Defined.

  Definition cat_pr2_pr1_associator_binprod x y z
    : cat_pr2 _ $o cat_pr1 _ $o associator_cat_binprod x y z $== cat_pr1 _ $o cat_pr2 _.
  Proof.
    nrefine ((_ $@L associator_twist'_unfold _ _ _ _ _ _ _ _) $@ _).
    nrefine (cat_assoc _ _ _ $@ (_ $@L (cat_assoc_opp _ _ _ $@ (_ $@R _))) $@ _).
    1: napply cat_binprod_beta_pr1.
    do 2 nrefine (cat_assoc_opp _ _ _ $@ _).
    nrefine ((cat_binprod_pr2_pr2_twist _ _ _ $@R _) $@ _).
    nrefine (cat_assoc _ _ _ $@ (_ $@L cat_pr2_fmap01_binprod _ _) $@ _).
    exact (cat_assoc_opp _ _ _ $@ (cat_binprod_beta_pr2 _ _ _ $@R _)).
  Defined.

  Definition cat_pr2_associator_binprod x y z
    : cat_pr2 _ $o associator_cat_binprod x y z $== cat_pr2 _ $o cat_pr2 _.
  Proof.
    nrefine ((_ $@L associator_twist'_unfold _ _ _ _ _ _ _ _) $@ _).
    nrefine (cat_assoc_opp _ _ _ $@ (cat_binprod_beta_pr2 _ _ _ $@R _) $@ _).
    nrefine (cat_assoc_opp _ _ _ $@ (cat_binprod_pr1_twist _ _ _ $@R _) $@ _).
    nrefine (cat_assoc _ _ _ $@ (_ $@L cat_pr2_fmap01_binprod _ _) $@ _).
    exact (cat_assoc_opp _ _ _ $@ (cat_binprod_beta_pr1 _ _ _ $@R _)).
  Defined.

  Definition cat_binprod_associator_corec {w x y z}
    (f : w $-> x) (g : w $-> y) (h : w $-> z)
    : associator_cat_binprod x y z $o cat_binprod_corec _ f (cat_binprod_corec _ g h)
      $== cat_binprod_corec _ (cat_binprod_corec _ f g) h.
  Proof.
    nrefine ((associator_twist'_unfold _ _ _ _ _ _ _ _ $@R _) $@ _).
    nrefine ((cat_assoc_opp _ _ _ $@R _) $@ cat_assoc _ _ _ $@ (_ $@L (_ $@ _)) $@ _).
    1: napply cat_binprod_fmap01_corec.
    1: rapply (cat_binprod_corec_eta _ _ _ _ _ (Id _)).
    1: napply cat_binprod_swap_corec.
    nrefine (cat_assoc _ _ _ $@ (_ $@L _) $@ _).
    1: napply cat_binprod_twist_corec.
    napply cat_binprod_swap_corec.
  Defined.

  Context (unit : A) `{!IsTerminal unit}.

  Local Instance right_unitor_binprod
    : RightUnitor cat_binprod unit.
  Proof.
    snapply Build_NatEquiv.
    - intros a; unfold flip.
      snapply cate_adjointify.
      + exact (cat_pr1 _).
      + exact (cat_binprod_corec _ (Id _) (mor_terminal _ _)).
      + exact (cat_binprod_beta_pr1 _ _ _).
      + napply cat_binprod_eta_pr.
        * nrefine (cat_assoc_opp _ _ _ $@ (cat_binprod_beta_pr1 _ _ _ $@R _) $@ _).
          exact (cat_idl _ $@ (cat_idr _)^$).
        * nrefine (cat_assoc_opp _ _ _ $@ (cat_binprod_beta_pr2 _ _ _ $@R _) $@ _).
          exact ((mor_terminal_unique _ _ _)^$ $@ mor_terminal_unique _ _ _).
    - snapply Build_Is1Natural.
      intros a b f.
      refine ((_ $@R _) $@ _ $@ (_ $@L _^$)).
      1,3: napply cate_buildequiv_fun.
      napply cat_binprod_beta_pr1.
  Defined.

  Local Existing Instance left_unitor_twist.

  Local Instance triangle_binprod
    : TriangleIdentity cat_binprod unit.
  Proof.
    snapply triangle_twist.
    intros a b.
    refine (fmap02 _ _ _ $@ _ $@ ((_ $@L fmap02 _ _ _^$) $@R _)).
    1,3: napply cate_buildequiv_fun.
    napply cat_binprod_eta_pr.
    - nrefine (cat_pr1_fmap01_binprod _ _ $@ _ $@ cat_assoc _ _ _).
      refine (_ $@ (((_^$ $@R _) $@ cat_assoc _ _ _) $@R _)).
      2: napply cat_binprod_beta_pr1.
      refine ((_ $@R _) $@ _)^$.
      1: napply cat_pr2_fmap01_binprod.
      napply cat_binprod_pr1_pr2_twist.
    - nrefine (cat_pr2_fmap01_binprod _ _ $@ _ $@ cat_assoc _ _ _).
      refine (_ $@ (((cat_binprod_beta_pr2 _ _ _)^$ $@R _) $@ cat_assoc _ _ _ $@R _)).
      refine ((_ $@R _) $@ _)^$.
      1: napply cat_pr1_fmap01_binprod.
      napply cat_binprod_beta_pr1.
  Defined.

  #[export] Instance pentagon_binprod
    : PentagonIdentity cat_binprod.
  Proof.
    intros a b c d.
    napply cat_binprod_eta_pr_xx_x.
    - nrefine (cat_assoc_opp _ _ _ $@ (_ $@R _) $@ _).
      1: napply cat_pr1_pr1_associator_binprod.
      refine (_ $@ (_ $@L ((((_^$ $@R _) $@ cat_assoc _ _ _) $@R _)
        $@ cat_assoc _ _ _)) $@ cat_assoc_opp _ _ _).
      2: napply cat_pr1_fmap10_binprod.
      do 2 nrefine (_ $@ (_ $@L cat_assoc_opp _ _ _)).
      napply cat_binprod_eta_pr.
      + nrefine (cat_assoc_opp _ _ _ $@ _ $@ cat_assoc _ _ _).
        refine (_ $@ _ $@ (_^$ $@R _) $@ cat_assoc _ _ _).
        1,3: napply cat_pr1_pr1_associator_binprod.
        do 2 nrefine (_ $@ cat_assoc _ _ _).
        refine (_^$ $@ (_^$ $@R _)).
        2: napply cat_pr1_pr1_associator_binprod.
        napply cat_pr1_fmap01_binprod.
      + nrefine (cat_assoc_opp _ _ _ $@ _ $@ cat_assoc _ _ _).
        refine (_ $@ _ $@ (_^$ $@R _) $@ cat_assoc _ _ _).
        1,3: napply cat_pr2_pr1_associator_binprod.
        do 2 nrefine (_ $@ cat_assoc _ _ _).
        refine (_ $@ ((cat_assoc _ _ _ $@ (_ $@L (_^$ $@ cat_assoc _ _ _))
          $@ cat_assoc_opp _ _ _ $@ cat_assoc_opp _ _ _) $@R _)).
        2: napply cat_pr2_pr1_associator_binprod.
        refine (_^$ $@ (_ $@L _^$) $@ cat_assoc_opp _ _ _).
        2: napply cat_pr2_fmap01_binprod.
        nrefine (cat_assoc_opp _ _ _ $@ (_ $@R _)).
        napply cat_pr1_pr1_associator_binprod.
    - nrefine (cat_assoc_opp _ _ _ $@ (_ $@R _) $@ _).
      1: napply cat_pr2_pr1_associator_binprod.
      nrefine (cat_assoc _ _ _ $@ _ $@ cat_assoc_opp _ _ _).
      nrefine ((_ $@L cat_pr2_associator_binprod _ _ _) $@ _).
      refine (_ $@ (_ $@L ((((_^$ $@R _) $@ cat_assoc _ _ _) $@R _) $@ cat_assoc _ _ _))).
      2: napply cat_pr1_fmap10_binprod.
      nrefine (_ $@ (_ $@L (cat_assoc_opp _ _ _ $@ cat_assoc_opp _ _ _))).
      refine (_ $@ (_^$ $@R _) $@ cat_assoc _ _ _).
      2: napply cat_pr2_associator_binprod.
      refine (_ $@ (_ $@L ((_^$ $@R _) $@ cat_assoc _ _ _ $@ cat_assoc _ _ _)) $@ cat_assoc_opp _ _ _).
      2: napply cat_pr2_pr1_associator_binprod.
      refine (_ $@ (_ $@L ((_ $@L _^$) $@ cat_assoc_opp _ _ _))).
      2: napply cat_pr2_fmap01_binprod.
      refine (cat_assoc_opp _ _ _ $@ (_^$ $@R _) $@ cat_assoc _ _ _ $@ cat_assoc _ _ _).
      napply cat_pr2_pr1_associator_binprod.
    - nrefine (cat_assoc_opp _ _ _ $@ (cat_pr2_associator_binprod _ _ _ $@R _) $@ _).
      nrefine (cat_assoc _ _ _ $@ (_ $@L (cat_pr2_associator_binprod _ _ _)) $@ _).
      refine (_ $@ (_^$ $@R _) $@ cat_assoc _ _ _ $@ (_ $@L (cat_assoc_opp _ _ _))).
      2: napply cat_pr2_fmap10_binprod.
      refine (_ $@ cat_assoc_opp _ _ _ $@ (_^$ $@R _) $@ cat_assoc _ _ _).
      2: napply cat_pr2_associator_binprod.
      refine (cat_assoc_opp _ _ _ $@ (_^$ $@R _) $@ cat_assoc _ _ _
        $@ (_ $@L (cat_pr2_fmap01_binprod _ _)^$)).
      napply cat_pr2_associator_binprod.
  Defined.

  #[export] Instance hexagon_identity
    : HexagonIdentity cat_binprod.
  Proof.
    intros a b c.
    nrefine (cat_assoc _ _ _ $@ _ $@ cat_assoc_opp _ _ _).
    napply cat_binprod_eta_pr.
    { nrefine (cat_assoc_opp _ _ _ $@ (cat_pr1_fmap10_binprod _ _ $@R _) $@ _).
      nrefine (cat_assoc _ _ _ $@ _).
      napply cat_binprod_eta_pr.
      { nrefine (cat_assoc_opp _ _ _ $@ _ $@ cat_assoc _ _ _ $@ cat_assoc _ _ _).
        refine ((_ $@R _) $@ _ $@ (_^$ $@R _)).
        1: napply cat_binprod_beta_pr1.
        2: napply cat_pr1_pr1_associator_binprod.
        nrefine (cat_assoc_opp _ _ _ $@ cat_assoc_opp _ _ _ $@ _ $@ cat_assoc _ _ _).
        refine ((_ $@R _) $@ _ $@ (_^$ $@R _)).
        1: napply cat_pr2_pr1_associator_binprod.
        2: napply cat_binprod_beta_pr1.
        refine (cat_assoc _ _ _ $@ (_ $@L _) $@ cat_assoc_opp _ _ _ $@ (_ $@R _) $@ _^$).
        1: napply cat_pr2_fmap01_binprod.
        2: napply cat_pr2_associator_binprod.
        napply cat_binprod_beta_pr1. }
      nrefine (cat_assoc_opp _ _ _ $@ _ $@ cat_assoc _ _ _ $@ cat_assoc _ _ _).
      refine ((_ $@R _) $@ _ $@ (_^$ $@R _)).
      1: napply cat_binprod_beta_pr2.
      2: napply cat_pr2_pr1_associator_binprod.
      nrefine (cat_assoc_opp _ _ _ $@ cat_assoc_opp _ _ _ $@ _ $@ cat_assoc _ _ _).
      refine ((_ $@R _) $@ _ $@ (((_ $@L _^$) $@ cat_assoc_opp _ _ _) $@R _)).
      1: napply cat_pr1_pr1_associator_binprod.
      2: napply cat_binprod_beta_pr2.
      refine (cat_pr1_fmap01_binprod _ _ $@ _^$).
      napply cat_pr1_pr1_associator_binprod. }
    nrefine (cat_assoc_opp _ _ _ $@ _ $@ cat_assoc _ _ _ $@ cat_assoc _ _ _).
    refine ((_ $@R _) $@ _ $@ ((_^$ $@R _) $@R _)).
    1: napply cat_pr2_fmap10_binprod.
    2: napply cat_pr2_associator_binprod.
    nrefine (cat_assoc_opp _ _ _ $@ (cat_pr2_associator_binprod _ _ _ $@R _) $@ _).
    nrefine (cat_assoc _ _ _ $@ (_ $@L _) $@ _ $@ (cat_assoc_opp _ _ _ $@R _)).
    1: napply cat_pr2_fmap01_binprod.
    refine (cat_assoc_opp _ _ _ $@ (_ $@R _) $@ _^$ $@ ((_ $@L _^$) $@R _)).
    1,3: napply cat_binprod_beta_pr2.
    napply cat_pr2_pr1_associator_binprod.
  Defined.

  Local Instance ismonoidal_cat_binprod
    : IsMonoidal A cat_binprod unit
    := {}.

  (** Many of the above instances are declared to be local because they follow from this one. *)
  #[export] Instance issymmetricmonoidal_cat_binprod
    : IsSymmetricMonoidal A cat_binprod unit
    := {}.

End Associativity.

(** ** Examples *)

(** *** Products in Type *)

(** Since we use the Yoneda lemma in this file, we therefore depend on WildCat.Universe which means these instances have to live here. *)

(** Assuming [Funext], [Type] has all products. *)
Instance hasallproducts_type `{Funext} : HasAllProducts Type.
Proof.
  intros I x.
  snapply Build_Product.
  - exact (forall (i : I), x i).
  - intros i f. exact (f i).
  - intros Z f a i. exact (f i a).
  - reflexivity.
  - intros Z f g p a.
    exact (path_forall _ _ (fun i => p i a)).
Defined.

(** It follows that [Type] has binary products, but we prove this separately to avoid [Funext]. *)
Instance hasbinaryproducts_type : HasBinaryProducts Type.
Proof.
  intros X Y.
  snapply Build_BinaryProduct.
  - exact (X * Y).
  - exact fst.
  - exact snd.
  - intros Z f g z. exact (f z, g z).
  - reflexivity.
  - reflexivity.
  - intros Z f g p q x.
    napply path_prod.
    + exact (p x).
    + exact (q x).
Defined.

(** *** Products in ZeroGpd *)

(** Since we use products in ZeroGpd to define general products, we must depend on ZeroGroupoid, which means that these instances have to live here. *)

(** Note that this does not rely on [Funext], since the 1-cells in the product 0-groupoid are *defined* to be homotopies. *)
Instance hasallproducts_0gpd : HasAllProducts ZeroGpd.
Proof.
  intros I x.
  snapply Build_Product.
  - exact (prod_0gpd I x).
  - exact prod_0gpd_pr.
  - intro G. apply equiv_prod_0gpd_corec.
  - reflexivity.
  - intros G f g p. intro a. intro i.
    exact (p i a).
Defined.

(** This follows from the previous result, but we prove it separately because using these custom binary products can make certain things easier, and can sometimes avoid the need to use [Funext]. *)
Instance hasbinaryproducts_0gpd : HasBinaryProducts ZeroGpd.
Proof.
  intros G H.
  snapply Build_BinaryProduct.
  - exact (binprod_0gpd G H).
  - apply binprod_0gpd_pr1.
  - apply binprod_0gpd_pr2.
  - intros K f g. exact (equiv_binprod_0gpd_corec G H K (f, g)).
  - reflexivity.
  - reflexivity.
  - intros K f g p q k. exact (p k, q k).
Defined.
