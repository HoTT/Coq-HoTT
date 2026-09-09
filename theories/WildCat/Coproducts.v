Require Import Basics.Overture Basics.Equivalences Basics.Tactics Basics.Decidable.
Require Import Types.Bool.
Require Import WildCat.Core WildCat.Equiv WildCat.Forall WildCat.NatTrans
               WildCat.Opposite WildCat.Products WildCat.Universe
               WildCat.Yoneda WildCat.ZeroGroupoid WildCat.PointedCat
               WildCat.Monoidal WildCat.Bifunctor.

(** * Categories with coproducts *)

(** ** Indexed coproducts *)

(** For [A] a wild 1-category, [I] a type, and [x : I -> A] an [I]-indexed family of objects in [A], we study the categorical coproduct of this family of objects.  As much as possible, we use the results from Products.v in [A^op]. *)

(** When [x] is an [I]-indexed family of objects in [A] and [coprod] is an object with an [I]-indexed family of inclusions, we get for each [z] an induced map from the 0-groupoid of morphisms [coprod $-> z] to the product of the 0-groupoids [x i $-> z] over [i : I]. *)
Definition cat_coprod_rec_inv {A : Type} `{Is1Cat A}
  {I : Type} (x : I -> A) (coprod : A) (inj : forall i, x i $-> coprod) (z : A)
  : yon_0gpd z coprod $-> prod_0gpd I (fun i => yon_0gpd z (x i))
  := cat_prod_corec_inv (A:=A^op) x coprod inj z.

(** An object is a coproduct of an [I]-indexed family if there is an [I]-indexed family of inclusions such that the induced map defined above is an equivalence.  We record this as the object being a product in the opposite category and deduce the relevant structure.  *)
Class IsCoproduct {A : Type} `{Is1Cat A} {I : Type} (x : I -> A) (cat_coprod : A)
  := iscoproduct :: IsProduct (A:=A^op) x cat_coprod.

Definition cat_in {A : Type} `{Is1Cat A} {I : Type} {x : I -> A} {cat_coprod : A}
  `{!IsCoproduct x cat_coprod} (i : I)
  : x i $-> cat_coprod
  := cat_pr (A:=A^op) (x:=x) (cat_prod:=cat_coprod) i.

Arguments cat_in {A _ _ _ _ _ x cat_coprod iscoprod} : rename.

Instance cat_isequiv_cat_coprod_rec_inv {A : Type} `{Is1Cat A}
  {I : Type} (x : I -> A) (cat_coprod : A) `{!IsCoproduct x cat_coprod}
  : forall (z : A), CatIsEquiv (cat_coprod_rec_inv x cat_coprod cat_in z)
  := cat_isequiv_cat_prod_corec_inv (A:=A^op) x cat_coprod.

Arguments cat_isequiv_cat_coprod_rec_inv {A _ _ _ _ _} x cat_coprod {iscoprod} : rename.

(** A coproduct in a category is a product in the opposite category. *)
Class Coproduct {A : Type} `{Is1Cat A} {I : Type} (x : I -> A)
  := coprod : Product (A:=A^op) x.

Definition cat_coprod {A : Type} `{Is1Cat A} {I : Type} (x : I -> A) `{!Coproduct x} : A
  := coprod.(cat_prod x).

Arguments cat_coprod {A _ _ _ _ _} x {coproduct} : rename.

(** We derive that a coproduct is also a coproduct in the sense above. *)
Instance cat_iscoprod {A : Type} `{Is1Cat A} {I : Type} (x : I -> A) `{!Coproduct x}
  : IsCoproduct x (cat_coprod x)
  := coprod.(cat_isprod x).

Arguments cat_iscoprod {A _ _ _ _ _} x {coproduct} : rename.

(** A wrapper for building coproducts with less typechecking. *)
Definition Build_Coproduct' {A : Type} `{Is1Cat A} {I : Type} (x : I -> A)
  (cat_coprod : A) (cat_iscoprod : IsCoproduct x cat_coprod)
  : Coproduct x
  := Build_Product' (A:=A^op) x cat_coprod cat_iscoprod.

Section CoproductConstructors.

  Context {A : Type} `{Is1Cat A} {I : Type} (x : I -> A)
    (cat_coprod : A) (cat_in : forall i : I, x i $-> cat_coprod)
    (cat_coprod_rec : forall z : A,
      (forall i : I, x i $-> z) -> (cat_coprod $-> z))
    (cat_coprod_beta_in : forall (z : A) (f : forall i, x i $-> z) (i : I),
      cat_coprod_rec z f $o cat_in i $== f i)
    (cat_coprod_eta_in : forall (z : A) (f g : cat_coprod $-> z),
      (forall i : I, f $o cat_in i $== g $o cat_in i) -> f $== g).

  (** A convenience wrapper for building [IsCoproduct]. *)
  Definition Build_IsCoproduct : IsCoproduct x cat_coprod
    := Build_IsProduct (A:=A^op) x cat_coprod cat_in cat_coprod_rec
        cat_coprod_beta_in cat_coprod_eta_in.

  (** A convenience wrapper for building coproducts. *)
  Definition Build_Coproduct : Coproduct x
    := Build_Coproduct' x cat_coprod Build_IsCoproduct.

End CoproductConstructors.

Section Lemmata.
  Context {A : Type} `{Is1Cat A} {I : Type} {x : I -> A} (cat_coprod : A)
    `{!IsCoproduct x cat_coprod}.

  Definition cate_cat_coprod_rec_inv {z : A}
    : yon_0gpd z cat_coprod $<~> prod_0gpd I (fun i => yon_0gpd z (x i))
    := cate_cat_prod_corec_inv (A:=A^op) (x:=x) cat_coprod.

  Definition cate_cat_coprod_rec {z : A}
    : prod_0gpd I (fun i => yon_0gpd z (x i)) $<~> yon_0gpd z cat_coprod
    := cate_cat_prod_corec (A:=A^op) (x:=x) cat_coprod.

  Definition cat_coprod_rec {z : A}
    : (forall i, x i $-> z) -> cat_coprod $-> z
    := cat_prod_corec (A:=A^op) (x:=x) cat_coprod.

  Definition cat_coprod_beta {z : A} (f : forall i, x i $-> z)
    : forall i, cat_coprod_rec f $o cat_in i $== f i
    := cat_prod_beta (A:=A^op) (x:=x) cat_coprod f.

  Definition cat_coprod_eta {z : A} (f : cat_coprod $-> z)
    : cat_coprod_rec (fun i => f $o cat_in i) $== f
    := cat_prod_eta (A:=A^op) (x:=x) cat_coprod f.

  Definition natequiv_cat_coprod_rec_inv
    : NatEquiv (fun z => yon_0gpd z cat_coprod)
      (fun z : A => prod_0gpd I (fun i => yon_0gpd z (x i)))
    := natequiv_cat_prod_corec_inv (A:=A^op) (x:=x) cat_coprod.

  Definition cat_coprod_rec_eta {z : A} {f g : forall i, x i $-> z}
    : (forall i, f i $== g i) -> cat_coprod_rec f $== cat_coprod_rec g
    := cat_prod_corec_eta (A:=A^op) (x:=x) cat_coprod.

  Definition cat_coprod_in_eta {z : A} {f g : cat_coprod $-> z}
    : (forall i, f $o cat_in i $== g $o cat_in i) -> f $== g
    := cat_prod_pr_eta (A:=A^op) (x:=x) cat_coprod.

End Lemmata.

Section InducedFromEquiv.

  Context {A : Type} `{HasEquivs A} {I : Type} {x : I -> A}
    (cat_coprod : A) `{!IsCoproduct x cat_coprod}
    (y : A) (f : cat_coprod $<~> y).

  (** A categorical equivalence out of a coproduct induces a coproduct structure on the codomain. *)
  Local Instance cat_coprod_coprod_equiv : IsCoproduct x y
    := cat_prod_equiv_prod (A:=A^op) (x:=x) cat_coprod _ f.

  (** The induced inclusion is given by the equivalence. *)
  Definition cat_in_comp (i : I)
    : cat_in i $== f $o cat_in i
    := cat_pr_comp cat_coprod y _ i.

  (** The induced recursion is given by the equivalence. *)
  Definition cat_coprod_rec_comp {z : A} (D : forall i, x i $-> z)
    : cat_coprod_rec y D $o f $== cat_coprod_rec cat_coprod D
    := cat_prod_corec_comp (A:=A^op) (he:=hasequivs_op) cat_coprod y f D.

End InducedFromEquiv.

(** *** Codiagonal / fold map out of the coproduct of a constant family *)

Definition cat_coprod_codiag {A : Type} {I : Type} (x : A) (cat_coprod : A)
  `{IsCoproduct _ I (fun _ => x) cat_coprod}
  : cat_coprod $-> x
  := cat_prod_diag (A:=A^op) x cat_coprod.

(** *** Uniqueness of coproducts *)

(** [I]-indexed coproducts are unique no matter how they are constructed. *)
Definition cate_cat_coprod {A : Type} `{HasEquivs A} {I J : Type} (ie : I <~> J)
  (x : I -> A) (coprod_x : A) `{!IsCoproduct x coprod_x}
  (y : J -> A) (coprod_y : A) `{!IsCoproduct y coprod_y}
  (e : forall (i : I), y (ie i) $<~> x i)
  : coprod_y $<~> coprod_x
  := cate_cat_prod (A:=A^op) ie x coprod_x y coprod_y e.

(** [I]-indexed coproducts are unique. *)
Definition cat_coprod_unique {A : Type} `{HasEquivs A} {I : Type}
  (x : I -> A) (coprod_x : A) `{!IsCoproduct x coprod_x}
  (y : I -> A) (coprod_y : A) `{!IsCoproduct y coprod_y}
  (e : forall i : I, x i $<~> y i)
  : coprod_x $<~> coprod_y
  := cate_cat_coprod 1 y _ x _ e.

(** *** Existence of coproducts *)

Class HasCoproducts (A : Type) `{Is1Cat A} (I : Type)
  := has_coproducts :: forall x : I -> A, Coproduct x.

Class HasAllCoproducts (A : Type) `{Is1Cat A}
  := has_all_coproducts :: forall I : Type, HasCoproducts A I.

(** *** Coproduct functor *)

Local Instance hasproductsop_hascoproducts {A I : Type} `{HasCoproducts A I}
  : HasProducts A^op I
  := fun x : I -> A^op => has_coproducts (A:=A) x.

Instance is0functor_cat_coprod (A : Type) (I : Type) `{IsGraph I}
  `{HasCoproducts A I}
  : @Is0Functor (I -> A) A (isgraph_forall I (fun _ => A)) _
    (fun x : I -> A => cat_coprod x).
Proof.
  apply is0functor_op'.
  exact (is0functor_cat_prod A^op I).
Defined.

Instance is1functor_cat_coprod (A : Type) (I : Type) `{IsGraph I}
  `{HasCoproducts A I}
  : @Is1Functor (I -> A) A _ _ _ (is1cat_forall I (fun _ => A)) _ _ _ _
    (fun x : I -> A => cat_coprod x) _.
Proof.
  apply is1functor_op'.
  exact (is1functor_cat_prod A^op I).
Defined.

(** *** Categories with specific kinds of coproducts *)

Definition isinitial_coprod_empty {A : Type} `{Is1Cat A} {x : Empty -> A}
  {coprod_empty : A} {coprod : IsCoproduct x coprod_empty}
  : IsInitial coprod_empty
  := isterminal_prod_empty (A:=A^op) (isprod:=coprod).

(** ** Binary coproducts *)

Class IsBinaryCoproduct {A : Type} `{Is1Cat A} (x y : A) (cat_bincoprod : A)
  := is_binary_coproduct :: IsBinaryProduct (A:=A^op) x y cat_bincoprod.

Instance isbincoprod_iscoprod {A : Type} `{Is1Cat A} (x y : A)
  (cat_bincoprod : A) `{!IsBinaryCoproduct x y cat_bincoprod}
  : IsCoproduct (Bool_rec _ x y) cat_bincoprod
  := is_binary_product.

Class BinaryCoproduct {A : Type} `{Is1Cat A} (x y : A)
  := binary_coproduct :: BinaryProduct (A:=A^op) x y.

Instance isbinarycoproduct_binarycoproduct {A : Type} `{Is1Cat A}
  (x y : A) {coprod : BinaryCoproduct x y}
  : IsBinaryCoproduct x y coprod.(cat_prod _)
  := cat_isprod _.

(** A category with binary coproducts is a category with a binary coproduct for each pair of objects. *)
Class HasBinaryCoproducts (A : Type) `{Is1Cat A}
  := has_binary_coproducts :: forall x y : A, BinaryCoproduct x y.

Instance hasbinarycoproducts_hascoproductsbool {A : Type}
  `{HasCoproducts A Bool}
  : HasBinaryCoproducts A
  := fun x y => has_coproducts (Bool_rec _ x y).

Section BinaryCoproducts.

  Context {A : Type} `{Is1Cat A} {x y : A}
    (cat_bincoprod : A) {isbincoprod : IsBinaryCoproduct x y cat_bincoprod}.

  Definition cat_inl : x $-> cat_bincoprod
    := cat_pr1 cat_bincoprod (isbinprod:=isbincoprod).

  Definition cat_inr : y $-> cat_bincoprod
    := cat_pr2 cat_bincoprod (isbinprod:=isbincoprod).

  Definition cat_bincoprod_rec {z : A} (f : x $-> z) (g : y $-> z)
    : cat_bincoprod $-> z
    := cat_binprod_corec (isbinprod:=isbincoprod) cat_bincoprod f g.

  Definition cat_bincoprod_beta_inl {z : A} (f : x $-> z) (g : y $-> z)
    : cat_bincoprod_rec f g $o cat_inl $== f
    := cat_binprod_beta_pr1 (isbinprod:=isbincoprod) cat_bincoprod f g.

  Definition cat_bincoprod_beta_inr {z : A} (f : x $-> z) (g : y $-> z)
    : cat_bincoprod_rec f g $o cat_inr $== g
    := cat_binprod_beta_pr2 (isbinprod:=isbincoprod) cat_bincoprod f g.

  Definition cat_bincoprod_eta {z : A} (f : cat_bincoprod $-> z)
    : cat_bincoprod_rec (f $o cat_inl) (f $o cat_inr) $== f
    := cat_binprod_eta (isbinprod:=isbincoprod) cat_bincoprod f.

  Definition cat_bincoprod_eta_in {z : A} {f g : cat_bincoprod $-> z}
    : f $o cat_inl $== g $o cat_inl
      -> f $o cat_inr $== g $o cat_inr
      -> f $== g
    := cat_binprod_eta_pr (isbinprod:=isbincoprod) cat_bincoprod f g.

  Definition cat_bincoprod_rec_eta {z : A} {f f' : x $-> z} {g g' : y $-> z}
    : f $== f'
      -> g $== g'
      -> cat_bincoprod_rec f g $== cat_bincoprod_rec f' g'
    := cat_binprod_corec_eta (isbinprod:=isbincoprod) cat_bincoprod f f' g g'.

End BinaryCoproducts.

Section BinaryCoproductConstructors.

  Context {A : Type} `{Is1Cat A} {x y : A}
    (cat_bincoprod : A) (cat_inl : x $-> cat_bincoprod) (cat_inr : y $-> cat_bincoprod)
    (cat_bincoprod_rec : forall z : A, (x $-> z) -> (y $-> z) -> cat_bincoprod $-> z)
    (cat_bincoprod_beta_inl : forall (z : A) (f : x $-> z) (g : y $-> z),
      cat_bincoprod_rec z f g $o cat_inl $== f)
    (cat_bincoprod_beta_inr : forall (z : A) (f : x $-> z) (g : y $-> z),
      cat_bincoprod_rec z f g $o cat_inr $== g)
    (cat_bincoprod_eta_in : forall (z : A) (f g : cat_bincoprod $-> z),
      f $o cat_inl $== g $o cat_inl -> f $o cat_inr $== g $o cat_inr -> f $== g).

  (** A convenience wrapper for building [IsBinaryCoproduct]. *)
  Definition Build_IsBinaryCoproduct : IsBinaryCoproduct x y cat_bincoprod
    := Build_IsBinaryProduct
        (cat_bincoprod : A^op)
        cat_inl
        cat_inr
        cat_bincoprod_rec
        cat_bincoprod_beta_inl
        cat_bincoprod_beta_inr
        cat_bincoprod_eta_in.

  (** A convenience wrapper for building binary coproducts. *)
  Definition Build_BinaryCoproduct : BinaryCoproduct x y
    := Build_Coproduct' _ cat_bincoprod Build_IsBinaryCoproduct.

End BinaryCoproductConstructors.

Definition cat_bincoprod {A: Type} `{HasBinaryCoproducts A} (x y : A) : A
  := cat_coprod (Bool_rec _ x y) (coproduct:=has_binary_coproducts x y).

Instance cat_isbincoprod {A: Type} `{HasBinaryCoproducts A} (x y : A)
  : IsBinaryCoproduct x y (cat_bincoprod x y)
  := cat_iscoprod (Bool_rec _ x y) (coproduct:=has_binary_coproducts x y).

(** From binary coproducts, all [Bool]-shaped coproducts can be constructed. This should not be an instance to avoid a cycle with [hasbinarycoproducts_hascoproductsbool]. *)
Definition hascoproductsbool_hasbinarycoproducts {A : Type}
  `{hbc : HasBinaryCoproducts A}
  : HasCoproducts A Bool
  := hasproductsbool_hasbinaryproducts (A:=A^op) (hbp:=hbc).

(** *** Binary coproduct functor *)

(** Hint: Use [Set Printing Implicit] to see the implicit arguments in the following proofs. *)

Instance is0bifunctor_cat_bincoprod {A : Type}
  `{hbc : HasBinaryCoproducts A}
  : Is0Bifunctor cat_bincoprod.
Proof.
  napply is0bifunctor_op'.
  exact (is0bifunctor_cat_binprod (A:=A^op) (hbp:=hbc)).
Defined.

Instance is1bifunctor_cat_bincoprod {A : Type}
  `{hbc : HasBinaryCoproducts A}
  : Is1Bifunctor cat_bincoprod.
Proof.
  napply is1bifunctor_op'.
  exact (is1bifunctor_cat_binprod (A:=A^op) (hbp:=hbc)).
Defined.

(** Products.v proves further results about the functoriality of binary products which have not been needed for coproducts so far:  that [cat_binprod_corec] is functorial in each of its two morphism arguments ([is0functor_cat_binprod_corec_l] and [is0functor_cat_binprod_corec_r]), and how each projection interacts with each of [fmap01], [fmap10] and [fmap11] ([cat_pr1_fmap01_binprod] and its five variants).  If needed, the duals can be obtained from those results in [A^op]. *)

(** *** Products and coproducts in the opposite category *)

Instance iscoproduct_op {A I : Type} `{Is1Cat A} (x : I -> A)
  (cat_prod : A) {isprod : IsProduct x cat_prod}
  : IsCoproduct (A:=A^op) x cat_prod
  := isprod.

Instance coproduct_op {A I : Type} `{Is1Cat A} (x : I -> A)
  {prod : Product x}
  : Coproduct (A:=A^op) x
  := prod.

Instance hasbinarycoproducts_op_hasbinaryproducts {A : Type}
  `{Is1Cat A, hbp : !HasBinaryProducts A}
  : HasBinaryCoproducts A^op
  := hbp.

Definition hasbinarycoproducts_hasbinaryproducts_op {A : Type}
  `{Is1Cat A, hbp : !HasBinaryProducts A^op}
  : HasBinaryCoproducts A
  := hbp.
Hint Immediate hasbinarycoproducts_hasbinaryproducts_op : typeclass_instances.

Instance hasbinaryproducts_op_hasbinarycoproducts {A : Type}
  `{Is1Cat A, hbc : !HasBinaryCoproducts A}
  : HasBinaryProducts A^op
  := hbc.

Definition hasbinaryproducts_hasbinarycoproducts_op {A : Type}
  `{Is1Cat A, hbc : !HasBinaryCoproducts A^op}
  : HasBinaryProducts A
  := hbc.
Hint Immediate hasbinaryproducts_hasbinarycoproducts_op : typeclass_instances.

(** *** Lemmas about [cat_bincoprod_rec] *)

Definition cat_bincoprod_fmap01_rec {A : Type}
  `{Is1Cat A, hbc : !HasBinaryCoproducts A} {w x y z : A}
  (f : z $-> w) (g : y $-> x) (h : x $-> w)
  : cat_bincoprod_rec _ f h
      $o fmap01 cat_bincoprod z g
    $== cat_bincoprod_rec _ f (h $o g)
  := cat_binprod_fmap01_corec (hbp:=hbc) f g h.

Definition cat_bincoprod_fmap10_rec {A : Type}
  `{Is1Cat A, hbc : !HasBinaryCoproducts A} {w x y z : A}
  (f : y $-> x) (g : x $-> w) (h : z $-> w)
  : cat_bincoprod_rec _ g h
      $o fmap10 cat_bincoprod f z
    $== cat_bincoprod_rec _ (g $o f) h
  := cat_binprod_fmap10_corec (hbp:=hbc) f g h.

Definition cat_bincoprod_fmap11_rec {A : Type}
  `{Is1Cat A, hbc : !HasBinaryCoproducts A} {v w x y z : A}
  (f : y $-> w) (g : z $-> x) (h : w $-> v) (i : x $-> v)
  : cat_bincoprod_rec _ h i
      $o fmap11 cat_bincoprod f g
    $== cat_bincoprod_rec _ (h $o f) (i $o g)
  := cat_binprod_fmap11_corec (hbp:=hbc) f g h i.

(** *** Codiagonal *)

Definition cat_bincoprod_codiag {A : Type} `{Is1Cat A} (x : A)
  (cat_bincoprod : A) {isbincoprod : IsBinaryCoproduct x x cat_bincoprod}
  : cat_bincoprod $-> x
  := cat_binprod_diag (isbinprod:=isbincoprod) x cat_bincoprod.

Definition cat_bincoprod_fmap11_codiag {A : Type}
  `{HasBinaryCoproducts A} {x y : A} (f : x $-> y)
  : f $o cat_bincoprod_codiag x _
    $== cat_bincoprod_codiag y _ $o fmap11 cat_bincoprod f f
  := cat_binprod_fmap11_diag (A:=A^op) _.

(** *** Symmetry of coproducts *)

Definition cat_bincoprod_swap {A : Type} `{Is1Cat A}
  {hbc : HasBinaryCoproducts A} (x y : A)
  : cat_bincoprod x y $-> cat_bincoprod y x
  := cat_binprod_swap (hbp:=hbc) _ _.

Definition cate_bincoprod_swap {A : Type} `{HasEquivs A}
  {hbc : HasBinaryCoproducts A} (x y : A)
  : cat_bincoprod x y $<~> cat_bincoprod y x
  := cate_binprod_swap (A:=A^op) (hbp:=hbc) _ _.

Definition cat_bincoprod_swap_codiag {A : Type} `{Is1Cat A}
  {hbc : HasBinaryCoproducts A} (x : A)
  : cat_bincoprod_codiag x _ $o cat_bincoprod_swap x x
    $== cat_bincoprod_codiag x _
  := cat_binprod_swap_diag (A:=A^op) x.

Definition cat_bincoprod_swap_rec {A : Type} `{Is1Cat A}
  `{hbc : !HasBinaryCoproducts A} {a b c : A} (f : a $-> c) (g : b $-> c)
  : cat_bincoprod_rec _ f g $o cat_bincoprod_swap b a $== cat_bincoprod_rec _ g f
  := cat_binprod_swap_corec (A:=A^op) _ _.

(** The swap map is a symmetric braiding.  Its two fields give the naturality and the involutivity of the swap map, which Products.v also states separately as [cat_binprod_swap_nat] and [cat_binprod_swap_cat_binprod_swap]. *)
Definition symmetricbraiding_bincoprod {A : Type} `{HasEquivs A}
  `{!HasBinaryCoproducts A}
  : SymmetricBraiding cat_bincoprod.
Proof.
  snapply symmetricbraiding_op'.
  1: exact _.
  exact symmetricbraiding_binprod.
Defined.

(** *** Associativity of coproducts *)

Instance associator_cat_bincoprod {A : Type} `{HasEquivs A}
  `{hbc : !HasBinaryCoproducts A}
  : Associator cat_bincoprod
  := associator_op' (bf0:=is0bifunctor_cat_bincoprod (hbc:=hbc))
      (assoc:=associator_cat_binprod (A:=A^op)).

Definition cat_bincoprod_rec_associator {A : Type} `{HasEquivs A}
  {hbc : HasBinaryCoproducts A}
  {w x y z : A} (f : w $-> z) (g : x $-> z) (h : y $-> z)
  : cat_bincoprod_rec _ (cat_bincoprod_rec _ f g) h $o associator_cat_bincoprod w x y
    $== cat_bincoprod_rec _ f (cat_bincoprod_rec _ g h).
Proof.
  napply cate_moveR_eV.
  symmetry.
  exact (cat_binprod_associator_corec (A:=A^op) (hbp:=hbc) f g h).
Defined.

(** *** Cocartesian Monoidal Structure *)

(** If [A] has binary coproducts and an initial object, then these form a symmetric monoidal structure.  Other things follow from this via typeclass search. *)
Instance issymmetricmonoidal_cat_bincoprod {A : Type} `{HasEquivs A}
  `{!HasBinaryCoproducts A} (zero : A) `{!IsInitial zero}
  : IsSymmetricMonoidal A cat_bincoprod zero | 10.
Proof.
  napply issymmetricmonoidal_op'.
  napply (issymmetricmonoidal_cat_binprod (A:=A^op) zero).
  by napply isterminal_op_isinitial.
Defined.

(** ** Examples *)

(** *** Coproducts in Type *)

(** [Type] has all coproducts. *)
Instance hasallcoproducts_type : HasAllCoproducts Type.
Proof.
  intros I x.
  snapply Build_Coproduct.
  - exact (sig (fun i : I => x i)).
  - exact (exist x).
  - intros A f [i xi].
    exact (f i xi).
  - intros A f i xi; reflexivity.
  - intros A f g p [i xi].
    exact (p i xi).
Defined.

(** In particular, [Type] has all binary coproducts. *)
Instance hasbinarycoproducts_type : HasBinaryCoproducts Type
  := {}.

(** ** Canonical coproduct-product map *)

(** There is a canonical map from a coproduct to a product when the indexing set has decidable equality and the category is pointed.  We factor out the components of this map into a separate definition to make goals involving [cat_coprod_prod] easier to read. *)
Definition cat_coprod_prod_component {A : Type} `{IsPointedCat A}
  {I : Type} `{DecidablePaths I}
  (x : I -> A) (i j : I)
  : x i $-> x j.
Proof.
  destruct (dec_paths i j) as [p|].
  - destruct p.
    exact (Id _).
  - exact zero_morphism.
Defined.

Definition cat_coprod_prod {A : Type} `{Is1Cat A, !IsPointedCat A}
  {I : Type} `{DecidablePaths I}
  (x : I -> A) (cat_coprod cat_prod : A)
  `{!IsCoproduct x cat_coprod, !IsProduct x cat_prod}
  : cat_coprod $-> cat_prod.
  Proof.
  rapply cat_coprod_rec.
  intros i.
  rapply cat_prod_corec.
  intros j.
  exact (cat_coprod_prod_component x i j).
Defined.

Definition cat_bincoprod_binprod {A : Type} `{Is1Cat A, !IsPointedCat A}
  (x y cat_bincoprod cat_binprod: A)
  `{!IsBinaryCoproduct x y cat_bincoprod, !IsBinaryProduct x y cat_binprod}
  : cat_bincoprod $-> cat_binprod.
Proof.
  napply cat_coprod_prod.
  1,2,4: exact _.
  rapply is_binary_coproduct.
Defined.
