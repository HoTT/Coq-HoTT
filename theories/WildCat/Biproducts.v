Require Import Basics.Overture Basics.Decidable Basics.Tactics Basics.Trunc Basics.Equivalences.
Require Import Types.Forall Types.Bool Types.Paths Types.Empty Types.Equiv Types.Sigma.
Require Import WildCat.Core WildCat.Products WildCat.Coproducts WildCat.Equiv.
Require Import WildCat.PointedCat WildCat.Bifunctor WildCat.Square WildCat.Forall.
Require Import WildCat.Opposite WildCat.Monoidal WildCat.MonoidalTwistConstruction.

(** * Categories with biproducts *)

(** ** Indexed biproducts *)

(** An object is a biproduct of a family if it is both a product and a coproduct of that family in a compatible way.  Other equivalent definitions are given as alternate constructions below.  Since the [IsProduct] and [IsCoproduct] fields are instances, you can use any results about products and coproducts from Products.v and Coproducts.v, so we do not duplicate all of those results here.  When both apply, use the results in Products.v, as the results in Coproducts.v are wrappers. Examples are the diagonal and codiagonal maps and the uniqueness of (co/bi)products. *)

Class IsBiproduct {A : Type} `{IsPointedCat A} {I : Type} `{DecidablePaths I}
  (x : I -> A) (cat_biprod : A)
  := Build_IsBiproduct' {
  isproduct_isbiproduct :: IsProduct x cat_biprod;
  iscoproduct_isbiproduct :: IsCoproduct x cat_biprod;
  cat_pr_in : forall i, cat_pr i $o cat_in i $== Id _;
  cat_pr_in_ne : forall i j, i <> j -> cat_pr j $o cat_in i $== zero_morphism;
}.

Arguments Build_IsBiproduct' {A _ _ _ _ _ I _} x cat_biprod.
Arguments isproduct_isbiproduct {A _ _ _ _ _ I _ x cat_biprod isbiprod} : rename.
Arguments iscoproduct_isbiproduct {A _ _ _ _ _ I _ x cat_biprod isbiprod} : rename.
Arguments cat_pr_in {A _ _ _ _ _ I _ x cat_biprod isbiprod} : rename.
Arguments cat_pr_in_ne {A _ _ _ _ _ I _ x cat_biprod isbiprod} : rename.

Class Biproduct {A : Type} `{IsPointedCat A} {I : Type} `{DecidablePaths I}
  (x : I -> A) := Build_Biproduct' {
    cat_biprod : A;
    cat_isbiprod :: IsBiproduct x cat_biprod;
}.

Arguments Build_Biproduct' {A _ _ _ _ _ I _} x cat_biprod cat_isbiprod.
Arguments cat_biprod {A _ _ _ _ _ I _} x {biproduct} : rename.
Arguments cat_isbiprod {A _ _ _ _ _ I _} x {biproduct} : rename.

Instance prod_biprod {A : Type} `{IsPointedCat A} {I : Type} `{DecidablePaths I}
  (x : I -> A) {biprod : Biproduct x}
  : Product x
  := Build_Product' x _ _.

Instance coprod_biprod {A : Type} `{IsPointedCat A} {I : Type} `{DecidablePaths I}
  (x : I -> A) {biprod : Biproduct x}
  : Coproduct x
  := Build_Coproduct' x _ _.

Section BiproductConstructors.

  Context {A : Type} `{IsPointedCat A} {I : Type}
    `{DecidablePaths I} (x : I -> A)
    (cat_biprod : A)
    (** A biproduct is a product. *)
    (cat_pr : forall i : I, cat_biprod $-> x i)
    (corec : forall z : A, (forall i : I, z $-> x i) -> (z $-> cat_biprod))
    (corec_beta : forall (z : A) (f : forall i, z $-> x i) (i : I),
      cat_pr i $o corec z f $== f i)
    (corec_eta : forall (z : A) (f g : z $-> cat_biprod),
      (forall i : I, cat_pr i $o f $== cat_pr i $o g) -> f $== g)
    (** A biproduct is a coproduct. *)
    (cat_in : forall i : I, x i $-> cat_biprod)
    (rec : forall z : A, (forall i : I, x i $-> z) -> (cat_biprod $-> z))
    (rec_beta : forall (z : A) (f : forall i, x i $-> z) (i : I),
      rec z f $o cat_in i $== f i)
    (rec_eta : forall (z : A) (f g : cat_biprod $-> z),
      (forall i : I, f $o cat_in i $== g $o cat_in i) -> f $== g)
    (** The projections and inclusion maps satisfy some further properties. *)
    (cat_pr_in : forall i : I, cat_pr i $o cat_in i $== Id _)
    (cat_pr_in_ne : forall i j : I, i <> j -> cat_pr j $o cat_in i $== zero_morphism).

  (** A convenience wrapper for building [IsBiproduct]. *)
  Definition Build_IsBiproduct : IsBiproduct x cat_biprod.
  Proof.
    snapply Build_IsBiproduct'.
    - by napply Build_IsProduct.
    - by napply Build_IsCoproduct.
    - exact cat_pr_in.
    - exact cat_pr_in_ne.
  Defined.

  (** A convenience wrapper for building biproducts. *)
  Definition Build_Biproduct : Biproduct x
    := Build_Biproduct' x cat_biprod Build_IsBiproduct.

End BiproductConstructors.

(** Since [cat_biprod] is both a product and a coproduct there is an induced endomorphism on [cat_biprod].  We will show that this morphism is homotopic to the identity.  *)
Section Endomorphism.
  Context {A : Type} `{IsPointedCat A}
    {I : Type} `{DecidablePaths I}
    {x : I -> A} (cat_biprod : A) `{!IsBiproduct x cat_biprod}.

  Definition cat_biprod_endo : cat_biprod $-> cat_biprod
    := cat_coprod_prod x cat_biprod cat_biprod.

  Definition cat_biprod_endo_id : Id _ $== cat_biprod_endo.
  Proof.
    lhs_V' rapply cat_coprod_eta.
    apply cat_coprod_rec_eta; intro i.
    lhs' rapply cat_idl.
    lhs_V' rapply cat_prod_eta.
    apply cat_prod_corec_eta; intro j.
    unfold cat_coprod_prod_component;
    destruct (dec_paths i j) as [p|np]; cbn.
    - destruct p.
      exact (cat_pr_in i).
    - exact (cat_pr_in_ne i j np).
  Defined.

  #[export]
  Instance catie_biprod_endo `{!HasEquivs A} : CatIsEquiv cat_biprod_endo
    := catie_homotopic _ cat_biprod_endo_id.

End Endomorphism.

(** If [cat_biprod] is an object with both a product and coproduct structure, then it defines a biproduct whenever we have a homotopy [Id _ $== cat_coprod_prod x _ _].  *)
Section HomotopyConstructor.
  Context {A : Type} `{IsPointedCat A}
  {I : Type} `{DecidablePaths I} (x : I -> A)
  (cat_biprod : A) `{!IsProduct x cat_biprod, !IsCoproduct x cat_biprod}
  (h : Id cat_biprod $== cat_coprod_prod x cat_biprod cat_biprod).

  (** An inclusion followed by a projection has a computation law by the specified homotopy. *)
  Definition cat_hbiprod_pr_in (i j : I)
    : cat_pr j $o cat_in i $== cat_coprod_prod_component x i j.
  Proof.
    rhs_V' rapply cat_prod_beta.
    apply cat_postwhisker.
    rhs_V' rapply (cat_coprod_beta _ (fun _ => cat_prod_corec _ _)).
    lhs_V' apply cat_idl.
    by apply cat_prewhisker.
  Defined.

  (** An inclusion followed by a projection of the same index is the identity. *)
  Definition cat_hbiprod_pr_in_eq (i : I)
    : cat_pr i $o cat_in i $== Id _.
  Proof.
    refine (cat_hbiprod_pr_in i i $@ _).
    unfold cat_coprod_prod_component.
    generalize (dec_paths i i).
    by rapply decidablepaths_refl.
  Defined.

  (** An inclusion followed by a projection of a different index is zero. *)
  Definition cat_hbiprod_pr_in_ne (i j : I) (p : i <> j)
    : cat_pr j $o cat_in i $== zero_morphism.
  Proof.
    refine (cat_hbiprod_pr_in i j $@ _).
    unfold cat_coprod_prod_component.
    decidable_false (dec_paths i j) p.
    reflexivity.
  Defined.

  Definition Build_hIsBiproduct : IsBiproduct x cat_biprod.
  Proof.
    rapply Build_IsBiproduct'.
    - apply cat_hbiprod_pr_in_eq.
    - apply cat_hbiprod_pr_in_ne.
  Defined.

End HomotopyConstructor.

Definition Build_hBiproduct {A : Type} `{IsPointedCat A} {I : Type}
  `{DecidablePaths I} (x : I -> A)
  (cat_biprod : A) `{!IsProduct x cat_biprod, !IsCoproduct x cat_biprod}
  (h : Id cat_biprod $== cat_coprod_prod x cat_biprod cat_biprod)
  : Biproduct x.
Proof.
  snapply (Build_Biproduct' x cat_biprod).
  by rapply Build_hIsBiproduct.
Defined.

(** If the canonical map from the coproduct to the product of [x] is an equivalence, then the product has a biproduct structure. *)
Section EquivConstructor.

  Context {A : Type} `{HasEquivs A, !IsPointedCat A}
  {I : Type} `{DecidablePaths I} (x : I -> A)
  (cat_prod : A) `{!IsProduct x cat_prod}
  (cat_coprod : A) `{!IsCoproduct x cat_coprod}
  {e : CatIsEquiv (cat_coprod_prod x _ _)}.

  Definition cate_cat_coprod_prod : cat_coprod $<~> cat_prod
    := Build_CatEquiv (cat_coprod_prod x _ _).

  Local Instance coprod_cat_prod : IsCoproduct x cat_prod
    := cat_coprod_coprod_equiv _ cat_prod cate_cat_coprod_prod.

  (** Mapping out of the coproduct using the universal property for the coproduct commutes with the equivalence. *)
  Definition cat_coprod_coprod_equiv_comp {z : A} (f : forall i, x i $-> z)
    : cat_coprod_rec cat_prod f $o cate_cat_coprod_prod $== cat_coprod_rec cat_coprod f
    := compose_hV_h (cat_coprod_rec cat_coprod f) cate_cat_coprod_prod.

  Definition cat_biprod_pr_in (i j : I)
    : cat_pr j $o cat_in i $== cat_coprod_prod_component x i j.
  Proof.
    refine ((_ $@L _) $@ _).
    { refine (cat_in_comp _ _ _ _ $@ _).
    lhs' apply (cate_buildequiv_fun (cat_coprod_prod x _ _) $@R _).
    apply cat_coprod_beta. }
    apply cat_prod_beta.
  Defined.

  Definition cat_biprod_pr_in_eq (i : I)
    : cat_pr i $o cat_in i $== Id _.
  Proof.
    refine (cat_biprod_pr_in i i $@ _).
    unfold cat_coprod_prod_component.
    generalize (dec_paths i i).
    by rapply decidablepaths_refl.
  Defined.

  Definition cat_biprod_pr_in_ne (i j : I) (p : i <> j)
    : cat_pr j $o cat_in i $== zero_morphism.
  Proof.
    refine (cat_biprod_pr_in i j $@ _).
    unfold cat_coprod_prod_component.
    decidable_false (dec_paths i j) p.
    reflexivity.
  Defined.

  Definition Build_eIsBiproduct : IsBiproduct x cat_prod.
  Proof.
    srapply Build_IsBiproduct'.
    - apply cat_biprod_pr_in_eq.
    - apply cat_biprod_pr_in_ne.
  Defined.

End EquivConstructor.

Definition Build_eBiproduct {A : Type} `{HasEquivs A, !IsPointedCat A}
  {I : Type} `{DecidablePaths I} (x : I -> A)
  (cat_prod : A) `{!IsProduct x cat_prod}
  (cat_coprod : A) `{!IsCoproduct x cat_coprod}
  {e : CatIsEquiv (cat_coprod_prod x _ _)}
  : Biproduct x.
Proof.
  snapply (Build_Biproduct' x cat_prod).
  rapply Build_eIsBiproduct.
Defined.

(** Compatibility of [cat_biprod_rec] and [cat_prod_corec]. *)
Definition cat_biprod_corec_rec {A : Type} `{IsPointedCat A} {I : Type}
  `{DecidablePaths I}
  {x y : I -> A} (biprod_x biprod_y : A) `{!IsBiproduct x biprod_x, !IsBiproduct y biprod_y}
  (f : forall i, x i $-> y i)
  : cat_prod_corec biprod_y (fun i => f i $o cat_pr i)
    $== cat_coprod_rec biprod_x (fun i => cat_in i $o f i).
Proof.
  rapply cat_prod_pr_eta.
  intro i.
  refine (cat_prod_beta _ _ _ $@ _).
  tapply (cat_coprod_in_eta (x:=x)).
  intro j.
  refine (_ $@ (_ $@L (cat_coprod_beta _ _ _)^$) $@ cat_assoc_opp _ _ _).
  refine (cat_assoc _ _ _ $@ _ $@ cat_assoc _ _ _).
  (* This can probably be simplified by turning into components and proving some naturality statement. *)
  destruct (dec_paths j i) as [p | np].
  - destruct p.
    refine ((_ $@L _) $@ cat_idr _ $@ (cat_idl _)^$ $@ (_^$ $@R _)).
    1,2: napply cat_pr_in.
  - refine ((_ $@L _) $@ cat_zero_r _ $@ (cat_zero_l _)^$ $@ (_^$ $@R _)).
    1,2: napply cat_pr_in_ne; assumption.
Defined.

(** *** Existence of biproducts *)

Class HasBiproducts (A : Type) `{HasEquivs A, !IsPointedCat A}
  (I : Type) `{DecidablePaths I}
  := has_biproducts :: forall (x : I -> A), Biproduct x.

Instance hasproducts_hasbiproducts {A I : Type} `{HasBiproducts A I}
  : HasProducts A I
  := fun x => prod_biprod x.

Instance hascoproducts_hasbiproducts {A I : Type} `{HasBiproducts A I}
  : HasCoproducts A I
  := fun x => coprod_biprod x.

(** *** Biproduct functor *)

Instance is0functor_cat_biprod (A I : Type) `{HasBiproducts A I}
  : Is0Functor (fun x : I -> A => cat_biprod x)
  := is0functor_cat_prod A I.

Instance is1functor_cat_biprod (A I : Type) `{HasBiproducts A I}
  : Is1Functor (fun x : I -> A => cat_biprod x)
  := is1functor_cat_prod A I.

(** *** An empty biproduct is a zero object *)

(** An empty biproduct is terminal by [isterminal_prod_empty], so it is equivalent to the zero object. (It is also initial by [isinitial_coprod_empty].) *)
Definition cate_biprod_empty_zero {A : Type} `{HasEquivs A, !IsPointedCat A}
  {x : Empty -> A} {biprod_empty : A} `{!IsBiproduct x biprod_empty}
  : biprod_empty $<~> zero_object
  := cate_isterminal A _ _ isterminal_zero_object isterminal_prod_empty.

(** ** Binary biproducts *)

Class IsBinaryBiproduct {A : Type} `{IsPointedCat A} (x y cat_binbiprod : A)
  := is_binary_biproduct :: IsBiproduct (Bool_rec _ x y) cat_binbiprod.

Instance isbinaryprod_isbinarybiprod {A : Type} `{IsPointedCat A}
  (x y cat_binbiprod : A) `{!IsBinaryBiproduct x y cat_binbiprod}
  : IsBinaryProduct x y cat_binbiprod
  := isproduct_isbiproduct.

Instance isbinarycoprod_isbinarybiprod {A : Type} `{IsPointedCat A}
  (x y cat_binbiprod : A) `{bip : !IsBinaryBiproduct x y cat_binbiprod}
  : IsBinaryCoproduct x y cat_binbiprod
  := iscoproduct_isbiproduct (isbiprod := bip).

Class BinaryBiproduct {A : Type} `{IsPointedCat A} (x y : A)
  := binary_biproduct :: Biproduct (Bool_rec _ x y).

Instance isbinbiprod_binbiprod {A : Type} `{IsPointedCat A}
  (x y : A) {binbiprod : BinaryBiproduct x y}
  : IsBinaryBiproduct x y _
  := cat_isbiprod _.

Instance binprod_binbiprod {A : Type} `{IsPointedCat A}
  (x y : A) {binbiprod : BinaryBiproduct x y}
  : BinaryProduct x y
  := Build_Product' _ _ _.

Instance bincoprod_binbiprod {A : Type} `{IsPointedCat A}
  (x y : A) {binbiprod : BinaryBiproduct x y}
  : BinaryCoproduct x y
  := Build_Coproduct' _ _ (isbinarycoprod_isbinarybiprod x y _).

Definition Build_eBinaryBiproduct {A : Type} `{HasEquivs A, !IsPointedCat A}
  {x y : A} {p : BinaryProduct x y} {c : BinaryCoproduct x y}
  {ie : CatIsEquiv (cat_bincoprod_binprod x y c.(cat_prod _) p.(cat_prod _))}
  : BinaryBiproduct x y
  := Build_eBiproduct _ _ _ (e:=ie).

Section BinaryBiproductConstructors.

  Context {A : Type} `{IsPointedCat A}
    {x y : A} (cat_binbiprod : A)
    (** A binary biproduct is a product. *)
    (cat_pr1 : cat_binbiprod $-> x) (cat_pr2 : cat_binbiprod $-> y)
    (corec : forall z : A, (z $-> x) -> (z $-> y) -> (z $-> cat_binbiprod))
    (corec_beta_pr1 : forall (z : A) (f : z $-> x) (g : z $-> y),
      cat_pr1 $o corec z f g $== f)
    (corec_beta_pr2 : forall (z : A) (f : z $-> x) (g : z $-> y),
      cat_pr2 $o corec z f g $== g)
    (corec_eta : forall (z : A) (f g : z $-> cat_binbiprod),
      cat_pr1 $o f $== cat_pr1 $o g -> cat_pr2 $o f $== cat_pr2 $o g -> f $== g)
    (** A binary biproduct is a coproduct. *)
    (cat_inl : x $-> cat_binbiprod) (cat_inr : y $-> cat_binbiprod)
    (rec : forall z : A, (x $-> z) -> (y $-> z) -> (cat_binbiprod $-> z))
    (rec_beta_inl : forall (z : A) (f : x $-> z) (g : y $-> z),
      rec z f g $o cat_inl $== f)
    (rec_beta_inr : forall (z : A) (f : x $-> z) (g : y $-> z),
      rec z f g $o cat_inr $== g)
    (rec_eta : forall (z : A) (f g : cat_binbiprod $-> z),
      f $o cat_inl $== g $o cat_inl -> f $o cat_inr $== g $o cat_inr -> f $== g)
    (** The projections and inclusion maps satisfy some further properties. *)
    (cat_pr1_inl : cat_pr1 $o cat_inl $== Id _)
    (cat_pr2_inr : cat_pr2 $o cat_inr $== Id _)
    (cat_pr1_inr : cat_pr1 $o cat_inr $== zero_morphism)
    (cat_pr2_inl : cat_pr2 $o cat_inl $== zero_morphism).

  (** A convenience wrapper for building [IsBinaryBiproduct]. *)
  Definition Build_IsBinaryBiproduct
    : IsBinaryBiproduct x y cat_binbiprod.
  Proof.
    snapply (Build_IsBiproduct _ cat_binbiprod).
    - intros [ | ].
      + exact cat_pr1.
      + exact cat_pr2.
    - intros z f.
      exact (corec z (f true) (f false)).
    - intros z f [ | ].
      + exact (corec_beta_pr1 z (f true) (f false)).
      + exact (corec_beta_pr2 z (f true) (f false)).
    - intros z f g p.
      exact (corec_eta z _ _ (p true) (p false)).
    - intros [ | ].
      + exact cat_inl.
      + exact cat_inr.
    - intros z f.
      exact (rec z (f true) (f false)).
    - intros z f [ | ].
      + exact (rec_beta_inl z (f true) (f false)).
      + exact (rec_beta_inr z (f true) (f false)).
    - intros z f g p.
      exact (rec_eta z _ _ (p true) (p false)).
    - intros [ | ].
      + exact cat_pr1_inl.
      + exact cat_pr2_inr.
    - intros i j ne.
      destruct (negb_ne' ne), i as [ | ].
      + exact cat_pr2_inl.
      + exact cat_pr1_inr.
  Defined.

  (** Smart constructor for binary biproducts. *)
  Definition Build_BinaryBiproduct : BinaryBiproduct x y
    := Build_Biproduct' _ cat_binbiprod Build_IsBinaryBiproduct.

End BinaryBiproductConstructors.

Class HasBinaryBiproducts (A : Type) `{IsPointedCat A}
  := has_binary_biproducts :: forall (x y : A), BinaryBiproduct x y.

Instance hasbinarybiproducts_hasbiproductsbool {A : Type}
  `{HasEquivs A, !IsPointedCat A, !HasBiproducts A Bool}
  : HasBinaryBiproducts A
  := fun x y => has_biproducts (Bool_rec _ x y).

Instance hasbinaryproducts_hasbinarybiproducts {A : Type}
  `{HasBinaryBiproducts A}
  : HasBinaryProducts A
  := fun x y => binprod_binbiprod x y.

Instance hasbinarycoproducts_hasbinarybiproducts {A : Type}
  `{HasBinaryBiproducts A}
  : HasBinaryCoproducts A
  := fun x y => bincoprod_binbiprod x y.

Section BinaryBiproducts.

  Context {A : Type} `{IsPointedCat A} {x y : A}
    (cat_binbiprod : A) {isbinbiprod : IsBinaryBiproduct x y cat_binbiprod}.

  Definition cat_binbiprod_corec_zero_inl {z} (f : z $-> x)
    : cat_binprod_corec _ f zero_morphism $== cat_inl _ $o f.
  Proof.
    napply cat_binprod_eta_pr.
    - refine (cat_binprod_beta_pr1 _ _ _ $@ _^$).
      exact ((cat_assoc _ _ _)^$ $@ (cat_pr_in _ $@R _) $@ cat_idl _).
    - refine (cat_binprod_beta_pr2 _ _ _ $@ _^$).
      exact ((cat_assoc _ _ _)^$ $@ (cat_pr_in_ne _ _ (not_fixed_negb _) $@R _) $@ cat_zero_l _).
  Defined.

  Definition cat_binbiprod_corec_zero_inr {z} (f : z $-> y)
    : cat_binprod_corec _ zero_morphism f $== cat_inr _ $o f.
  Proof.
    napply cat_binprod_eta_pr.
    - refine (cat_binprod_beta_pr1 _ _ _ $@ _^$).
      exact ((cat_assoc _ _ _)^$ $@ (cat_pr_in_ne _ _ (not_fixed_negb _) $@R _) $@ cat_zero_l _).
    - refine (cat_binprod_beta_pr2 _ _ _ $@ _^$).
      exact ((cat_assoc _ _ _)^$ $@ (cat_pr_in _ $@R _) $@ cat_idl _).
  Defined.

End BinaryBiproducts.

(** Compatibility of [cat_binprod_rec] and [cat_binprod_corec]. *)
Definition cat_binbiprod_corec_rec {A : Type} `{IsPointedCat A}
  {w x y z cat_binbiprod_w_x cat_binbiprod_y_z : A}
  `{!IsBinaryBiproduct w x cat_binbiprod_w_x}
  `{!IsBinaryBiproduct y z cat_binbiprod_y_z}
  (f : w $-> y) (g : x $-> z)
  : cat_binprod_corec _ (f $o cat_pr1 _) (g $o cat_pr2 _)
    $== cat_bincoprod_rec _ (cat_inl _ $o f) (cat_inr _ $o g).
Proof.
  unfold cat_binprod_corec, cat_bincoprod_rec.
  refine (_ $@ _ $@ _).
  2: rapply (cat_biprod_corec_rec cat_binbiprod_w_x cat_binbiprod_y_z).
  2: by intros [|].
  1: snapply cat_prod_corec_eta; by intros [|].
  snapply cat_coprod_rec_eta; by intros [|].
Defined.

Definition cat_binbiprod {A : Type} `{HasBinaryBiproducts A} (x y : A) : A
  := (has_binary_biproducts x y).(cat_biprod _).

(** *** Binary biproduct bifunctor *)

Instance is0bifunctor_cat_binbiprod {A : Type}
  `{HasBinaryBiproducts A}
  : Is0Bifunctor cat_binbiprod
  := is0bifunctor_cat_binprod.

Instance is1bifunctor_cat_binbiprod {A : Type}
  `{HasBinaryBiproducts A}
  : Is1Bifunctor cat_binbiprod
  := is1bifunctor_cat_binprod.

(** *** Symmetry *)

Section Symmetry.
  Context {A : Type} `{HasBinaryBiproducts A}.

  Local Instance symmetricbraiding_binbiprod
    : SymmetricBraiding cat_binbiprod
    := symmetricbraiding_binprod.

  Definition cat_binprod_swap_inl (x y : A)
    : cat_binprod_swap x y $o cat_inl _
      $== cat_inr _.
  Proof.
    napply cat_binprod_eta_pr.
    - refine ((cat_assoc _ _ _)^$ $@ _).
      refine ((_ $@R _) $@ _).
      1: napply cat_binprod_beta_pr1.
      refine (_ $@ _^$).
      all: napply (cat_pr_in_ne _ _ (not_fixed_negb _)).
    - refine ((cat_assoc _ _ _)^$ $@ _).
      refine ((_ $@R _) $@ _).
      1: napply cat_binprod_beta_pr2.
      refine (_ $@ _^$).
      all: napply cat_pr_in.
  Defined.

  Definition cat_binprod_swap_inr (x y : A)
    : cat_binprod_swap x y $o cat_inr _
      $== cat_inl _.
  Proof.
    napply cat_binprod_eta_pr.
    - refine ((cat_assoc _ _ _)^$ $@ _).
      refine ((_ $@R _) $@ _).
      1: napply cat_binprod_beta_pr1.
      refine (_ $@ _^$).
      all: napply cat_pr_in.
    - refine ((cat_assoc _ _ _)^$ $@ _).
      refine ((_ $@R _) $@ _).
      1: napply cat_binprod_beta_pr2.
      refine (_ $@ _^$).
      all: napply (cat_pr_in_ne _ _ (not_fixed_negb _)).
  Defined.

  Definition cat_binprod_swap_eq_cat_bincoprod_swap (x y : A)
    : cat_binprod_swap x y $== cat_bincoprod_swap x y.
  Proof.
    napply cat_bincoprod_eta_in.
    - refine (cat_binprod_swap_inl x y $@ _).
      symmetry.
      napply cat_bincoprod_beta_inl.
    - refine (cat_binprod_swap_inr x y $@ _).
      symmetry.
      napply cat_bincoprod_beta_inr.
  Defined.

End Symmetry.

(** *** Associativity of binary biproducts *)

Section Associativity.

  Context {A : Type} `{HasBinaryBiproducts A, !HasEquivs A}.

  Definition cat_binprod_twist_inl (x y z : A)
    : cat_binprod_twist x y z $o cat_inl _
      $== cat_inr _ $o cat_inl _.
  Proof.
    napply cat_binprod_eta_pr.
    - refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      1: napply cat_binprod_beta_pr1.
      refine (cat_assoc _ _ _ $@ _ $@ cat_assoc _ _ _).
      refine ((_ $@L _) $@ _ $@ (_^$ $@R _)).
      1,3: napply (cat_pr_in_ne _ _ (not_fixed_negb _)).
      refine (_ $@ _^$).
      1: napply cat_zero_r.
      napply cat_zero_l.
    - refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      1: napply cat_binprod_beta_pr2.
      refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ _).
      refine (cat_bincoprod_beta_inl _ _ _ $@ cat_idr _ $@ _).
      refine ((cat_idl _)^$ $@ (_^$ $@R _) $@ cat_assoc _ _ _).
      exact (cat_pr_in false).
  Defined.

  Definition cat_binprod_twist_inr_inl (x y z : A)
    : cat_binprod_twist x y z $o cat_inr _ $o cat_inl _
      $== cat_inl _.
  Proof.
    napply cat_binprod_eta_pr.
    - refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _)).
        1: napply cat_binprod_beta_pr1. }
      refine (cat_assoc _ _ _ $@ _).
      refine (cat_assoc _ _ _ $@ _).
      refine ((_ $@L _) $@ _).
      { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
        1: exact (cat_pr_in false).
        napply cat_idl. }
      refine (_ $@ _^$).
      all: napply cat_pr_in.
    - refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _)).
        1: napply cat_binprod_beta_pr2. }
      refine (cat_assoc _ _ _ $@ (_ $@R _) $@ _).
      1: rapply cat_binbiprod_corec_rec.
      refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      1: napply cat_bincoprod_beta_inr.
      refine (cat_assoc _ _ _ $@ (_ $@L _) $@ _).
      1: exact (cat_pr_in_ne _ _ (not_fixed_negb _)).
      refine (_ $@ _^$).
      1: napply cat_zero_r.
      exact (cat_pr_in_ne _ _ (not_fixed_negb _)).
  Defined.

  Definition cat_binprod_twist_inr_inr (x y z : A)
    : cat_binprod_twist x y z $o cat_inr _ $o cat_inr _
      $== cat_inr _ $o cat_inr _.
  Proof.
    napply cat_binprod_eta_pr.
    - refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _)).
        1: napply cat_binprod_beta_pr1. }
      refine (cat_assoc _ _ _ $@ _).
      refine (cat_assoc _ _ _ $@ _).
      refine ((_ $@L _) $@ _).
      { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
        1: exact (cat_pr_in false).
        napply cat_idl. }
      refine (_ $@ _^$).
      1: exact (cat_pr_in_ne _ _ (not_fixed_negb _)).
      refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      1: exact (cat_pr_in_ne _ _ (not_fixed_negb _)).
      napply cat_zero_l.
    - refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _)).
        1: napply cat_binprod_beta_pr2. }
      refine (cat_assoc _ _ _ $@ (_ $@R _) $@ _).
      1: rapply cat_binbiprod_corec_rec.
      refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      1: napply cat_bincoprod_beta_inr.
      refine (cat_assoc _ _ _ $@ (_ $@L _) $@ _).
      1: napply cat_pr_in.
      refine (cat_idr _ $@ _^$).
      refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      1: exact (cat_pr_in false).
      napply cat_idl.
  Defined.

  Definition associator_cat_binprod_inl (x y z : A)
    : associator_cat_binprod x y z $o cat_inl _
      $== cat_inl _ $o cat_inl _.
  Proof.
    refine ((_ $@R _) $@ _).
    1: rapply associator_twist'_unfold.
    refine (cat_assoc _ _ _ $@ _).
    refine ((_ $@L (cat_assoc _ _ _ $@ (_ $@L _))) $@ _).
    { refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ (_ $@ _)).
      1: napply cat_bincoprod_beta_inl.
      napply cat_idr. }
    refine ((_ $@L _) $@ _).
    1: napply cat_binprod_twist_inl.
    refine (cat_assoc_opp _ _ _ $@ _).
    refine (_ $@R _).
    napply cat_binprod_swap_inr.
  Defined.

  Definition associator_cat_binprod_inr_inl (x y z : A)
    : associator_cat_binprod x y z $o cat_inr _ $o cat_inl _
      $== cat_inl _ $o cat_inr _.
  Proof.
    refine (((_ $@R _) $@R _) $@ _).
    1: napply associator_twist'_unfold.
    refine (cat_assoc _ _ _ $@ _).
    refine (cat_assoc _ _ _ $@ _).
    refine ((_ $@L (cat_assoc _ _ _ $@ (_ $@L _))) $@ _).
    { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _)).
      refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ _).
      napply cat_bincoprod_beta_inr. }
    refine ((_ $@L _) $@ _).
    { refine ((cat_assoc _ _ _)^$ $@ _).
      refine (((cat_assoc _ _ _)^$ $@R _) $@ _).
      refine (cat_assoc _ _ _ $@ _).
      refine ((_ $@L _) $@ _).
      1: napply cat_binprod_swap_inl.
      napply cat_binprod_twist_inr_inr. }
    refine ((cat_assoc _ _ _)^$ $@ (_ $@R _)).
    napply cat_binprod_swap_inr.
  Defined.

  Definition associator_cat_binprod_inr_inr (x y z : A)
    : associator_cat_binprod x y z $o cat_inr _ $o cat_inr _
      $== cat_inr _.
  Proof.
    refine (((_ $@R _) $@R _) $@ _).
    1: napply associator_twist'_unfold.
    refine (cat_assoc _ _ _ $@ _).
    refine (cat_assoc _ _ _ $@ _).
    refine ((_ $@L (cat_assoc _ _ _ $@ (_ $@L _))) $@ _).
    { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _)).
      refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ _).
      napply cat_bincoprod_beta_inr. }
    refine ((_ $@L _) $@ _).
    { refine ((cat_assoc _ _ _)^$ $@ _).
      refine (((cat_assoc _ _ _)^$ $@R _) $@ _).
      refine (cat_assoc _ _ _ $@ _).
      refine ((_ $@L _) $@ _).
      1: napply cat_binprod_swap_inr.
      napply cat_binprod_twist_inr_inl. }
    napply cat_binprod_swap_inl.
  Defined.

  (** If [A] is pointed and has binary biproducts, then these form a symmetric monoidal structure.  Other things follow from this via typeclass search. *)
  #[export] Instance issymmetricmonoidal_cat_binbiprod
    : IsSymmetricMonoidal A cat_binbiprod zero_object
    := issymmetricmonoidal_cat_binprod zero_object.

End Associativity.

(** ** Biproducts in the opposite category *)

(** Biproducts exist in the opposite category if they exist in the original category. *)
Instance biproduct_op {A I : Type} {x : I -> A} `{biprod : Biproduct A I x}
  : Biproduct (A:=A^op) x.
Proof.
  napply (Build_Biproduct' (A:=A^op) x (cat_biprod (biproduct:=biprod) x)).
  srapply Build_IsBiproduct'.
  - napply cat_pr_in.
  - intros i j n.
    napply cat_pr_in_ne.
    exact (fun q => n q^).
Defined.

Instance hasbiproducts_op {A I : Type}
  `{HasEquivs A, !IsPointedCat A, DecidablePaths I, !HasBiproducts A I}
  : HasBiproducts (A^op) I.
Proof.
  intros x.
  by napply biproduct_op.
Defined.

Instance binarybiproduct_op {A : Type}
  `{HasEquivs A, !IsPointedCat A} {x y : A} {bb : BinaryBiproduct x y}
  : BinaryBiproduct (A:=A^op) x y.
Proof.
  napply biproduct_op.
  exact bb.
Defined.

Instance hasbinarybiproducts_op {A : Type}
  `{HasEquivs A, !IsPointedCat A} {hbb : HasBinaryBiproducts A}
  : HasBinaryBiproducts (A^op).
Proof.
  intros x y.
  napply biproduct_op.
  exact (hbb x y).
Defined.
