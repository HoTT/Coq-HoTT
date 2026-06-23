Require Import Basics.Overture Basics.Decidable Basics.Tactics Basics.Trunc Basics.Equivalences.
Require Import Types.Forall Types.Bool Types.Paths Types.Empty Types.Equiv Types.Sigma.
Require Import WildCat.Core WildCat.Products WildCat.Coproducts WildCat.Equiv.
Require Import WildCat.PointedCat WildCat.Bifunctor WildCat.Square.
Require Import WildCat.Opposite WildCat.Monoidal WildCat.MonoidalTwistConstruction.

(** * Categories with biproducts *)

(** ** Biproducts *)

Class IsBiproduct (I : Type) `{DecidablePaths I} {A : Type}
  `{IsPointedCat A} {x : I -> A} (cat_biprod : A)
  := Build_IsBiproduct' {
  isproduct_isbiproduct :: IsProduct I x cat_biprod;
  iscoproduct_isbiproduct :: IsCoproduct I x cat_biprod;
  cat_pr_in : forall i, cat_pr _ _ i $o cat_in _ _ i $== Id _;
  cat_pr_in_ne : forall i j, i <> j -> cat_pr _ _ j $o cat_in _ _ i $== zero_morphism;
}.

Arguments IsBiproduct I {_ A _ _ _ _ _} x cat_biprod.
Arguments Build_IsBiproduct' I {_ A _ _ _ _ _} x _ _ _.

(** An (un)curried constructor for biproducts. *)
Definition Build_IsBiproduct (I : Type) `{DecidablePaths I}
  {A : Type} `{IsPointedCat A} (x : I -> A)
  (cat_biprod : A)
  (** A biproduct is a product. *)
  (cat_pr : forall i, cat_biprod $-> x i)
  (corec : forall z, (forall i, z $-> x i) -> z $-> cat_biprod)
  (corec_beta : forall z f i, cat_pr i $o corec z f $== f i)
  (corec_eta : forall z (f g : z $-> cat_biprod),
    (forall i, cat_pr i $o f $== cat_pr i $o g) -> f $== g)
  (** A biproduct is a coproduct. *)
  (cat_in : forall i, x i $-> cat_biprod)
  (rec : forall z, (forall i, x i $-> z) -> cat_biprod $-> z)
  (rec_beta : forall z f i, rec z f $o cat_in i $== f i)
  (rec_eta : forall z (f g : cat_biprod $-> z),
    (forall i, f $o cat_in i $== g $o cat_in i) -> f $== g)
  (** The projections and inclusion maps satisfy some further properties. *)
  (cat_pr_in : forall i, cat_pr i $o cat_in i $== Id _)
  (cat_pr_in_ne : forall i j, i <> j -> cat_pr j $o cat_in i $== zero_morphism)
  : IsBiproduct I x cat_biprod.
Proof.
  snapply Build_IsBiproduct'.
  - by napply Build_IsProduct.
  - by napply Build_IsCoproduct.
  - exact cat_pr_in.
  - exact cat_pr_in_ne.
Defined.

(** Since [cat_biprod] is both a product and a coproduct there is an induced endomorphism on [cat_biprod].  We will show that this morphism is homotopic to the identity.  *)
Section Induced.
  Context (I : Type) `{DecidablePaths I}
  {A : Type} `{IsPointedCat A}
  {x : I -> A} (cat_biprod : A) `{!IsBiproduct I x cat_biprod}.

  Definition induced_isbiproduct : cat_biprod $-> cat_biprod
  := cat_coprod_prod x cat_biprod cat_biprod.

  Definition homotopic_induced_isbiproduct : Id _ $== induced_isbiproduct.
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
  Instance catie_induced_isbiproduct `{!HasEquivs A} : CatIsEquiv induced_isbiproduct
    := catie_homotopic _ homotopic_induced_isbiproduct.

End Induced.

(** Compatability of [cat_biprod_rec] and [cat_prod_corec]. *)
Definition cat_biprod_corec_rec I `{DecidablePaths I} {A : Type} `{IsPointedCat A}
  {x y : I -> A} (biprod_x biprod_y : A) `{!IsBiproduct I x biprod_x, !IsBiproduct I y biprod_y}
  (f : forall i, x i $-> y i)
  : cat_prod_corec biprod_y (fun i => f i $o cat_pr _ _ i)
    $== cat_coprod_rec _ biprod_x (fun i => cat_in _ _ i $o f i).
Proof.
  rapply cat_prod_pr_eta.
  intro i.
  refine (cat_prod_beta _ _ _ $@ _).
  tapply (cat_coprod_in_eta (x:=x) I).
  intro j.
  refine (_ $@ (_ $@L (cat_coprod_beta _ _ _ _)^$) $@ cat_assoc_opp _ _ _).
  refine (cat_assoc _ _ _ $@ _ $@ cat_assoc _ _ _).
  (* This can probably be simplified by turning into components and proving some naturality statement. *)
  destruct (dec_paths j i) as [p | np].
  - destruct p.
    refine ((_ $@L _) $@ cat_idr _ $@ (cat_idl _)^$ $@ (_^$ $@R _)).
    1,2: napply cat_pr_in.
  - refine ((_ $@L _) $@ cat_zero_r _ $@ (cat_zero_l _)^$ $@ (_^$ $@R _)).
    1,2: napply cat_pr_in_ne; assumption.
Defined.

(** If [cat_biprod] is an object with both a product and coproduct structure, then it defines a biproduct whenever we have a homotopy [Id _ $== cat_coprod_prod x _ _].  *)
Section HomotopyConstructor.
  Context (I : Type) `{DecidablePaths I}
  {A : Type} `{IsPointedCat A} (x : I -> A)
  (cat_biprod : A) `{!IsProduct I x cat_biprod, !IsCoproduct I x cat_biprod}
  (h : Id cat_biprod $== cat_coprod_prod x cat_biprod cat_biprod).

  (** An inclusion followed by a projection has a computation law by the specified homotopy. *)
  Definition cat_hbiprod_pr_in (i j : I)
    : cat_pr _ _ j $o cat_in _ _ i $== cat_coprod_prod_component x i j.
  Proof.
    rhs_V' rapply cat_prod_beta.
    apply cat_postwhisker.
    rhs_V' rapply (cat_coprod_beta _ _ (fun _ => cat_prod_corec _ _)).
    lhs_V' apply cat_idl.
    by apply cat_prewhisker.
  Defined.

  (** An inclusion followed by a projection of the same index is the identity. *)
  Definition cat_hbiprod_pr_in_eq (i : I)
    : cat_pr _ _ i $o cat_in _ _ i $== Id _.
  Proof.
    refine (cat_hbiprod_pr_in i i $@ _).
    unfold cat_coprod_prod_component.
    generalize (dec_paths i i).
    by napply decidable_paths_refl.
  Defined.

  (** An inclusion followed by a projection of a different index is zero. *)
  Definition cat_hbiprod_pr_in_ne (i j : I) (p : i <> j)
    : cat_pr _ _ j $o cat_in _ _ i $== zero_morphism.
  Proof.
    refine (cat_hbiprod_pr_in i j $@ _).
    unfold cat_coprod_prod_component.
    decidable_false (dec_paths i j) p.
    reflexivity.
  Defined.

  Definition Build_hIsBiproduct : IsBiproduct I x cat_biprod.
  Proof.
    rapply Build_IsBiproduct'.
    - apply cat_hbiprod_pr_in_eq.
    - apply cat_hbiprod_pr_in_ne.
  Defined.

End HomotopyConstructor.

(** If the canonical map from the coproduct to the product of [x] is an equivalence, then the product has a biproduct structure. *)
Section EquivConstructor.

  Context (I : Type) `{DecidablePaths I}
  {A : Type} `{HasEquivs A, !IsPointedCat A} (x : I -> A)
  (cat_prod : A) `{!IsProduct I x cat_prod}
  (cat_coprod : A) `{!IsCoproduct I x cat_coprod}
  {e : CatIsEquiv (cat_coprod_prod x _ _)}.

  Definition cate_cat_coprod_prod : cat_coprod $<~> cat_prod
    := Build_CatEquiv (cat_coprod_prod x _ _).

  (** We only want this instance locally. *)
  Instance coprod_cat_prod : IsCoproduct I x cat_prod
    := cat_coprod_coprod_equiv _ _ cat_prod cate_cat_coprod_prod.

  (** Mapping out of the coproduct using the universal property for the coproduct commutes with the equivalence *)
  Definition cat_coprod_coprod_equiv_comp {z : A} (f : forall i, x i $-> z)
    : cat_coprod_rec _ cat_prod f $o cate_cat_coprod_prod $== cat_coprod_rec _ cat_coprod f
    := compose_hV_h (cat_coprod_rec I cat_coprod f) cate_cat_coprod_prod.

  Definition cat_biprod_pr_in (i j : I)
    : cat_pr _ _ j $o cat_in _ _ i $== cat_coprod_prod_component x i j.
  Proof.
    refine ((_ $@L _) $@ _).
    { refine (cat_in_comp _ _ _ _ _ $@ _).
    lhs' apply (cate_buildequiv_fun (cat_coprod_prod x _ _) $@R _).
    apply cat_coprod_beta. }
    apply cat_prod_beta.
  Defined.

  Definition cat_biprod_pr_in_eq (i : I)
    : cat_pr _ _ i $o cat_in _ _ i $== Id _.
  Proof.
    refine (cat_biprod_pr_in i i $@ _).
    unfold cat_coprod_prod_component.
    generalize (dec_paths i i).
    by napply decidable_paths_refl.
  Defined.

  Definition cat_biprod_pr_in_ne (i j : I) (p : i <> j)
    : cat_pr _ _ j $o cat_in _ _ i $== zero_morphism.
  Proof.
    refine (cat_biprod_pr_in i j $@ _).
    unfold cat_coprod_prod_component.
    decidable_false (dec_paths i j) p.
    reflexivity.
  Defined.

  Definition Build_IsBiproduct'' : IsBiproduct I x cat_prod.
  Proof.
    srapply Build_IsBiproduct'.
    - apply cat_biprod_pr_in_eq.
    - apply cat_biprod_pr_in_ne.
  Defined.

End EquivConstructor.

Class Biproduct (I : Type) `{DecidablePaths I} {A : Type}
  `{IsPointedCat A} (x : I -> A) := Build_Biproduct' {
    cat_biprod : A;
    cat_isbiprod :: IsBiproduct I x cat_biprod;
}.

Arguments Build_Biproduct' I {_} _ {_ _ _ _ _} x cat_biprod cat_isbiprod.
Arguments cat_biprod I {_ _ _ _ _ _ _} x.
Arguments cat_isbiprod I {_ _ _ _ _ _ _} x.

Definition Build_Biproduct (I : Type) `{DecidablePaths I}
  {A : Type} `{IsPointedCat A} (x : I -> A)
  (cat_biprod : A)
  (** A biproduct is a product. *)
  (cat_pr : forall i, cat_biprod $-> x i)
  (corec : forall z, (forall i, z $-> x i) -> z $-> cat_biprod)
  (corec_beta : forall z f i, cat_pr i $o corec z f $== f i)
  (corec_eta : forall z (f g : z $-> cat_biprod),
    (forall i, cat_pr i $o f $== cat_pr i $o g) -> f $== g)
  (** A biproduct is a coproduct. *)
  (cat_in : forall i, x i $-> cat_biprod)
  (rec : forall z, (forall i, x i $-> z) -> cat_biprod $-> z)
  (rec_beta : forall z f i, rec z f $o cat_in i $== f i)
  (rec_eta : forall z (f g : cat_biprod $-> z),
    (forall i, f $o cat_in i $== g $o cat_in i) -> f $== g)
  (** The projections and inclusion maps satisfy some further properties. *)
  (cat_pr_in : forall i, cat_pr i $o cat_in i $== Id _)
  (cat_pr_in_ne : forall i j, i <> j -> cat_pr j $o cat_in i $== zero_morphism)
  : Biproduct I x.
Proof.
  snapply (Build_Biproduct' _ _ _ cat_biprod).
  exact (Build_IsBiproduct I x cat_biprod
    cat_pr corec corec_beta corec_eta
    cat_in rec rec_beta rec_eta
    cat_pr_in cat_pr_in_ne).
Defined.

Definition Build_hBiproduct (I : Type) `{DecidablePaths I}
  {A : Type} `{IsPointedCat A} (x : I -> A)
  (cat_biprod : A) `{!IsProduct I x cat_biprod, !IsCoproduct I x cat_biprod}
  (h : Id cat_biprod $== cat_coprod_prod x cat_biprod cat_biprod)
  : Biproduct I x.
Proof.
  snapply (Build_Biproduct' _ _ _ cat_biprod).
  by rapply Build_hIsBiproduct.
Defined.

Definition Build_Biproduct'' (I : Type) `{DecidablePaths I}
  {A : Type} `{HasEquivs A, !IsPointedCat A} (x : I -> A)
  (cat_prod : A) `{!IsProduct I x cat_prod}
  (cat_coprod : A) `{!IsCoproduct I x cat_coprod}
  {e : CatIsEquiv (cat_coprod_prod x _ _)}
  : Biproduct I x.
Proof.
  snapply (Build_Biproduct' _ _ _ cat_prod).
  rapply Build_IsBiproduct''.
Defined.

(** *** Existence of biproducts *)

Class HasBiproducts (I A : Type)
  `{DecidablePaths I, HasEquivs A, !IsPointedCat A}
  := has_biproducts :: forall (x : I -> A), Biproduct I x.

(** *** Binary biproducts *)

Class BinaryBiproduct {A : Type} `{IsPointedCat A} (x y : A)
  := binary_biproduct :: Biproduct Bool (fun b => if b then x else y).

(** Smart constructor for binary biproducts. *)
Definition Build_BinaryBiproduct {A : Type} `{IsPointedCat A}
  {x y : A} (cat_biprod : A)
  (** A binary biproduct is a product. *)
  (cat_pr1 : cat_biprod $-> x) (cat_pr2 : cat_biprod $-> y)
  (corec : forall z, (z $-> x) -> (z $-> y) -> z $-> cat_biprod)
  (corec_beta_pr1 : forall z f g, cat_pr1 $o corec z f g $== f)
  (corec_beta_pr2 : forall z f g, cat_pr2 $o corec z f g $== g)
  (corec_eta : forall z (f g : z $-> cat_biprod),
    cat_pr1 $o f $== cat_pr1 $o g -> cat_pr2 $o f $== cat_pr2 $o g -> f $== g)
  (** A biproduct is a coproduct. *)
  (cat_inl : x $-> cat_biprod) (cat_inr : y $-> cat_biprod)
  (rec : forall z, (x $-> z) -> (y $-> z) -> cat_biprod $-> z)
  (rec_beta_inl : forall z f g, rec z f g $o cat_inl $== f)
  (rec_beta_inr : forall z f g, rec z f g $o cat_inr $== g)
  (rec_eta : forall z (f g : cat_biprod $-> z),
    f $o cat_inl $== g $o cat_inl -> f $o cat_inr $== g $o cat_inr -> f $== g)
  (** The projections and inclusion maps satisfy some further properties. *)
  (cat_pr1_inl : cat_pr1 $o cat_inl $== Id _)
  (cat_pr2_inr : cat_pr2 $o cat_inr $== Id _)
  (cat_pr1_inr : cat_pr1 $o cat_inr $== zero_morphism)
  (cat_pr2_inl : cat_pr2 $o cat_inl $== zero_morphism)
  : BinaryBiproduct x y.
Proof.
  snapply Build_Biproduct.
  - exact cat_biprod.
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

Class HasBinaryBiproducts (A : Type) `{IsPointedCat A}
  := has_binary_biproducts :: forall (x y : A), BinaryBiproduct x y.

Global Instance hasbinarybiproducts_hasbiproductsbool {A : Type}
  `{HasEquivs A, !IsPointedCat A, !HasBiproducts Bool A}
  : HasBinaryBiproducts A
  := fun x y => has_biproducts (fun b : Bool => if b then x else y).

Global Instance hasbinaryproducts_hasbinarybiproducts {A : Type}
  `{H : HasBinaryBiproducts A}
  : HasBinaryProducts A.
Proof.
  intros x y.
  rapply Build_Product'.
Defined.

Global Instance hasbinarycoproducts_hasbinarybiproducts {A : Type}
  `{H : HasBinaryBiproducts A}
  : HasBinaryCoproducts A.
Proof.
  intros x y.
  napply Build_Product'.
  napply Build_IsProduct'.
  napply cat_isequiv_cat_coprod_rec_inv.
  napply iscoproduct_isbiproduct.
  napply cat_isbiprod.
  exact (H x y).
Defined.

(* It doesn't make sense to make the rest of this file work, and then change everything after introducing IsBinaryBiproduct. *)

(* Section BinaryBiproducts.

  Context {A : Type} `{HasEquivs A, !IsPointedCat A} {x y : A}
    `{!BinaryBiproduct x y}.

  Definition cat_binbiprod : A
    := cat_biprod Bool (fun b => if b then x else y).

  Definition cat_binbiprod_pr1 : cat_binbiprod $-> x := cat_pr true.
  Definition cat_binbiprod_pr2 : cat_binbiprod $-> y := cat_pr false.

  Definition cat_binbiprod_corec {z : A} (f : z $-> x) (g : z $-> y)
    : z $-> cat_binbiprod.
  Proof.
    napply cat_prod_corec.
    intros [|].
    - exact f.
    - exact g.
  Defined.

  Definition cat_binbiprod_corec_beta_pr1 {z : A} (f : z $-> x) (g : z $-> y)
    : cat_binbiprod_pr1 $o cat_binbiprod_corec f g $== f
    := cat_prod_beta _ _ true.

  Definition cat_binbiprod_corec_beta_pr2 {z : A} (f : z $-> x) (g : z $-> y)
    : cat_binbiprod_pr2 $o cat_binbiprod_corec f g $== g
    := cat_prod_beta _ _ false.

  Definition cat_binbiprod_corec_eta {z : A} (f : z $-> cat_binbiprod)
    : cat_binbiprod_corec (cat_binbiprod_pr1 $o f) (cat_binbiprod_pr2 $o f)
      $== f.
  Proof.
    napply cat_prod_pr_eta.
    intros [|].
    - exact (cat_binbiprod_corec_beta_pr1 _ _).
    - exact (cat_binbiprod_corec_beta_pr2 _ _).
  Defined.

  Definition cat_binbiprod_corec_eta' {z : A} {f f' : z $-> x} {g g' : z $-> y}
    : f $== f' -> g $== g'
      -> cat_binbiprod_corec f g $== cat_binbiprod_corec f' g'.
  Proof.
    intros p q.
    napply cat_prod_corec_eta.
    intros [|].
    - exact p.
    - exact q.
  Defined.

  Definition cat_binbiprod_pr_eta {z : A} {f f' : z $-> cat_binbiprod}
     : cat_binbiprod_pr1 $o f $== cat_binbiprod_pr1 $o f'
      -> cat_binbiprod_pr2 $o f $== cat_binbiprod_pr2 $o f'
      -> f $== f'.
  Proof.
    intros p q.
    napply cat_prod_pr_eta.
    intros [|].
    - exact p.
    - exact q.
  Defined.

  Definition cat_binbiprod_inl : x $-> cat_binbiprod := cat_in true.
  Definition cat_binbiprod_inr : y $-> cat_binbiprod := cat_in false.

  Definition cat_binbiprod_rec {z : A} (f : x $-> z) (g : y $-> z)
    : cat_binbiprod $-> z.
  Proof.
    tapply cat_coprod_rec.
    intros [|].
    - exact f.
    - exact g.
  Defined.

  Definition cat_binbiprod_rec_beta_inl {z : A} (f : x $-> z) (g : y $-> z)
    : cat_binbiprod_rec f g $o cat_binbiprod_inl $== f
    := cat_coprod_beta _ _ true.

  Definition cat_binbiprod_rec_beta_inr {z : A} (f : x $-> z) (g : y $-> z)
    : cat_binbiprod_rec f g $o cat_binbiprod_inr $== g
    := cat_coprod_beta _ _ false.

  Definition cat_binbiprod_rec_eta {z : A} (f : cat_binbiprod $-> z)
    : cat_binbiprod_rec (f $o cat_binbiprod_inl) (f $o cat_binbiprod_inr) $== f.
  Proof.
    tapply cat_coprod_in_eta.
    intros [|].
    - exact (cat_binbiprod_rec_beta_inl _ _).
    - exact (cat_binbiprod_rec_beta_inr _ _).
  Defined.

  Definition cat_binbiprod_rec_eta' {z : A} {f f' : x $-> z} {g g' : y $-> z}
    : f $== f' -> g $== g'
      -> cat_binbiprod_rec f g $== cat_binbiprod_rec f' g'.
  Proof.
    intros p q.
    napply cat_coprod_rec_eta.
    intros [|].
    - exact p.
    - exact q.
  Defined.

  Definition cat_binbiprod_in_eta {z : A} {f f' : cat_binbiprod $-> z}
    : f $o cat_binbiprod_inl $== f' $o cat_binbiprod_inl
      -> f $o cat_binbiprod_inr $== f' $o cat_binbiprod_inr
      -> f $== f'.
  Proof.
    intros p q.
    tapply cat_coprod_in_eta.
    intros [|].
    - exact p.
    - exact q.
  Defined.

  Definition cat_binbiprod_pr1_inl
    : cat_binbiprod_pr1 $o cat_binbiprod_inl $== Id _
    := cat_biprod_pr_in_eq Bool _ true.

  Definition cat_binbiprod_pr2_inr
    : cat_binbiprod_pr2 $o cat_binbiprod_inr $== Id _
    := cat_biprod_pr_in_eq Bool _ false.

  Definition cat_binbiprod_pr2_inl
    : cat_binbiprod_pr2 $o cat_binbiprod_inl $== zero_morphism.
  Proof.
    snapply (cat_biprod_pr_in_ne Bool _ (i := true) (j := false)).
    napply (not_fixed_negb false).
  Defined.

  Definition cat_binbiprod_pr1_inr
    : cat_binbiprod_pr1 $o cat_binbiprod_inr $== zero_morphism.
  Proof.
    snapply (cat_biprod_pr_in_ne Bool _ (i := false) (j := true)).
    napply (not_fixed_negb true).
  Defined.

  Definition cat_binbiprod_corec_zero_inl {z} (f : z $-> x)
    : cat_binbiprod_corec f zero_morphism $== cat_binbiprod_inl $o f.
  Proof.
    snapply cat_binbiprod_pr_eta.
    - refine (cat_binbiprod_corec_beta_pr1 _ _ $@ _^$).
      exact ((cat_assoc _ _ _)^$ $@ (cat_binbiprod_pr1_inl $@R _) $@ cat_idl _).
    - refine (cat_binbiprod_corec_beta_pr2 _ _ $@ _^$).
      exact ((cat_assoc _ _ _)^$ $@ (cat_binbiprod_pr2_inl $@R _) $@ cat_zero_l _).
  Defined.

  Definition cat_binbiprod_corec_zero_inr {z} (f : z $-> y)
    : cat_binbiprod_corec zero_morphism f $== cat_binbiprod_inr $o f.
  Proof.
    snapply cat_binbiprod_pr_eta.
    - refine (cat_binbiprod_corec_beta_pr1 _ _ $@ _^$).
      exact ((cat_assoc _ _ _)^$ $@ (cat_binbiprod_pr1_inr $@R _) $@ cat_zero_l _).
    - refine (cat_binbiprod_corec_beta_pr2 _ _ $@ _^$).
      exact ((cat_assoc _ _ _)^$ $@ (cat_binbiprod_pr2_inr $@R _) $@ cat_idl _).
  Defined.

End BinaryBiproducts.

Arguments cat_binbiprod {A _ _ _ _ _ _} x y {_}.

(** Annoyingly this doesn't follow directly from the general diagonal since [fun b => if b then x else x] is not definitionally equal to [fun _ => x]. *)
Definition cat_binbiprod_diag {A : Type}
  `{HasEquivs A, !IsPointedCat A} (x : A) `{!BinaryBiproduct x x}
  : x $-> cat_binbiprod x x.
Proof.
  snapply cat_binbiprod_corec; exact (Id _).
Defined.

Definition cat_binbiprod_codiag {A : Type}
  `{HasEquivs A, !IsPointedCat A} (x : A) `{!BinaryBiproduct x x}
  : cat_binbiprod x x $-> x.
Proof.
  snapply cat_binbiprod_rec; exact (Id _).
Defined.

(** Compatability of [cat_binprod_rec] and [cat_binprod_corec]. *)
Definition cat_binbiprod_corec_rec {A : Type}
  `{HasEquivs A, !IsPointedCat A} {w x y z : A}
  `{!BinaryBiproduct w x, !BinaryBiproduct y z}
  (f : w $-> y) (g : x $-> z)
  : cat_binbiprod_corec (f $o cat_binbiprod_pr1) (g $o cat_binbiprod_pr2)
    $== cat_binbiprod_rec (cat_binbiprod_inl $o f) (cat_binbiprod_inr $o g).
Proof.
  unfold cat_binbiprod_corec, cat_binbiprod_rec.
  nrefine (_ $@ _ $@ _).
  2: snapply cat_biprod_corec_rec; by intros [|].
  1: snapply cat_prod_corec_eta; by intros [|].
  snapply cat_coprod_rec_eta; by intros [|].
Defined.

(** *** Binary biproduct bifunctor *)

Global Instance is0bifunctor_cat_binbiprod {A : Type}
  `{HasBinaryBiproducts A}
  : Is0Bifunctor (fun x y : A => cat_binbiprod x y)
  := is0bifunctor_cat_binprod.

Global Instance is1bifunctor_cat_binbiprod {A : Type}
  `{HasBinaryBiproducts A}
  : Is1Bifunctor (fun x y : A => cat_binbiprod x y)
  := is1bifunctor_cat_binprod.

(** Binary biproducts are functorial in each argument. *)
Global Instance is0functor_cat_binbiprod_l {A : Type}
  `{HasBinaryBiproducts A} (y : A)
  : Is0Functor (fun x => cat_binbiprod x y)
  := is0functor10_bifunctor _ y.

Global Instance is1functor_cat_binbiprod_l {A : Type}
  `{HasBinaryBiproducts A} (y : A)
  : Is1Functor (fun x => cat_binbiprod x y)
  := is1functor10_bifunctor _ y.

Global Instance is0functor_cat_binbiprod_r {A : Type}
  `{HasBinaryBiproducts A} (x : A)
  : Is0Functor (fun y => cat_binbiprod x y)
  := is0functor01_bifunctor _ x.

Global Instance is1functor_cat_binbiprod_r {A : Type}
  `{HasBinaryBiproducts A} (x : A)
  : Is1Functor (fun y => cat_binbiprod x y)
  := is1functor01_bifunctor _ x.

(** *** Functor lemmas *)

Definition cat_binbiprod_fmap01_corec {A : Type}
  `{HasEquivs A, !IsPointedCat A, !HasBinaryBiproducts A} {w x y z : A}
  (f : w $-> z) (g : x $-> y) (h : w $-> x)
  : fmap01 (fun x y => cat_binbiprod x y) z g $o cat_binbiprod_corec f h
    $== cat_binbiprod_corec f (g $o h).
Proof.
  rapply cat_binprod_fmap01_corec.
Defined.

Definition cat_binbiprod_fmap10_corec {A : Type}
  `{HasEquivs A, !IsPointedCat A, !HasBinaryBiproducts A} {w x y z : A}
  (f : x $-> y) (g : w $-> x) (h : w $-> z)
  : fmap10 (fun x y => cat_binbiprod x y) f z $o cat_binbiprod_corec g h
    $== cat_binbiprod_corec (f $o g) h.
Proof.
  rapply cat_binprod_fmap10_corec.
Defined.

Definition cat_binbiprod_fmap11_corec {A : Type}
  `{HasEquivs A, !IsPointedCat A, !HasBinaryBiproducts A} {v w x y z : A}
  (f : w $-> y) (g : x $-> z) (h : v $-> w) (i : v $-> x)
  : fmap11 (fun x y => cat_binbiprod x y) f g $o cat_binbiprod_corec h i
    $== cat_binbiprod_corec (f $o h) (g $o i).
Proof.
  rapply cat_binprod_fmap11_corec.
Defined.

Definition cat_binbiprod_diag_fmap11 {A : Type}
  `{HasEquivs A, !IsPointedCat A, !HasBinaryBiproducts A} {x y : A} (f : x $-> y)
  : cat_binbiprod_diag y $o f
    $== fmap11 (fun x y => cat_binbiprod x y) f f $o cat_binbiprod_diag x.
Proof.
  refine (_ $@ _^$).
  2: napply cat_binbiprod_fmap11_corec.
  napply cat_binbiprod_pr_eta.
  - refine ((cat_assoc _ _ _)^$ $@ _).
    refine ((_ $@R _) $@ cat_idl _ $@ (cat_idr _)^$ $@ _^$).
    1,2: rapply cat_binbiprod_corec_beta_pr1.
  - refine ((cat_assoc _ _ _)^$ $@ _).
    refine ((_ $@R _) $@ cat_idl _ $@ (cat_idr _)^$ $@ _^$).
    1,2: rapply cat_binbiprod_corec_beta_pr2.
Defined.

Definition cat_binbiprod_codiag_fmap11 {A : Type}
  `{HasEquivs A, !IsPointedCat A, !HasBinaryBiproducts A} {x y : A} (f : x $-> y)
  : f $o cat_binbiprod_codiag x
    $== cat_binbiprod_codiag y $o fmap11 (fun x y => cat_binbiprod x y) f f.
Proof.
  napply cat_binbiprod_in_eta.
  - refine (cat_assoc _ _ _ $@ (_ $@L _) $@ cat_idr _ $@ _).
    1: napply cat_binbiprod_rec_beta_inl.
    refine (_ $@ (_ $@L _) $@ (cat_assoc _ _ _)^$).
    2: { refine (_^$ $@ (cat_binbiprod_corec_rec _ _ $@R _)^$).
         napply cat_binbiprod_rec_beta_inl. }
    nrefine (_ $@ cat_assoc _ _ _).
    refine ((_ $@R _) $@ _)^$.
    1: napply cat_binbiprod_rec_beta_inl.
    napply cat_idl.
  - refine (cat_assoc _ _ _ $@ (_ $@L _) $@ cat_idr _ $@ _).
    1: napply cat_binbiprod_rec_beta_inr.
    refine (_ $@ (_ $@L _) $@ (cat_assoc _ _ _)^$).
    2: { refine (_^$ $@ (cat_binbiprod_corec_rec _ _ $@R _)^$).
         1: napply cat_binbiprod_rec_beta_inr. }
    refine (_^$ $@ (_^$ $@R _) $@ cat_assoc _ _ _).
    2: napply cat_binbiprod_rec_beta_inr.
    rapply cat_idl.
  Defined.

(** *** Symmetry *)

Section Symmetry.
  Context {A : Type} `{HasBinaryBiproducts A}.

  Definition cat_binbiprod_swap (x y : A)
    : cat_binbiprod x y $-> cat_binbiprod y x
    := cat_binbiprod_corec cat_binbiprod_pr2 cat_binbiprod_pr1.

  Lemma cat_binbiprod_swap_swap (x y : A)
    : cat_binbiprod_swap x y $o cat_binbiprod_swap y x $== Id _.
  Proof.
    rapply cat_binprod_swap_cat_binprod_swap.
  Defined.

  Local Instance symmetricbraiding_cat_binbiprod
    : SymmetricBraiding (fun x y => cat_binbiprod x y).
  Proof.
    rapply symmetricbraiding_binprod.
  Defined.

  Lemma cat_binbiprod_swap_inl (x y : A)
    : cat_binbiprod_swap x y $o cat_binbiprod_inl
      $== cat_binbiprod_inr.
  Proof.
    napply cat_binbiprod_pr_eta.
    - refine ((cat_assoc _ _ _)^$ $@ _).
      refine ((_ $@R _) $@ _).
      1: napply cat_binbiprod_corec_beta_pr1.
      refine (_ $@ _^$).
      1: napply cat_binbiprod_pr2_inl.
      napply cat_binbiprod_pr1_inr.
    - refine ((cat_assoc _ _ _)^$ $@ _).
      refine ((_ $@R _) $@ _).
      1: napply cat_binbiprod_corec_beta_pr2.
      refine (_ $@ _^$).
      1: napply cat_binbiprod_pr1_inl.
      napply cat_binbiprod_pr2_inr.
  Defined.

  Lemma cat_binbiprod_swap_inr (x y : A)
    : cat_binbiprod_swap x y $o cat_binbiprod_inr
      $== cat_binbiprod_inl.
  Proof.
    napply cat_binbiprod_pr_eta.
    - refine ((cat_assoc _ _ _)^$ $@ _).
      refine ((_ $@R _) $@ _).
      1: napply cat_binbiprod_corec_beta_pr1.
      refine (_ $@ _^$).
      1: napply cat_binbiprod_pr2_inr.
      napply cat_binbiprod_pr1_inl.
    - refine ((cat_assoc _ _ _)^$ $@ _).
      refine ((_ $@R _) $@ _).
      1: napply cat_binbiprod_corec_beta_pr2.
      refine (_ $@ _^$).
      1: napply cat_binbiprod_pr1_inr.
      napply cat_binbiprod_pr2_inl.
  Defined.

  (** The swap map preserves the diagonal. *)
  Lemma cat_binbiprod_swap_diag (x : A)
    : cat_binbiprod_swap x x $o cat_binbiprod_diag x $== cat_binbiprod_diag x.
  Proof.
    napply cat_binbiprod_pr_eta.
    - refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      1: napply cat_binbiprod_corec_beta_pr1.
      refine (cat_binbiprod_corec_beta_pr2 _ _ $@ _^$).
      napply cat_binbiprod_corec_beta_pr1.
    - refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      1: napply cat_binbiprod_corec_beta_pr2.
      refine (cat_binbiprod_corec_beta_pr1 _ _ $@ _^$).
      napply cat_binbiprod_corec_beta_pr2.
  Defined.

  (** The swap map preserves the codiagonal. *)
  Lemma cat_binbiprod_swap_codiag (x : A)
    : cat_binbiprod_codiag x $o cat_binbiprod_swap x x $== cat_binbiprod_codiag x.
  Proof.
    napply cat_binbiprod_in_eta.
    - refine (_ $@ (cat_binbiprod_rec_beta_inl _ _)^$).
      refine (cat_assoc _ _ _ $@ (_ $@L _) $@ _).
      1: napply cat_binbiprod_swap_inl.
      napply cat_binbiprod_rec_beta_inr.
    - refine (_ $@ (cat_binbiprod_rec_beta_inr _ _)^$).
      refine (cat_assoc _ _ _ $@ (_ $@L _) $@ _).
      1: napply cat_binbiprod_swap_inr.
      napply cat_binbiprod_rec_beta_inl.
  Defined.

End Symmetry.

(** *** Associativity of binary biproducts *)

Section Associativity.

  Context {A : Type} `{HasBinaryBiproducts A}.

  Local Existing Instance associator_cat_binprod.

  Lemma cate_binbiprod_assoc (x y z : A)
    : cat_binbiprod x (cat_binbiprod y z)
      $<~> cat_binbiprod (cat_binbiprod x y) z.
  Proof.
    rapply associator_cat_binprod.
  Defined.

  Definition cat_binbiprod_twist (x y z : A)
    : cat_binbiprod x (cat_binbiprod y z)
      $-> cat_binbiprod y (cat_binbiprod x z)
    := cat_binprod_twist x y z.

  Lemma cat_binbiprod_twist_inl (x y z : A)
    : cat_binbiprod_twist x y z $o cat_binbiprod_inl
      $== cat_binbiprod_inr $o cat_binbiprod_inl.
  Proof.
    napply cat_binbiprod_pr_eta.
    - refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      1: napply cat_binbiprod_corec_beta_pr1.
      refine (cat_assoc _ _ _ $@ _ $@ cat_assoc _ _ _).
      refine ((_ $@L _) $@ _ $@ (_^$ $@R _)).
      1: napply cat_binbiprod_pr2_inl.
      2: napply cat_binbiprod_pr1_inr.
      refine (_ $@ _^$).
      1: napply cat_zero_r.
      napply cat_zero_l.
    - refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      1: napply cat_binbiprod_corec_beta_pr2.
      refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ _).
      refine (cat_binbiprod_rec_beta_inl _ _ $@ cat_idr _ $@ _).
      refine ((cat_idl _)^$ $@ (_^$ $@R _) $@ cat_assoc _ _ _).
      napply cat_binbiprod_pr2_inr.
  Defined.

  Lemma cat_binbiprod_twist_inr_inl (x y z : A)
    : cat_binbiprod_twist x y z $o cat_binbiprod_inr $o cat_binbiprod_inl
      $== cat_binbiprod_inl.
  Proof.
    napply cat_binbiprod_pr_eta.
    - refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _)).
        1: napply cat_binbiprod_corec_beta_pr1. }
      refine (cat_assoc _ _ _ $@ _).
      refine (cat_assoc _ _ _ $@ _).
      refine ((_ $@L _) $@ _).
      { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
        1: napply cat_binbiprod_pr2_inr.
        napply cat_idl. }
      refine (_ $@ _^$).
      1,2: napply cat_binbiprod_pr1_inl.
    - refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _)).
        1: napply cat_binbiprod_corec_beta_pr2. }
      refine (cat_assoc _ _ _ $@ (_ $@R _) $@ _).
      1: napply cat_binbiprod_corec_rec.
      refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      1: napply cat_binbiprod_rec_beta_inr.
      refine (cat_assoc _ _ _ $@ (_ $@L _) $@ _).
      1: napply cat_binbiprod_pr2_inl.
      refine (_ $@ _^$).
      1: napply cat_zero_r.
      napply cat_binbiprod_pr2_inl.
  Defined.

  Lemma cat_binbiprod_twist_inr_inr (x y z : A)
    : cat_binbiprod_twist x y z $o cat_binbiprod_inr $o cat_binbiprod_inr
      $== cat_binbiprod_inr $o cat_binbiprod_inr.
  Proof.
    napply cat_binbiprod_pr_eta.
    - refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _)).
        1: napply cat_binbiprod_corec_beta_pr1. }
      refine (cat_assoc _ _ _ $@ _).
      refine (cat_assoc _ _ _ $@ _).
      refine ((_ $@L _) $@ _).
      { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
        1: napply cat_binbiprod_pr2_inr.
        napply cat_idl. }
      refine (_ $@ _^$).
      1: napply cat_binbiprod_pr1_inr.
      refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      1: napply cat_binbiprod_pr1_inr.
      napply cat_zero_l.
    - refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _)).
        1: napply cat_binbiprod_corec_beta_pr2. }
      refine (cat_assoc _ _ _ $@ (_ $@R _) $@ _).
      1: napply cat_binbiprod_corec_rec.
      refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      1: napply cat_binbiprod_rec_beta_inr.
      refine (cat_assoc _ _ _ $@ (_ $@L _) $@ _).
      1: napply cat_binbiprod_pr2_inr.
      refine (cat_idr _ $@ _^$).
      refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      1: napply cat_binbiprod_pr2_inr.
      napply cat_idl.
  Defined.

  Lemma cate_binbiprod_assoc_inl (x y z : A)
    : cate_binbiprod_assoc x y z $o cat_binbiprod_inl
      $== cat_binbiprod_inl $o cat_binbiprod_inl.
  Proof.
    refine ((_ $@R _) $@ _).
    1: napply associator_twist'_unfold.
    refine (cat_assoc _ _ _ $@ _).
    refine ((_ $@L (cat_assoc _ _ _ $@ (_ $@L _))) $@ _).
    { refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ (_ $@ _)).
      1: napply cat_binbiprod_rec_beta_inl.
      napply cat_idr. }
    refine ((_ $@L _) $@ _).
    1: napply cat_binbiprod_twist_inl.
    refine (cat_assoc_opp _ _ _ $@ _).
    refine (_ $@R _).
    napply cat_binbiprod_swap_inr.
  Defined.

  Lemma cate_binbiprod_assoc_inr_inl (x y z : A)
    : cate_binbiprod_assoc x y z $o cat_binbiprod_inr $o cat_binbiprod_inl
      $== cat_binbiprod_inl $o cat_binbiprod_inr.
  Proof.
    refine (((_ $@R _) $@R _) $@ _).
    1: napply associator_twist'_unfold.
    refine (cat_assoc _ _ _ $@ _).
    refine (cat_assoc _ _ _ $@ _).
    refine ((_ $@L (cat_assoc _ _ _ $@ (_ $@L _))) $@ _).
    { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _)).
      refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ _).
      napply cat_binbiprod_rec_beta_inr. }
    refine ((_ $@L _) $@ _).
    { refine ((cat_assoc _ _ _)^$ $@ _).
      refine (((cat_assoc _ _ _)^$ $@R _) $@ _).
      refine (cat_assoc _ _ _ $@ _).
      refine ((_ $@L _) $@ _).
      1: napply cat_binbiprod_swap_inl.
      napply cat_binbiprod_twist_inr_inr. }
    refine ((cat_assoc _ _ _)^$ $@ (_ $@R _)).
    napply cat_binbiprod_swap_inr.
  Defined.

  Lemma cate_binbiprod_assoc_inr_inr (x y z : A)
    : cate_binbiprod_assoc x y z $o cat_binbiprod_inr $o cat_binbiprod_inr
      $== cat_binbiprod_inr.
  Proof.
    refine (((_ $@R _) $@R _) $@ _).
    1: napply associator_twist'_unfold.
    refine (cat_assoc _ _ _ $@ _).
    refine (cat_assoc _ _ _ $@ _).
    refine ((_ $@L (cat_assoc _ _ _ $@ (_ $@L _))) $@ _).
    { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _)).
      refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ _).
      napply cat_binbiprod_rec_beta_inr. }
    refine ((_ $@L _) $@ _).
    { refine ((cat_assoc _ _ _)^$ $@ _).
      refine (((cat_assoc _ _ _)^$ $@R _) $@ _).
      refine (cat_assoc _ _ _ $@ _).
      refine ((_ $@L _) $@ _).
      1: napply cat_binbiprod_swap_inr.
      napply cat_binbiprod_twist_inr_inl. }
    napply cat_binbiprod_swap_inl.
  Defined.

  Definition issymmetricmonoidal_cat_binbiprod
    : IsSymmetricMonoidal A (fun x y => cat_binbiprod x y) zero_object.
  Proof.
    change (IsSymmetricMonoidal A (fun x y => cat_binprod x y) zero_object).
    exact _.
  Defined.

End Associativity.

(** *** Biproducts in the opposite category *)

(** Biproducts exist in the opposite category if they exist in the original category. *)
Global Instance biproduct_op {I A : Type} {x : I -> A} `{Biproduct I A x}
  : Biproduct (A:=A^op) I x.
Proof.
  snapply Build_Biproduct'.
  (** Products in the opposite category are coproducts in the original category. *)
  - exact biproduct_coproduct.
  (** Coproducts in the opposite category are products in the original category. *)
  - napply coproduct_op.
    exact _.
  - snapply catie_homotopic.
    + simpl; exact (cat_coprod_prod (A:=A) x).
    + simpl; exact _.
    + (** Showing that these two maps are homotopic is a bit tricky. *)
      napply cat_coprod_in_eta.
      intros i.
      napply cat_prod_pr_eta.
      intros j.
      simpl.
      refine (cat_assoc _ _ _ $@ _).
      refine ((_ $@L _) $@ _).
      1: napply cat_coprod_beta.
      refine (_ $@ _).
      1: napply cat_prod_beta.
      symmetry.
      refine ((_ $@R _) $@ _).
      1: napply cat_prod_beta.
      refine (_ $@ _).
      1: napply cat_coprod_beta.
      unfold cat_coprod_prod_component.
      generalize (dec_paths j i).
      generalize (dec_paths i j).
      intros [p|np].
      * apply (decidable_hprop_true p^).
        by destruct p.
      * apply (decidable_false (fun q => np q^)).
        reflexivity.
Defined.

Global Instance hasbiproducts_op {I A : Type} `{DecidablePaths I, HasEquivs A, !IsPointedCat A, !HasBiproducts I A}
  : HasBiproducts I (A^op).
Proof.
  intros x.
  by rapply biproduct_op.
Defined.

Global Instance binarybiproduct_op {A : Type}
  `{HasEquivs A, !IsPointedCat A} {x y : A} {bb : BinaryBiproduct x y}
  : BinaryBiproduct (A:=A^op) x y.
Proof.
  napply biproduct_op.
  exact bb.
Defined.

Global Instance hasbinarybiproducts_op {A : Type}
  `{HasEquivs A, !IsPointedCat A} {hbb : HasBinaryBiproducts A}
  : HasBinaryBiproducts (A^op).
Proof.
  intros x y.
  rapply biproduct_op.
  exact (hbb x y).
Defined. *)
