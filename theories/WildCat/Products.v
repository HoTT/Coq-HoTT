Require Import Basics.Equivalences Basics.Overture Basics.Tactics.
Require Import Types.Bool Types.Prod Types.Forall.
Require Import WildCat.Bifunctor WildCat.Core WildCat.Equiv WildCat.EquivGpd
               WildCat.Forall WildCat.NatTrans WildCat.Opposite
               WildCat.Universe WildCat.Yoneda WildCat.ZeroGroupoid
               WildCat.Monoidal WildCat.MonoidalTwistConstruction.

(** * Categories with products *)

Definition cat_prod_corec_inv {I A : Type} `{Is1Cat A}
  (prod : A) (x : I -> A) (z : A) (pr : forall i, prod $-> x i)
  : yon_0gpd prod z $-> prod_0gpd I (fun i => yon_0gpd (x i) z).
Proof.
  snrapply equiv_prod_0gpd_corec.
  intros i.
  exact (fmap (fun x => yon_0gpd x z) (pr i)).
Defined.

(* A product of an [I]-indexed family of objects of a category is an object of the category with an [I]-indexed family of projections such that the induced map is an equivalence. *)
Class Product (I : Type) {A : Type} `{Is1Cat A} {x : I -> A} := Build_Product' {
  cat_prod : A;
  cat_pr : forall i : I, cat_prod $-> x i;
  cat_isequiv_cat_prod_corec_inv
    :: forall z : A, CatIsEquiv (cat_prod_corec_inv cat_prod x z cat_pr);
}.

Arguments Product I {A _ _ _ _} x.
Arguments cat_prod I {A _ _ _ _} x {product} : rename.

(** A convenience wrapper for building products *)
Definition Build_Product (I : Type) {A : Type} `{Is1Cat A} {x : I -> A}
  (cat_prod : A) (cat_pr : forall i : I, cat_prod $-> x i)
  (cat_prod_corec : forall z : A,
    (forall i : I, z $-> x i) -> (z $-> cat_prod))
  (cat_prod_beta_pr : forall (z : A) (f : forall i, z $-> x i) (i : I),
    cat_pr i $o cat_prod_corec z f $== f i)
  (cat_prod_eta_pr : forall (z : A) (f g : z $-> cat_prod),
    (forall i : I, cat_pr i $o f $== cat_pr i $o g) -> f $== g)
  : Product I x.
Proof.
  snrapply (Build_Product' I A _ _ _ _ _ cat_prod cat_pr).
  intros z.
  nrapply isequiv_0gpd_issurjinj.
  nrapply Build_IsSurjInj.
  - intros f.
    exists (cat_prod_corec z f).
    intros i.
    nrapply cat_prod_beta_pr.
  - intros f g p.
    by nrapply cat_prod_eta_pr.
Defined.

Section Lemmata.

  Context (I : Type) {A : Type} {x : I -> A} `{Product I _ x}.

  Definition cate_cat_prod_corec_inv {z : A}
    : (yon_0gpd (cat_prod I x) z) $<~> prod_0gpd I (fun i => yon_0gpd (x i) z)
    := Build_CatEquiv (cat_prod_corec_inv (cat_prod I x) x z cat_pr).

  Definition cate_cat_prod_corec {z : A}
    : prod_0gpd I (fun i => yon_0gpd (x i) z) $<~> (yon_0gpd (cat_prod I x) z)
    := cate_cat_prod_corec_inv^-1$.

  Definition cat_prod_corec {z : A}
    : (forall i, z $-> x i) -> (z $-> cat_prod I x).
  Proof.
    apply cate_cat_prod_corec.
  Defined.

  (** Applying the [i]th projection after a tuple of maps gives the [ith] map. *)
  Lemma cat_prod_beta {z : A} (f : forall i, z $-> x i)
    : forall i, cat_pr i $o cat_prod_corec f $== f i.
  Proof.
    exact (cate_isretr cate_cat_prod_corec_inv f).
  Defined.

  (** The pairing map is the unique map that makes the following diagram commute. *)
  Lemma cat_prod_eta {z : A} (f : z $-> cat_prod I x)
    : cat_prod_corec (fun i => cat_pr i $o f) $== f.
  Proof.
    exact (cate_issect cate_cat_prod_corec_inv f).
  Defined.

  Local Instance is0functor_prod_0gpd_helper
    : Is0Functor (fun z : A^op => prod_0gpd I (fun i => yon_0gpd (x i) z)).
  Proof.
    snrapply Build_Is0Functor.
    intros a b f.
    snrapply Build_Morphism_0Gpd.
    - intros g i.
      exact (f $o g i).
    - snrapply Build_Is0Functor.
      intros g h p i.
      exact (f $@L p i).
  Defined.

  Local Instance is1functor_prod_0gpd_helper
    : Is1Functor (fun z : A^op => prod_0gpd I (fun i => yon_0gpd (x i) z)).
  Proof.
    snrapply Build_Is1Functor.
    - intros a b f g p r i.
      refine (_ $@L _).
      exact p.
    - intros a r i.
      nrapply cat_idl; exact _.
    - intros a b c f g r i.
      nrapply cat_assoc; exact _.
  Defined.

  Definition natequiv_cat_prod_corec_inv
    : NatEquiv (yon_0gpd (cat_prod I x))
      (fun z : A^op => prod_0gpd I (fun i => yon_0gpd (x i) z)).
  Proof.
    snrapply Build_NatEquiv.
    1: intro; nrapply cate_cat_prod_corec_inv.
    exact (is1natural_yoneda_0gpd
      (cat_prod I x)
      (fun z => prod_0gpd I (fun i => yon_0gpd (x i) z))
      cat_pr).
  Defined.

  Lemma cat_prod_corec_eta {z : A} {f f' : forall i, z $-> x i}
    : (forall i, f i $== f' i) -> cat_prod_corec f $== cat_prod_corec f'.
  Proof.
    intros p.
    unfold cat_prod_corec.
    nrapply (moveL_equiv_V_0gpd cate_cat_prod_corec_inv).
    nrefine (cate_isretr cate_cat_prod_corec_inv _ $@ _).
    exact p.
  Defined.

  Lemma cat_prod_pr_eta {z : A} {f f' : z $-> cat_prod I x}
    : (forall i, cat_pr i $o f $== cat_pr i $o f') -> f $== f'.
  Proof.
    intros p.
    refine ((cat_prod_eta _)^$ $@ _ $@ cat_prod_eta _).
    by nrapply cat_prod_corec_eta.
  Defined.

End Lemmata.

(** *** Diagonal map *)

Definition cat_prod_diag {I : Type} {A : Type} (x : A)
  `{Product I _ (fun _ => x)}
  : x $-> cat_prod I (fun _ => x)
  := cat_prod_corec I (fun _ => Id x).

(** *** Uniqueness of products *)

Definition cate_cat_prod {I J : Type} (ie : I <~> J) {A : Type} `{HasEquivs A}
  (x : I -> A) `{!Product I x} (y : J -> A) `{!Product J y}
  (e : forall i : I, x i $<~> y (ie i))
  : cat_prod I x $<~> cat_prod J y.
Proof.
  nrapply yon_equiv_0gpd.
  nrefine (natequiv_compose _ (natequiv_cat_prod_corec_inv _)).
  nrefine (natequiv_compose
            (natequiv_inverse (natequiv_cat_prod_corec_inv _)) _).
  snrapply Build_NatEquiv.
  - intros z.
    nrapply (cate_prod_0gpd ie).
    intros i.
    exact (natequiv_yon_equiv_0gpd (e i) _).
  - snrapply Build_Is1Natural.
    intros a b f g j.
    cbn.
    destruct (eisretr ie j).
    exact (cat_assoc_opp _ _ _).
Defined.

(** [I]-indexed products are unique no matter how they are constructed. *)
Definition cat_prod_unique {I A : Type} `{HasEquivs A}
  (x : I -> A) `{!Product I x} (y : I -> A) `{!Product I y}
  (e : forall i : I, x i $<~> y i)
  : cat_prod I x $<~> cat_prod I y.
Proof.
  exact (cate_cat_prod 1 x y e).
Defined.

(** *** Existence of products *)

Class HasProducts (I A : Type) `{Is1Cat A}
  := has_products :: forall x : I -> A, Product I x.

Class HasAllProducts (A : Type) `{Is1Cat A}
  := has_all_products :: forall I : Type, HasProducts I A.

(** *** Product functor *)

Global Instance is0functor_cat_prod (I : Type) (A : Type) `{HasProducts I A}
  : Is0Functor (fun x : I -> A => cat_prod I x).
Proof.
  nrapply Build_Is0Functor.
  intros x y f.
  exact (cat_prod_corec I (fun i => f i $o cat_pr i)).
Defined.

Global Instance is1functor_cat_prod (I : Type) (A : Type) `{HasProducts I A}
  : Is1Functor (fun x : I -> A => cat_prod I x).
Proof.
  nrapply Build_Is1Functor.
  - intros x y f g p.
    exact (cat_prod_corec_eta I (fun i => p i $@R cat_pr i)).
  - intros x.
    nrefine (_ $@ (cat_prod_eta I (Id _))).
    exact (cat_prod_corec_eta I (fun i => cat_idl _ $@ (cat_idr _)^$)).
  - intros x y z f g.
    nrapply cat_prod_pr_eta.
    intros i.
    nrefine (cat_prod_beta _ _ _ $@ _).
    nrefine (_ $@ cat_assoc _ _ _).
    symmetry.
    nrefine (cat_prod_beta _ _ _ $@R _ $@ _).
    nrefine (cat_assoc _ _ _ $@ _).
    nrefine (_ $@L cat_prod_beta _ _ _ $@ _).
    nrapply cat_assoc_opp.
Defined.

(** *** Categories with specific kinds of products *)

Definition isterminal_prodempty {A : Type} {z : A}
  `{Product Empty A (fun _ => z)}
  : IsTerminal (cat_prod Empty (fun _ => z)).
Proof.
  intros a.
  snrefine (cat_prod_corec _ _; fun f => cat_prod_pr_eta _ _); intros [].
Defined.

(** *** Binary products *)

Class BinaryProduct {A : Type} `{Is1Cat A} (x y : A)
  := binary_product :: Product Bool (fun b => if b then x else y).

(** A category with binary products is a category with a binary product for each pair of objects. *)
Class HasBinaryProducts (A : Type) `{Is1Cat A}
  := has_binary_products :: forall x y : A, BinaryProduct x y.

Global Instance hasbinaryproducts_hasproductsbool {A : Type} `{HasProducts Bool A}
  : HasBinaryProducts A
  := fun x y => has_products (fun b : Bool => if b then x else y).

Section BinaryProducts.

  Context {A : Type} `{Is1Cat A} {x y : A} `{!BinaryProduct x y}.

  Definition cat_binprod : A
    := cat_prod Bool (fun b : Bool => if b then x else y).

  Definition cat_pr1 : cat_binprod $-> x := cat_pr true.

  Definition cat_pr2 : cat_binprod $-> y := cat_pr false.

  Definition cat_binprod_corec {z : A} (f : z $-> x) (g : z $-> y)
    : z $-> cat_binprod.
  Proof.
    nrapply (cat_prod_corec Bool).
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
    nrapply cat_prod_pr_eta.
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

Arguments cat_binprod {A _ _ _ _} x y {_}.

(** A convenience wrapper for building binary products *)
Definition Build_BinaryProduct {A : Type} `{Is1Cat A} {x y : A}
  (cat_binprod : A) (cat_pr1 : cat_binprod $-> x) (cat_pr2 : cat_binprod $-> y)
  (cat_binprod_corec : forall z : A, z $-> x -> z $-> y -> z $-> cat_binprod)
  (cat_binprod_beta_pr1 : forall (z : A) (f : z $-> x) (g : z $-> y),
    cat_pr1 $o cat_binprod_corec z f g $== f)
  (cat_binprod_beta_pr2 : forall (z : A) (f : z $-> x) (g : z $-> y),
    cat_pr2 $o cat_binprod_corec z f g $== g)
  (cat_binprod_eta_pr : forall (z : A) (f g : z $-> cat_binprod),
    cat_pr1 $o f $== cat_pr1 $o g -> cat_pr2 $o f $== cat_pr2 $o g -> f $== g)
  : Product Bool (fun b => if b then x else y).
Proof.
  snrapply (Build_Product _ cat_binprod).
  - intros [|].
    + exact cat_pr1.
    + exact cat_pr2.
  - intros z f.
    nrapply cat_binprod_corec.
    + exact (f true).
    + exact (f false).
  - intros z f [|].
    + nrapply cat_binprod_beta_pr1.
    + nrapply cat_binprod_beta_pr2.
  - intros z f g p.
    nrapply cat_binprod_eta_pr.
    + exact (p true).
    + exact (p false).
Defined.

Definition cat_binprod_eta_pr_x_xx {A : Type} `{HasBinaryProducts A} {w x y z : A}
  (f g : w $-> cat_binprod x (cat_binprod y z))
  : cat_pr1 $o f $== cat_pr1 $o g
  -> cat_pr1 $o cat_pr2 $o f $== cat_pr1 $o cat_pr2 $o g
  -> cat_pr2 $o cat_pr2 $o f $== cat_pr2 $o cat_pr2 $o g
  -> f $== g.
Proof.
  intros p q r.
  snrapply cat_binprod_eta_pr.
  - exact p.
  - snrapply cat_binprod_eta_pr.
    + exact (cat_assoc_opp _ _ _ $@ q $@ cat_assoc _ _ _).
    + exact (cat_assoc_opp _ _ _ $@ r $@ cat_assoc _ _ _).
Defined.

Definition cat_binprod_eta_pr_xx_x {A : Type} `{HasBinaryProducts A} {w x y z : A}
  (f g : w $-> cat_binprod (cat_binprod x y) z)
  : cat_pr1 $o cat_pr1 $o f $== cat_pr1 $o cat_pr1 $o g
  -> cat_pr2 $o cat_pr1 $o f $== cat_pr2 $o cat_pr1 $o g
  -> cat_pr2 $o f $== cat_pr2 $o g
  -> f $== g.
Proof.
  intros p q r.
  snrapply cat_binprod_eta_pr.
  2: exact r.
  snrapply cat_binprod_eta_pr.
  1,2: refine (cat_assoc_opp _ _ _ $@ _ $@ cat_assoc _ _ _).
  - exact p.
  - exact q.
Defined.

Definition cat_binprod_eta_pr_x_xx_id {A : Type} `{HasBinaryProducts A} {x y z : A}
  (f : cat_binprod x (cat_binprod y z) $-> cat_binprod x (cat_binprod y z))
  : cat_pr1 $o f $== cat_pr1
  -> cat_pr1 $o cat_pr2 $o f $== cat_pr1 $o cat_pr2
  -> cat_pr2 $o cat_pr2 $o f $== cat_pr2 $o cat_pr2
  -> f $== Id _.
Proof.
  intros p q r.
  snrapply cat_binprod_eta_pr_x_xx.
  - exact (p $@ (cat_idr _)^$).
  - exact (q $@ (cat_idr _)^$).
  - exact (r $@ (cat_idr _)^$).
Defined.

(** From binary products, all Bool-shaped products can be constructed. This should not be an instance to avoid a cycle with [hasbinaryproducts_hasproductsbool]. *)
Definition hasproductsbool_hasbinaryproducts {A : Type} `{HasBinaryProducts A}
  : HasProducts Bool A.
Proof.
  intros x.
  snrapply Build_Product.
  - exact (cat_binprod (x true) (x false)).
  - intros [|].
    + exact cat_pr1.
    + exact cat_pr2.
  - intros z f.
    exact (cat_binprod_corec (f true) (f false)).
  - intros z f [|].
    + exact (cat_binprod_beta_pr1 (f true) (f false)).
    + exact (cat_binprod_beta_pr2 (f true) (f false)).
  - intros z f g p.
    nrapply cat_binprod_eta_pr.
    + exact (p true).
    + exact (p false).
Defined.

(** *** Operations on indexed products *)

(** We can take the disjoint union of the index set of an indexed product if we have all binary products. This is useful for associating products in a canonical way. This leads to symmetry and associativity of binary products. *)

Definition cat_prod_index_sum {I J : Type} {A : Type} `{HasBinaryProducts A}
  (x : I -> A) (y : J -> A)
  : Product I x -> Product J y -> Product (I + J) (sum_ind _ x y).
Proof.
  intros p q.
  snrapply Build_Product.
  - exact (cat_binprod (cat_prod I x) (cat_prod J y)).
  - intros [i | j].
    + exact (cat_pr _ $o cat_pr1).
    + exact (cat_pr _ $o cat_pr2).
  - intros z f.
    nrapply cat_binprod_corec.
    + nrapply cat_prod_corec.
      exact (f o inl).
    + nrapply cat_prod_corec.
      exact (f o inr).
  - intros z f [i | j].
    + nrefine (cat_assoc _ _ _ $@ _).
      nrefine ((_ $@L cat_binprod_beta_pr1 _ _) $@ _).
      rapply cat_prod_beta.
    + nrefine (cat_assoc _ _ _ $@ _).
      nrefine ((_ $@L cat_binprod_beta_pr2 _ _) $@ _).
      rapply cat_prod_beta.
  - intros z f g r.
    rapply cat_binprod_eta_pr.
    + rapply  cat_prod_pr_eta.
      intros i.
      exact ((cat_assoc _ _ _)^$ $@ r (inl i) $@ cat_assoc _ _ _).
    + rapply  cat_prod_pr_eta.
      intros j.
      exact ((cat_assoc _ _ _)^$ $@ r (inr j) $@ cat_assoc _ _ _).
Defined.

(** *** Binary product functor *)

(** We prove bifunctoriality of [cat_binprod : A -> A -> A] by factoring it as [cat_prod Bool o Bool_rec A]. First, we prove that [Bool_rec A : A -> A -> (Bool -> A)] is a bifunctor. *)
Local Instance is0bifunctor_boolrec {A : Type} `{Is1Cat A}
  : Is0Bifunctor (Bool_rec A).
Proof.
  snrapply Build_Is0Bifunctor'.
  1,2: exact _.
  snrapply Build_Is0Functor.
  intros [a b] [a' b'] [f g] [ | ].
  - exact f.
  - exact g.
Defined.

Local Instance is1bifunctor_boolrec {A : Type} `{Is1Cat A}
  : Is1Bifunctor (Bool_rec A).
Proof.
  snrapply Build_Is1Bifunctor'.
  snrapply Build_Is1Functor.
  - intros [a b] [a' b'] [f g] [f' g'] [p q] [ | ].
    + exact p.
    + exact q.
  - intros [a b] [ | ]; reflexivity.
  - intros [a b] [a' b'] [a'' b''] [f f'] [g g'] [ | ]; reflexivity.
Defined.

(** As a special case of the product functor, restriction along [Bool_rec A] yields bifunctoriality of [cat_binprod]. *)
Global Instance is0bifunctor_cat_binprod {A : Type} `{HasBinaryProducts A}
  : Is0Bifunctor (fun x y => cat_binprod x y).
Proof.
  pose (p:=@has_products _ _ _ _ _ _ hasproductsbool_hasbinaryproducts).
  exact (is0bifunctor_postcompose
          (Bool_rec A) (fun x => cat_prod Bool x (product:=p x))).
Defined.

Global Instance is1bifunctor_cat_binprod {A : Type} `{HasBinaryProducts A}
  : Is1Bifunctor (fun x y => cat_binprod x y).
Proof.
  pose (p:=@has_products _ _ _ _ _ _ hasproductsbool_hasbinaryproducts).
  exact (is1bifunctor_postcompose
          (Bool_rec A) (fun x => cat_prod Bool x (product:=p x))).
Defined.

(** Binary products are functorial in each argument. *)
Global Instance is0functor_cat_binprod_l {A : Type} `{HasBinaryProducts A}
  (y : A)
  : Is0Functor (fun x => cat_binprod x y).
Proof.
  exact (is0functor10_bifunctor _ y).
Defined.

Global Instance is1functor_cat_binprod_l {A : Type} `{HasBinaryProducts A}
  (y : A)
  : Is1Functor (fun x => cat_binprod x y).
Proof.
  exact (is1functor10_bifunctor _ y).
Defined.

Global Instance is0functor_cat_binprod_r {A : Type} `{HasBinaryProducts A}
  (x : A)
  : Is0Functor (fun y => cat_binprod x y).
Proof.
  exact (is0functor01_bifunctor _ x).
Defined.

Global Instance is1functor_cat_binprod_r {A : Type} `{HasBinaryProducts A}
  (x : A)
  : Is1Functor (fun y => cat_binprod x y).
Proof.
  exact (is1functor01_bifunctor _ x).
Defined.

(** [cat_binprod_corec] is also functorial in each morphsism. *)

Global Instance is0functor_cat_binprod_corec_l {A : Type}
  `{HasBinaryProducts A} {x y z : A} (g : z $-> y)
  : Is0Functor (fun f : z $-> y => cat_binprod_corec f g).
Proof.
  snrapply Build_Is0Functor.
  intros f f' p.
  by nrapply cat_binprod_corec_eta.
Defined.

Global Instance is0functor_cat_binprod_corec_r {A : Type}
  `{HasBinaryProducts A} {x y z : A} (f : z $-> x)
  : Is0Functor (fun g : z $-> x => cat_binprod_corec f g).
Proof.
  snrapply Build_Is0Functor.
  intros g h p.
  by nrapply cat_binprod_corec_eta.
Defined.

Definition cat_pr1_fmap01_binprod {A : Type} `{HasBinaryProducts A}
  (a : A) {x y : A} (g : x $-> y)
  : cat_pr1 $o fmap01 (fun x y => cat_binprod x y) a g $== cat_pr1
  := cat_binprod_beta_pr1 _ _ $@ cat_idl _.

Definition cat_pr1_fmap10_binprod {A : Type} `{HasBinaryProducts A}
  {x y : A} (f : x $-> y) (a : A)
  : cat_pr1 $o fmap10 (fun x y => cat_binprod x y) f a $== f $o cat_pr1
  := cat_binprod_beta_pr1 _ _.

Definition cat_pr1_fmap11_binprod {A : Type} `{HasBinaryProducts A}
  {w x y z : A} (f : w $-> y) (g : x $-> z)
  : cat_pr1 $o fmap11 (fun x y => cat_binprod x y) f g $== f $o cat_pr1
  := cat_binprod_beta_pr1 _ _.

Definition cat_pr2_fmap01_binprod {A : Type} `{HasBinaryProducts A}
  (a : A) {x y : A} (g : x $-> y)
  : cat_pr2 $o fmap01 (fun x y => cat_binprod x y) a g $== g $o cat_pr2
  := cat_binprod_beta_pr2 _ _.

Definition cat_pr2_fmap10_binprod {A : Type} `{HasBinaryProducts A}
  {x y : A} (f : x $-> y) (a : A)
  : cat_pr2 $o fmap10 (fun x y => cat_binprod x y) f a $== cat_pr2
  := cat_binprod_beta_pr2 _ _ $@ cat_idl _.

Definition cat_pr2_fmap11_binprod {A : Type} `{HasBinaryProducts A}
  {w x y z : A} (f : w $-> y) (g : x $-> z)
  : cat_pr2 $o fmap11 (fun x y => cat_binprod x y) f g $== g $o cat_pr2
  := cat_binprod_beta_pr2 _ _.

(** *** Diagonal *)

(** Annoyingly this doesn't follow directly from the general diagonal since [fun b => if b then x else x] is not definitionally equal to [fun _ => x]. *)
Definition cat_binprod_diag {A : Type}
  `{Is1Cat A} (x : A) `{!BinaryProduct x x}
  : x $-> cat_binprod x x.
Proof.
  snrapply cat_binprod_corec; exact (Id _).
Defined.

(** *** Lemmas about [cat_binprod_corec] *)

Definition cat_binprod_fmap01_corec {A : Type}
  `{Is1Cat A, !HasBinaryProducts A} {w x y z : A}
  (f : w $-> z) (g : x $-> y) (h : w $-> x)
  : fmap01 (fun x y => cat_binprod x y) z g $o cat_binprod_corec f h
    $== cat_binprod_corec f (g $o h).
Proof.
  snrapply cat_binprod_eta_pr.
  - nrefine (cat_assoc_opp _ _ _ $@ _).
    refine ((_ $@R _) $@ cat_assoc _ _ _ $@ cat_idl _ $@ _ $@ _^$).
    1-3: rapply cat_binprod_beta_pr1.
  - nrefine (cat_assoc_opp _ _ _ $@ _).
    refine ((_ $@R _) $@ cat_assoc _ _ _ $@ (_ $@L _) $@ _^$).
    1-3: rapply cat_binprod_beta_pr2.
Defined.

Definition cat_binprod_fmap10_corec {A : Type}
  `{Is1Cat A, !HasBinaryProducts A} {w x y z : A}
  (f : x $-> y) (g : w $-> x) (h : w $-> z)
  : fmap10 (fun x y => cat_binprod x y) f z $o cat_binprod_corec g h
    $== cat_binprod_corec (f $o g) h.
Proof.
  snrapply cat_binprod_eta_pr.
  - refine (cat_assoc_opp _ _ _ $@ _).
    refine ((_ $@R _) $@ cat_assoc _ _ _ $@ (_ $@L _) $@ _^$).
    1-3: nrapply cat_binprod_beta_pr1.
  - refine (cat_assoc_opp _ _ _ $@ _).
    refine ((_ $@R _) $@ cat_assoc _ _ _ $@ cat_idl _ $@ _ $@ _^$).
    1-3: nrapply cat_binprod_beta_pr2.
Defined.

Definition cat_binprod_fmap11_corec {A : Type}
  `{Is1Cat A, !HasBinaryProducts A} {v w x y z : A}
  (f : w $-> y) (g : x $-> z) (h : v $-> w) (i : v $-> x)
  : fmap11 (fun x y => cat_binprod x y) f g $o cat_binprod_corec h i
    $== cat_binprod_corec (f $o h) (g $o i).
Proof.
  snrapply cat_binprod_eta_pr.
  - refine (cat_assoc_opp _ _ _ $@ _).
    refine ((_ $@R _) $@ cat_assoc _ _ _ $@ (_ $@L _) $@ _^$).
    1-3: nrapply cat_binprod_beta_pr1.
  - nrefine (cat_assoc_opp _ _ _ $@ _).
    refine ((_ $@R _) $@ cat_assoc _ _ _ $@ (_ $@L _) $@ _^$).
    1-3: rapply cat_binprod_beta_pr2.
Defined.

(** *** Symmetry of binary products *)

Section Symmetry.

  (** The requirement of having all binary products can be weakened further to having specific binary products, but it is not clear this is a useful generality. *)
  Context {A : Type} `{HasEquivs A} `{!HasBinaryProducts A}.

  Definition cat_binprod_swap (x y : A) : cat_binprod x y $-> cat_binprod y x
    := cat_binprod_corec cat_pr2 cat_pr1.

  Lemma cat_binprod_swap_cat_binprod_swap (x y : A)
    : cat_binprod_swap x y $o cat_binprod_swap y x $== Id _.
  Proof.
    nrapply cat_binprod_eta_pr.
    - refine ((cat_assoc _ _ _)^$ $@ _).
      nrefine (cat_binprod_beta_pr1 _ _ $@R _ $@ _).
      exact (cat_binprod_beta_pr2 _ _ $@ (cat_idr _)^$).
    - refine ((cat_assoc _ _ _)^$ $@ _).
      nrefine (cat_binprod_beta_pr2 _ _ $@R _ $@ _).
      exact (cat_binprod_beta_pr1 _ _ $@ (cat_idr _)^$).
  Defined.

  Lemma cate_binprod_swap (x y : A)
    : cat_binprod x y $<~> cat_binprod y x.
  Proof.
    snrapply cate_adjointify.
    1,2: nrapply cat_binprod_swap.
    all: nrapply cat_binprod_swap_cat_binprod_swap.
  Defined.

  Definition cat_binprod_swap_corec {a b c : A} (f : a $-> b) (g : a $-> c)
    : cat_binprod_swap b c $o cat_binprod_corec f g $== cat_binprod_corec g f.
  Proof.
    nrapply cat_binprod_eta_pr.
    - refine (cat_assoc_opp _ _ _ $@ (_ $@R _) $@ (_ $@ _^$)).
      1,3: nrapply cat_binprod_beta_pr1.
      nrapply cat_binprod_beta_pr2.
    - refine (cat_assoc_opp _ _ _ $@ (_ $@R _) $@ (_ $@ _^$)).
      1,3: nrapply cat_binprod_beta_pr2.
      nrapply cat_binprod_beta_pr1.
  Defined.

  Definition cat_binprod_swap_nat {a b c d : A} (f : a $-> c) (g : b $-> d)
    : cat_binprod_swap c d $o fmap11 (fun x y : A => cat_binprod x y) f g
    $== fmap11 (fun x y : A => cat_binprod x y) g f $o cat_binprod_swap a b
    := cat_binprod_swap_corec _ _ $@ (cat_binprod_fmap11_corec _ _ _ _)^$.

  Local Instance symmetricbraiding_binprod
    : SymmetricBraiding (fun x y => cat_binprod x y).
  Proof.
    snrapply Build_SymmetricBraiding.
    - snrapply Build_NatTrans.
      + intros [x y].
        exact (cat_binprod_swap x y).
      + snrapply Build_Is1Natural.
        intros [a b] [c d] [f g]; cbn in f, g.
        exact(cat_binprod_swap_nat f g).
    - exact cat_binprod_swap_cat_binprod_swap.
  Defined.

End Symmetry.

(** *** Associativity of binary products *)

Section Associativity.

  Context {A : Type} `{HasEquivs A} `{!HasBinaryProducts A}.

  Definition cat_binprod_twist (x y z : A)
    : cat_binprod x (cat_binprod y z) $-> cat_binprod y (cat_binprod x z).
  Proof.
    nrapply cat_binprod_corec.
    - exact (cat_pr1 $o cat_pr2).
    - exact (fmap01 (fun x y => cat_binprod x y) x cat_pr2).
  Defined.

  Definition cat_binprod_pr1_twist (x y z : A)
    : cat_pr1 $o cat_binprod_twist x y z $== cat_pr1 $o cat_pr2
    := cat_binprod_beta_pr1 _ _.

  Definition cat_binprod_pr1_pr2_twist (x y z : A)
    : cat_pr1 $o cat_pr2 $o cat_binprod_twist x y z $== cat_pr1.
  Proof.
    nrefine (cat_assoc _ _ _ $@ _).
    nrefine ((_ $@L cat_binprod_beta_pr2 _ _) $@ _).
    nrapply cat_pr1_fmap01_binprod.
  Defined.

  Definition cat_binprod_pr2_pr2_twist (x y z : A)
    : cat_pr2 $o cat_pr2 $o cat_binprod_twist x y z $== cat_pr2 $o cat_pr2.
  Proof.
    nrefine (cat_assoc _ _ _ $@ _).
    nrefine ((_ $@L cat_binprod_beta_pr2 _ _) $@ _).
    nrapply cat_pr2_fmap01_binprod.
  Defined.
  
  Definition cat_binprod_twist_corec {w x y z : A}
    (f : w $-> x) (g : w $-> y) (h : w $-> z)
    : cat_binprod_twist x y z $o cat_binprod_corec f (cat_binprod_corec g h)
      $== cat_binprod_corec g (cat_binprod_corec f h).
  Proof.
    nrapply cat_binprod_eta_pr.
    - nrefine (cat_assoc_opp _ _ _ $@ _).
      refine ((_ $@R _) $@ cat_assoc _ _ _ $@ (_ $@L _) $@ (_ $@ _^$)).
      1: nrapply cat_binprod_pr1_twist.
      1: nrapply cat_binprod_beta_pr2.
      1,2: nrapply cat_binprod_beta_pr1.
    - refine (cat_assoc_opp _ _ _ $@ (_ $@R _) $@ _ $@ (cat_binprod_beta_pr2 _ _)^$).
      1: nrapply cat_binprod_beta_pr2.
      nrefine (cat_binprod_fmap01_corec _ _ _ $@ _).
      nrapply cat_binprod_corec_eta.
      1: exact (Id _).
      nrapply cat_binprod_beta_pr2.
  Defined.

  Lemma cat_binprod_twist_cat_binprod_twist (x y z : A)
    : cat_binprod_twist x y z $o cat_binprod_twist y x z $== Id _.
  Proof.
    nrapply cat_binprod_eta_pr_x_xx_id.
    - nrefine (cat_assoc_opp _ _ _ $@ (cat_binprod_pr1_twist _ _ _ $@R _) $@ _).
      nrapply cat_binprod_pr1_pr2_twist.
    - nrefine (cat_assoc_opp _ _ _ $@ (cat_binprod_pr1_pr2_twist _ _ _ $@R _) $@ _).
      nrapply cat_binprod_pr1_twist.
    - nrefine (cat_assoc_opp _ _ _ $@ (cat_binprod_pr2_pr2_twist _ _ _ $@R _) $@ _).
      nrapply cat_binprod_pr2_pr2_twist.
  Defined.

  Definition cate_binprod_twist (x y z : A)
    : cat_binprod x (cat_binprod y z) $<~> cat_binprod y (cat_binprod x z).
  Proof.
    snrapply cate_adjointify.
    1,2: nrapply cat_binprod_twist.
    1,2: nrapply cat_binprod_twist_cat_binprod_twist.
  Defined.

  Definition cat_binprod_twist_nat {a a' b b' c c' : A}
    (f : a $-> a') (g : b $-> b') (h : c $-> c')
    : cat_binprod_twist a' b' c'
        $o fmap11 (fun x y => cat_binprod x y) f (fmap11 (fun x y => cat_binprod x y) g h)
      $== fmap11 (fun x y => cat_binprod x y) g (fmap11 (fun x y => cat_binprod x y) f h)
        $o cat_binprod_twist a b c.
  Proof.
    nrapply cat_binprod_eta_pr.
    - refine (cat_assoc_opp _ _ _ $@ _).
      nrefine ((cat_binprod_beta_pr1 _ _ $@R _) $@ _).
      nrefine (cat_assoc _ _ _ $@ _).
      nrefine ((_ $@L _) $@ _).
      1: nrapply cat_pr2_fmap11_binprod.
      nrefine (cat_assoc_opp _ _ _ $@ _).
      nrefine ((_ $@R _) $@ _).
      1: nrapply cat_pr1_fmap11_binprod.
      nrefine (_ $@ cat_assoc _ _ _).
      refine (_ $@ (_^$ $@R _)).
      2: nrapply cat_pr1_fmap11_binprod.
      refine (cat_assoc _ _ _ $@ (_ $@L _^$) $@ (cat_assoc _ _ _)^$).
      nrapply cat_binprod_beta_pr1.
    - nrefine (cat_assoc_opp _ _ _ $@ (cat_binprod_beta_pr2 _ _ $@R _) $@ _).
      nrefine (_ $@ cat_assoc _ _ _).
      refine (_ $@ (_^$ $@R _)).
      2: nrapply cat_pr2_fmap11_binprod.
      refine (_ $@ (_ $@L _^$) $@ (cat_assoc _ _ _)^$).
      2: nrapply cat_binprod_beta_pr2.
      refine (_^$ $@ _ $@ _).
      1,3: rapply fmap11_comp.
      rapply fmap22.
      1: exact (cat_idl _ $@ (cat_idr _)^$).
      nrapply cat_binprod_beta_pr2.
  Defined.

  Local Existing Instance symmetricbraiding_binprod.

  Local Instance associator_cat_binprod : Associator (fun x y => cat_binprod x y).
  Proof.
    snrapply associator_twist.
    - exact _.
    - exact cat_binprod_twist.
    - exact cat_binprod_twist_cat_binprod_twist.
    - intros ? ? ? ? ? ?; exact cat_binprod_twist_nat.
  Defined.

  Definition cat_pr1_pr1_associator_binprod x y z
    : cat_pr1 $o cat_pr1 $o associator_cat_binprod x y z $== cat_pr1.
  Proof.
    nrefine ((_ $@L associator_twist'_unfold _ _ _ _ _ _ _ _) $@ _).
    nrefine (cat_assoc _ _ _ $@ (_ $@L (cat_assoc_opp _ _ _ $@ (_ $@R _))) $@ _).
    1: nrapply cat_binprod_beta_pr1.
    do 2 nrefine (cat_assoc_opp _ _ _ $@ _).
    nrefine ((cat_binprod_pr1_pr2_twist _ _ _ $@R _) $@ _).
    nrapply cat_pr1_fmap01_binprod.
  Defined.

  Definition cat_pr2_pr1_associator_binprod x y z
    : cat_pr2 $o cat_pr1 $o associator_cat_binprod x y z $== cat_pr1 $o cat_pr2.
  Proof.
    nrefine ((_ $@L associator_twist'_unfold _ _ _ _ _ _ _ _) $@ _).
    nrefine (cat_assoc _ _ _ $@ (_ $@L (cat_assoc_opp _ _ _ $@ (_ $@R _))) $@ _).
    1: nrapply cat_binprod_beta_pr1.
    do 2 nrefine (cat_assoc_opp _ _ _ $@ _).
    nrefine ((cat_binprod_pr2_pr2_twist _ _ _ $@R _) $@ _).
    nrefine (cat_assoc _ _ _ $@ (_ $@L cat_pr2_fmap01_binprod _ _) $@ _).
    exact (cat_assoc_opp _ _ _ $@ (cat_binprod_beta_pr2 _ _ $@R _)).
  Defined.

  Definition cat_pr2_associator_binprod x y z
    : cat_pr2 $o associator_cat_binprod x y z $== cat_pr2 $o cat_pr2.
  Proof.
    nrefine ((_ $@L associator_twist'_unfold _ _ _ _ _ _ _ _) $@ _).
    nrefine (cat_assoc_opp _ _ _ $@ (cat_binprod_beta_pr2 _ _ $@R _) $@ _).
    nrefine (cat_assoc_opp _ _ _ $@ (cat_binprod_pr1_twist _ _ _ $@R _) $@ _).
    nrefine (cat_assoc _ _ _ $@ (_ $@L cat_pr2_fmap01_binprod _ _) $@ _).
    exact (cat_assoc_opp _ _ _ $@ (cat_binprod_beta_pr1 _ _ $@R _)).
  Defined.
  
  Definition cat_binprod_associator_corec {w x y z}
    (f : w $-> x) (g : w $-> y) (h : w $-> z)
    : associator_cat_binprod x y z $o cat_binprod_corec f (cat_binprod_corec g h)
      $== cat_binprod_corec (cat_binprod_corec f g) h. 
  Proof.
    nrefine ((associator_twist'_unfold _ _ _ _ _ _ _ _ $@R _) $@ _).
    nrefine ((cat_assoc_opp _ _ _ $@R _) $@ cat_assoc _ _ _ $@ (_ $@L (_ $@ _)) $@ _). 
    1: nrapply cat_binprod_fmap01_corec.
    1: rapply (cat_binprod_corec_eta _ _ _ _ (Id _)).
    1: nrapply cat_binprod_swap_corec.
    nrefine (cat_assoc _ _ _ $@ (_ $@L _) $@ _).
    1: nrapply cat_binprod_twist_corec.
    nrapply cat_binprod_swap_corec.
  Defined.

  Context (unit : A) `{!IsTerminal unit}.

  Local Instance right_unitor_binprod
    : RightUnitor (fun x y => cat_binprod x y) unit.
  Proof.
    snrapply Build_NatEquiv.
    - intros a; unfold flip.
      snrapply cate_adjointify.
      + exact cat_pr1.
      + exact (cat_binprod_corec (Id _) (mor_terminal _ _)).
      + exact (cat_binprod_beta_pr1 _ _).
      + nrapply cat_binprod_eta_pr.
        * nrefine (cat_assoc_opp _ _ _ $@ (cat_binprod_beta_pr1 _ _ $@R _) $@ _).
          exact (cat_idl _ $@ (cat_idr _)^$).
        * nrefine (cat_assoc_opp _ _ _ $@ (cat_binprod_beta_pr2 _ _ $@R _) $@ _).
          exact ((mor_terminal_unique _ _ _)^$ $@ mor_terminal_unique _ _ _).
    - snrapply Build_Is1Natural.
      intros a b f.
      refine ((_ $@R _) $@ _ $@ (_ $@L _^$)).
      1,3: nrapply cate_buildequiv_fun.
      nrapply cat_binprod_beta_pr1.
  Defined.

  Local Existing Instance left_unitor_twist.

  Local Instance triangle_binprod
    : TriangleIdentity (fun x y => cat_binprod x y) unit.
  Proof.
    snrapply triangle_twist.
    intros a b.
    refine (fmap02 _ _ _ $@ _ $@ ((_ $@L fmap02 _ _ _^$) $@R _)).
    1,3: nrapply cate_buildequiv_fun.
    nrapply cat_binprod_eta_pr.
    - nrefine (cat_pr1_fmap01_binprod _ _ $@ _ $@ cat_assoc _ _ _).
      refine (_ $@ (((_^$ $@R _) $@ cat_assoc _ _ _) $@R _)).
      2: nrapply cat_binprod_beta_pr1.
      refine ((_ $@R _) $@ _)^$.
      1: nrapply cat_pr2_fmap01_binprod.
      nrapply cat_binprod_pr1_pr2_twist.
    - nrefine (cat_pr2_fmap01_binprod _ _ $@ _ $@ cat_assoc _ _ _).
      refine (_ $@ (((cat_binprod_beta_pr2 _ _)^$ $@R _) $@ cat_assoc _ _ _ $@R _)).
      refine ((_ $@R _) $@ _)^$.
      1: nrapply cat_pr1_fmap01_binprod.
      nrapply cat_binprod_beta_pr1.
  Defined.

  Local Instance pentagon_binprod
    : PentagonIdentity (fun x y => cat_binprod x y).
  Proof.
    intros a b c d.
    nrapply cat_binprod_eta_pr_xx_x.
    - nrefine (cat_assoc_opp _ _ _ $@ (_ $@R _) $@ _).
      1: nrapply cat_pr1_pr1_associator_binprod.
      refine (_ $@ (_ $@L ((((_^$ $@R _) $@ cat_assoc _ _ _) $@R _)
        $@ cat_assoc _ _ _)) $@ cat_assoc_opp _ _ _).
      2: nrapply cat_pr1_fmap10_binprod.
      do 2 nrefine (_ $@ (_ $@L cat_assoc_opp _ _ _)).
      nrapply cat_binprod_eta_pr.
      + nrefine (cat_assoc_opp _ _ _ $@ _ $@ cat_assoc _ _ _).
        refine (_ $@ _ $@ (_^$ $@R _) $@ cat_assoc _ _ _).
        1,3: nrapply cat_pr1_pr1_associator_binprod.
        do 2 nrefine (_ $@ cat_assoc _ _ _).
        refine (_^$ $@ (_^$ $@R _)).
        2: nrapply cat_pr1_pr1_associator_binprod.
        nrapply cat_pr1_fmap01_binprod.
      + nrefine (cat_assoc_opp _ _ _ $@ _ $@ cat_assoc _ _ _).
        refine (_ $@ _ $@ (_^$ $@R _) $@ cat_assoc _ _ _).
        1,3: nrapply cat_pr2_pr1_associator_binprod.
        do 2 nrefine (_ $@ cat_assoc _ _ _).
        refine (_ $@ ((cat_assoc _ _ _ $@ (_ $@L (_^$ $@ cat_assoc _ _ _))
          $@ cat_assoc_opp _ _ _ $@ cat_assoc_opp _ _ _) $@R _)).
        2: nrapply cat_pr2_pr1_associator_binprod.
        refine (_^$ $@ (_ $@L _^$) $@ cat_assoc_opp _ _ _).
        2: nrapply cat_pr2_fmap01_binprod.
        nrefine (cat_assoc_opp _ _ _ $@ (_ $@R _)).
        nrapply cat_pr1_pr1_associator_binprod.
    - nrefine (cat_assoc_opp _ _ _ $@ (_ $@R _) $@ _).
      1: nrapply cat_pr2_pr1_associator_binprod.
      nrefine (cat_assoc _ _ _ $@ _ $@ cat_assoc_opp _ _ _).
      nrefine ((_ $@L cat_pr2_associator_binprod _ _ _) $@ _).
      refine (_ $@ (_ $@L ((((_^$ $@R _) $@ cat_assoc _ _ _) $@R _) $@ cat_assoc _ _ _))).
      2: nrapply cat_pr1_fmap10_binprod.
      nrefine (_ $@ (_ $@L (cat_assoc_opp _ _ _ $@ cat_assoc_opp _ _ _))).
      refine (_ $@ (_^$ $@R _) $@ cat_assoc _ _ _).
      2: nrapply cat_pr2_associator_binprod.
      refine (_ $@ (_ $@L ((_^$ $@R _) $@ cat_assoc _ _ _ $@ cat_assoc _ _ _)) $@ cat_assoc_opp _ _ _).
      2: nrapply cat_pr2_pr1_associator_binprod.
      refine (_ $@ (_ $@L ((_ $@L _^$) $@ cat_assoc_opp _ _ _))).
      2: nrapply cat_pr2_fmap01_binprod.
      refine (cat_assoc_opp _ _ _ $@ (_^$ $@R _) $@ cat_assoc _ _ _ $@ cat_assoc _ _ _).
      nrapply cat_pr2_pr1_associator_binprod.
    - nrefine (cat_assoc_opp _ _ _ $@ (cat_pr2_associator_binprod _ _ _ $@R _) $@ _).
      nrefine (cat_assoc _ _ _ $@ (_ $@L (cat_pr2_associator_binprod _ _ _)) $@ _).
      refine (_ $@ (_^$ $@R _) $@ cat_assoc _ _ _ $@ (_ $@L (cat_assoc_opp _ _ _))).
      2: nrapply cat_pr2_fmap10_binprod.
      refine (_ $@ cat_assoc_opp _ _ _ $@ (_^$ $@R _) $@ cat_assoc _ _ _).
      2: nrapply cat_pr2_associator_binprod.
      refine (cat_assoc_opp _ _ _ $@ (_^$ $@R _) $@ cat_assoc _ _ _
        $@ (_ $@L (cat_pr2_fmap01_binprod _ _)^$)).
      nrapply cat_pr2_associator_binprod.
  Defined.

  Local Instance hexagon_identity
    : HexagonIdentity (fun x y => cat_binprod x y).
  Proof.
    intros a b c.
    nrefine (cat_assoc _ _ _ $@ _ $@ cat_assoc_opp _ _ _).
    nrapply cat_binprod_eta_pr.
    { nrefine (cat_assoc_opp _ _ _ $@ (cat_pr1_fmap10_binprod _ _ $@R _) $@ _).
      nrefine (cat_assoc _ _ _ $@ _).
      nrapply cat_binprod_eta_pr.
      { nrefine (cat_assoc_opp _ _ _ $@ _ $@ cat_assoc _ _ _ $@ cat_assoc _ _ _).
        refine ((_ $@R _) $@ _ $@ (_^$ $@R _)).
        1: nrapply cat_binprod_beta_pr1.
        2: nrapply cat_pr1_pr1_associator_binprod.
        nrefine (cat_assoc_opp _ _ _ $@ cat_assoc_opp _ _ _ $@ _ $@ cat_assoc _ _ _).
        refine ((_ $@R _) $@ _ $@ (_^$ $@R _)).
        1: nrapply cat_pr2_pr1_associator_binprod.
        2: nrapply cat_binprod_beta_pr1.
        refine (cat_assoc _ _ _ $@ (_ $@L _) $@ cat_assoc_opp _ _ _ $@ (_ $@R _) $@ _^$).
        1: nrapply cat_pr2_fmap01_binprod.
        2: nrapply cat_pr2_associator_binprod.
        nrapply cat_binprod_beta_pr1. }
      nrefine (cat_assoc_opp _ _ _ $@ _ $@ cat_assoc _ _ _ $@ cat_assoc _ _ _).
      refine ((_ $@R _) $@ _ $@ (_^$ $@R _)).
      1: nrapply cat_binprod_beta_pr2.
      2: nrapply cat_pr2_pr1_associator_binprod.
      nrefine (cat_assoc_opp _ _ _ $@ cat_assoc_opp _ _ _ $@ _ $@ cat_assoc _ _ _).
      refine ((_ $@R _) $@ _ $@ (((_ $@L _^$) $@ cat_assoc_opp _ _ _) $@R _)).
      1: nrapply cat_pr1_pr1_associator_binprod.
      2: nrapply cat_binprod_beta_pr2.
      refine (cat_pr1_fmap01_binprod _ _ $@ _^$).
      nrapply cat_pr1_pr1_associator_binprod. }
    nrefine (cat_assoc_opp _ _ _ $@ _ $@ cat_assoc _ _ _ $@ cat_assoc _ _ _).
    refine ((_ $@R _) $@ _ $@ ((_^$ $@R _) $@R _)).
    1: nrapply cat_pr2_fmap10_binprod.
    2: nrapply cat_pr2_associator_binprod.
    nrefine (cat_assoc_opp _ _ _ $@ (cat_pr2_associator_binprod _ _ _ $@R _) $@ _).
    nrefine (cat_assoc _ _ _ $@ (_ $@L _) $@ _ $@ (cat_assoc_opp _ _ _ $@R _)).
    1: nrapply cat_pr2_fmap01_binprod.
    refine (cat_assoc_opp _ _ _ $@ (_ $@R _) $@ _^$ $@ ((_ $@L _^$) $@R _)).
    1,3: nrapply cat_binprod_beta_pr2.
    nrapply cat_pr2_pr1_associator_binprod.
  Defined.

  Global Instance ismonoidal_cat_binprod
    : IsMonoidal A (fun x y => cat_binprod x y) unit
    := {}.

  Global Instance issymmetricmonoidal_cat_binprod
    : IsSymmetricMonoidal A (fun x y => cat_binprod x y) unit
    := {}.

End Associativity.

(** *** Products in Type *)

(** Since we use the Yoneda lemma in this file, we therefore depend on WildCat.Universe which means these instances have to live here. *)
Global Instance hasbinaryproducts_type : HasBinaryProducts Type.
Proof.
  intros X Y.
  snrapply Build_BinaryProduct.
  - exact (X * Y).
  - exact fst.
  - exact snd.
  - intros Z f g z. exact (f z, g z).
  - reflexivity.
  - reflexivity.
  - intros Z f g p q x.
    nrapply path_prod.
    + exact (p x).
    + exact (q x).
Defined.

(** Assuming [Funext], [Type] has all products. *)
Global Instance hasallproducts_type `{Funext} : HasAllProducts Type.
Proof.
  intros I x.
  snrapply Build_Product.
  - exact (forall (i : I), x i).
  - intros i f. exact (f i).
  - intros A f a i. exact (f i a).
  - reflexivity.
  - intros A f g p a.
    exact (path_forall _ _ (fun i => p i a)).
Defined.
