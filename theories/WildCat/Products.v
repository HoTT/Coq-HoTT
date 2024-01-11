Require Import Basics EquivGpd Types.Prod.
Require Import WildCat.Core WildCat.ZeroGroupoid WildCat.Equiv WildCat.Yoneda WildCat.Universe WildCat.NatTrans WildCat.Opposite.

(** * Categories with products *)

(* TODO: jdchristensen: There's a more general result, that given any two maps A -> B and A -> C of 0-groupoids, there's a map A -> prop_0gpd B C of 0-groupoids. Then this lemma is that general result applied to is0functor_yon_0gpd of the two projections. *)
Definition cat_prod_corec_inv {A : Type} `{Is1Cat A}
  (xy x y z : A) (pr1 : xy $-> x) (pr2 : xy $-> y)
  : yon_0gpd xy z $-> prod_0gpd (yon_0gpd x z) (yon_0gpd y z).
Proof.
  snrapply Build_Morphism_0Gpd.
  - simpl; intros f.
    exact (pr1 $o f, pr2 $o f).
  - snrapply Build_Is0Functor.
    simpl; intros f g p; split.
    + exact (pr1 $@L p).
    + exact (pr2 $@L p).
Defined.

(* A binary product of two objects of a category is an object of the category with a pair of projections such that the induced map is an equivalence. *) 
Class BinaryProduct {A : Type} `{Is1Cat A} {x y : A} := Build_BinaryProduct' {
  cat_prod : A;
  cat_pr1 : cat_prod $-> x;
  cat_pr2 : cat_prod $-> y;
  cat_isequiv_cat_prod_corec_inv
    :: forall z, CatIsEquiv (cat_prod_corec_inv cat_prod x y z cat_pr1 cat_pr2);  
}.

Arguments BinaryProduct {A _ _ _ _} x y.
Arguments cat_prod {A _ _ _ _} x y {_}.

(** This is a convenience wrapper for building BinaryProducts *)
Definition Build_BinaryProduct {A : Type} `{Is1Cat A} {x y : A}
  (cat_prod : A) (cat_pr1 : cat_prod $-> x) (cat_pr2 : cat_prod $-> y)
  (cat_prod_corec : forall z : A, (z $-> x) -> (z $-> y) -> (z $-> cat_prod))
  (cat_prod_beta_pr1 : forall z (f : z $-> x) (g : z $-> y), cat_pr1 $o cat_prod_corec z f g $== f)
  (cat_prod_beta_pr2 : forall z (f : z $-> x) (g : z $-> y), cat_pr2 $o cat_prod_corec z f g $== g)
  (cat_prod_pr_eta : forall z (f g : z $-> cat_prod), cat_pr1 $o f $== cat_pr1 $o g -> cat_pr2 $o f $== cat_pr2 $o g -> f $== g)
  : BinaryProduct x y.
Proof.
  snrapply (Build_BinaryProduct' _ _ _ _ _ _ _ cat_prod cat_pr1 cat_pr2).
  intros z.
  apply isequiv_0gpd_issurjinj.
  snrapply Build_IsSurjInj.
  - intros [f g].
    exists (cat_prod_corec z f g).
    split.
    + apply cat_prod_beta_pr1.
    + apply cat_prod_beta_pr2.
  - intros f g [p q].
    by apply cat_prod_pr_eta.
Defined.

Section Lemmata.

  Context {A : Type} {x y : A} `{BinaryProduct _ x y}.

  Definition cate_cat_prod_corec_inv {z : A}
    : (yon_0gpd (cat_prod x y) z) $<~> prod_0gpd (yon_0gpd x z) (yon_0gpd y z).
  Proof.
    srapply Build_CatEquiv.
  Defined.

  Definition cate_cat_prod_corec {z : A}
    : prod_0gpd (yon_0gpd x z) (yon_0gpd y z) $<~> (yon_0gpd (cat_prod x y) z)
    := cate_cat_prod_corec_inv^-1$.

  Definition cat_prod_corec {z : A}
    : (z $-> x) -> (z $-> y) -> (z $-> cat_prod x y).
  Proof.
    intros f g.
    apply cate_cat_prod_corec.
    exact (f, g).
  Defined.
    
  (** Applying the first projection after a map pairing gives the first map. *) 
  Lemma cat_prod_beta_pr1 {z : A} (f : z $-> x) (g : z $-> y)
    : cat_pr1 $o cat_prod_corec f g $== f.
  Proof.
    exact (fst (cate_isretr cate_cat_prod_corec_inv (f, g))).
  Defined.

  (** Applying the second projection after a map pairing gives the second map. *)
  Lemma cat_prod_beta_pr2 {z : A} (f : z $-> x) (g : z $-> y)
    : cat_pr2 $o cat_prod_corec f g $== g.
  Proof.
    exact (snd (cate_isretr cate_cat_prod_corec_inv (f, g))).
  Defined.

  (** The pairing map is the unique map that makes the following diagram commute. *)
  Lemma cat_prod_eta {z : A} (f : z $-> cat_prod x y)
    : cat_prod_corec (cat_pr1 $o f) (cat_pr2 $o f) $== f.
  Proof.
    exact (cate_issect cate_cat_prod_corec_inv f).
  Defined.

  (* TODO: decompose and move *)
  Local Instance is0functor_prod_0gpd_helper
    : Is0Functor (fun z : A^op => prod_0gpd (yon_0gpd x z) (yon_0gpd y z)).
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
  Local Instance is1functor_prod_0gpd_helper
    : Is1Functor (fun z : A^op => prod_0gpd (yon_0gpd x z) (yon_0gpd y z)).
  Proof.
    snrapply Build_Is1Functor.
    - intros a b f g p [r_fst r_snd].
      cbn; split.
      + refine (_ $@L _).
        apply p.
      + refine (_ $@L _).
        apply p.
    - intros a [r_fst r_snd].
      split; apply cat_idl.
    - intros a b c f g [r_fst r_snd].
      split; apply cat_assoc.
  Defined.
  
  Definition natequiv_cat_prod_corec_inv
    : NatEquiv (yon_0gpd (cat_prod x y)) (fun z : A^op => prod_0gpd (yon_0gpd x z) (yon_0gpd y z)).
  Proof.
    snrapply Build_NatEquiv.
    { intros a.
      apply cate_cat_prod_corec_inv. }
    exact (is1natural_yoneda_0gpd
      (cat_prod x y)
      (fun z : A^op => prod_0gpd (yon_0gpd x z) (yon_0gpd y z))
      (cat_pr1, cat_pr2)).
  Defined.

  Lemma cat_prod_corec_eta {z : A} {f f' : z $-> x} {g g' : z $-> y}
    : f $== f' -> g $== g' -> cat_prod_corec f g $== cat_prod_corec f' g'.
  Proof.
    intros p q.
    unfold cat_prod_corec.
    apply (moveL_equiv_V_0gpd cate_cat_prod_corec_inv).
    refine (cate_isretr cate_cat_prod_corec_inv _ $@ _).
    split.
    - exact p.
    - exact q.
  Defined.

  Lemma cat_prod_pr_eta {z : A} {f f' : z $-> cat_prod x y}
    : cat_pr1 $o f $== cat_pr1 $o f' -> cat_pr2 $o f $== cat_pr2 $o f' -> f $== f'.
  Proof.
    intros fst snd.
    refine ((cat_prod_eta _)^$ $@ _ $@ cat_prod_eta _).
    by apply cat_prod_corec_eta.
  Defined.

End Lemmata.

(** *** Categories with binary products *)

(** A category with binary products is a category with a binary product for each pair of objects. *)
Class HasBinaryProducts (A : Type) `{Is1Cat A} := {
  binary_products :: forall x y : A, BinaryProduct x y;
}.

(** *** Product functor *)

(** Binary products are functorial in each argument. *)

(* TODO: jdchristensen: Another approach to handling functoriality on the right is to first prove that products are symmetric. Then functoriality on the right follows from functoriality on the left... *)
Global Instance is0functor_cat_prod_l {A : Type}
  `{HasBinaryProducts A} y
  : Is0Functor (fun x => cat_prod x y).
Proof.
  snrapply Build_Is0Functor.
  intros a b f.
  apply cat_prod_corec.
  - exact (f $o cat_pr1).
  - exact cat_pr2.
Defined.

Global Instance is1functor_cat_prod_l {A : Type}
  `{HasBinaryProducts A} y
  : Is1Functor (fun x => cat_prod x y).
Proof.
  snrapply Build_Is1Functor.
  - intros a b f g p.
    simpl.
    apply cat_prod_corec_eta.
    2: apply Id.
    exact (p $@R cat_pr1).
  - intros x.
    simpl.
    apply cat_prod_pr_eta.
    + refine (cat_prod_beta_pr1 _ _ $@ _).
      exact (cat_idl _ $@ (cat_idr _)^$).
    + refine (cat_prod_beta_pr2 _ _ $@ _).
      exact (cat_idr _)^$.
  - intros x z w f g.
    simpl.
    apply cat_prod_pr_eta.
    + refine (cat_prod_beta_pr1 _ _ $@ _).
      refine (_ $@ cat_assoc _ _ _).
      refine (_ $@ ((cat_prod_beta_pr1 _ _)^$ $@R _)).
      refine (cat_assoc _ _ _ $@ (_ $@L _) $@ (cat_assoc _ _ _)^$).
      exact (cat_prod_beta_pr1 _ _)^$.
    + refine (cat_prod_beta_pr2 _ _ $@ _).
      refine (_ $@ cat_assoc _ _ _).
      refine (_ $@ ((cat_prod_beta_pr2 _ _)^$ $@R _)).
      exact (cat_prod_beta_pr2 _ _)^$.
Defined.

Global Instance is0functor_cat_prod_r {A : Type}
  `{HasBinaryProducts A} x
  : Is0Functor (fun y => cat_prod x y).
Proof.
  snrapply Build_Is0Functor.
  intros a b f.
  apply cat_prod_corec.
  - exact cat_pr1.
  - exact (f $o cat_pr2).
Defined.

Global Instance is1functor_cat_prod_r {A : Type}
  `{HasBinaryProducts A} x
  : Is1Functor (fun y => cat_prod x y).
Proof.
  snrapply Build_Is1Functor.
  - intros y z f g p.
    apply cat_prod_corec_eta.
    1: apply Id.
    exact (p $@R cat_pr2).
  - intros y. simpl.
    refine (_ $@ cat_prod_eta _).
    apply cat_prod_corec_eta.
    + symmetry.
      apply cat_idr.
    + exact (cat_idl _ $@ (cat_idr _)^$).
  - intros y z w f g.
    simpl.
    apply cat_prod_pr_eta.
    + refine (cat_prod_beta_pr1 _ _ $@ _).
      refine (_ $@ cat_assoc _ _ _).
      refine (_ $@ ((cat_prod_beta_pr1 _ _)^$ $@R _)).
      exact (cat_prod_beta_pr1 _ _)^$.    
    + refine (cat_prod_beta_pr2 _ _ $@ _).
      refine (_ $@ cat_assoc _ _ _).
      refine (_ $@ ((cat_prod_beta_pr2 _ _)^$ $@R _)).
      refine (_ $@ (cat_assoc _ _ _)^$).
      refine (cat_assoc _ _ _ $@ _).
      exact (_ $@L cat_prod_beta_pr2 _ _)^$.
Defined.

(** [cat_prod_corec] is also functorial in each morphsism. *)

Global Instance is0functor_cat_prod_corec_l {A : Type}
  `{HasBinaryProducts A} {x y z : A} (g : z $-> y)
  : Is0Functor (fun f : z $-> y => cat_prod_corec f g).
Proof.
  snrapply Build_Is0Functor.
  intros f f' p.
  by apply cat_prod_corec_eta.
Defined.

Global Instance is0functor_cat_prod_corec_r {A : Type}
  `{HasBinaryProducts A} {x y z : A} (f : z $-> x)
  : Is0Functor (fun g : z $-> x => cat_prod_corec f g).
Proof.
  snrapply Build_Is0Functor.
  intros g h p.
  by apply cat_prod_corec_eta.
Defined.

(** Since we use the Yoneda lemma in this file, we therefore depend on WildCat.Universe which means this instance has to therefore live here. *)
Global Instance hasbinaryproducts_type : HasBinaryProducts Type.
Proof.
  snrapply Build_HasBinaryProducts.
  intros X Y.
  snrapply Build_BinaryProduct.
  - exact (X * Y).
  - exact fst.
  - exact snd.
  - intros Z f g z. exact (f z, g z).
  - reflexivity.
  - reflexivity.
  - intros Z f g p q x.
    apply path_prod.
    + exact (p x).
    + exact (q x).
Defined.
