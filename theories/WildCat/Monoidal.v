Require Import Basics.Overture Basics.Tactics Types.Forall.
Require Import WildCat.Core WildCat.Bifunctor WildCat.Prod WildCat.Equiv.
Require Import WildCat.NatTrans WildCat.Opposite.

(** * Monoidal Categories *)

(** In this file we define monoidal categories and symmetric monoidal categories. *)

(** ** Typeclasses for common diagrams *)

(** TODO: These should eventually be moved to a separate file in WildCat and used in other places. They can be thought of as a wildcat generalization of the classes in canonical_names.v *)

(** *** Associators *)

Class Associator {A : Type} `{HasEquivs A}
  (F : A -> A -> A) `{!Is0Bifunctor F, !Is1Bifunctor F}
  := associator_uncurried
    : NatEquiv (fun '(a, b, c) => F a (F b c)) (fun '(a, b, c) => F (F a b) c).

Arguments associator_uncurried {A _ _ _ _ _ F _ _ _}.

Definition associator {A : Type} `{HasEquivs A} {F : A -> A -> A}
  `{!Is0Bifunctor F, !Is1Bifunctor F, !Associator F}
  : forall a b c, F a (F b c) $<~> F (F a b) c
  := fun a b c => associator_uncurried (a, b, c).
Coercion associator : Associator >-> Funclass.

Definition Build_Associator {A : Type} `{HasEquivs A} (F : A -> A -> A)
  `{!Is0Bifunctor F, !Is1Bifunctor F}
  (associator : forall a b c, F a (F b c) $<~> F (F a b) c)
  (isnat_assoc : Is1Natural
    (fun '(a, b, c) => F a (F b c))
    (fun '(a, b, c) => F (F a b) c)
    (fun '(a, b, c) => associator a b c))
  : Associator F.
Proof.
  snrapply Build_NatEquiv.
  - intros [[a b] c].
    exact (associator a b c).
  - exact isnat_assoc.
Defined. 

(** *** Unitors *)

Class LeftUnitor {A : Type} `{HasEquivs A}
  (F : A -> A -> A) `{!Is0Bifunctor F, !Is1Bifunctor F} (unit : A)
  (** A natural isomorphism [left_unitor] witnessing the left unit law of [F]. *)
  := left_unitor : NatEquiv (F unit) idmap.
Coercion left_unitor : LeftUnitor >-> NatEquiv.
Arguments left_unitor {A _ _ _ _ _ F _ _ unit _}.

Class RightUnitor {A : Type} `{HasEquivs A}
  (F : A -> A -> A) `{!Is0Bifunctor F, !Is1Bifunctor F} (unit : A)
  (** A natural isomorphism [right_unitor] witnessing the right unit law of [F]. *)
  := right_unitor : NatEquiv (flip F unit) idmap.
Coercion right_unitor : RightUnitor >-> NatEquiv.
Arguments right_unitor {A _ _ _ _ _ F _ _ unit _}.

(** *** Triangle and Pentagon identities *)

Class TriangleIdentity {A : Type} `{HasEquivs A}
  (F : A -> A -> A) `{!Is0Bifunctor F, !Is1Bifunctor F, !Associator F}
  (unit : A) `{!LeftUnitor F unit, !RightUnitor F unit}
  (** The triangle identity for an associator and unitors. *)
  := triangle_identity a b
    : fmap01 F a (left_unitor b)
    $== fmap10 F (right_unitor a) b $o (associator (F := F) a unit b).
Coercion triangle_identity : TriangleIdentity >-> Funclass.
Arguments triangle_identity {A _ _ _ _ _} F {_ _ _} unit {_}.

Class PentagonIdentity {A : Type} `{HasEquivs A}
  (F : A -> A -> A) `{!Is0Bifunctor F, !Is1Bifunctor F, !Associator F}
  (** The pentagon identity for an associator. *)
  := pentagon_identity a b c d
    : associator (F a b) c d $o associator a b (F c d)
      $== fmap10 F (associator a b c) d $o associator a (F b c) d
        $o fmap01 F a (associator b c d).
Coercion pentagon_identity : PentagonIdentity >-> Funclass.
Arguments pentagon_identity {A _ _ _ _ _} F {_ _ _}.

(** *** Braiding *)

Class Braiding {A : Type} `{Is1Cat A}
  (F : A -> A -> A) `{!Is0Bifunctor F, !Is1Bifunctor F}
  := braid_uncurried : NatTrans (uncurry F) (uncurry (flip F)).

Arguments braid_uncurried {A _ _ _ _ F _ _ _}.
    
Definition braid {A : Type} `{Is1Cat A} {F : A -> A -> A}
  `{!Is0Bifunctor F, !Is1Bifunctor F, !Braiding F}
  : forall a b, F a b $-> F b a
  := fun a b => braid_uncurried (a, b).
Coercion braid : Braiding >-> Funclass.

Class SymmetricBraiding {A : Type} `{Is1Cat A}
  (F : A -> A -> A) `{!Is0Bifunctor F, !Is1Bifunctor F} := {
  braiding_symmetricbraiding :: Braiding F;
  braid_braid : forall a b, braid a b $o braid b a $== Id (F b a);
}.
(** We could have used [::>] in [braiding_symmetricbraiding] instead however due to bug https://github.com/coq/coq/issues/18971 the coercion isn't registered, so we have to register it manually instead. *)
Coercion braiding_symmetricbraiding : SymmetricBraiding >-> Braiding.
Arguments braid_braid {A _ _ _ _ F _ _ _} a b.

(** *** Hexagon identity *)

Class HexagonIdentity {A : Type} `{HasEquivs A}
  (F : A -> A -> A)
  `{!Is0Bifunctor F, !Is1Bifunctor F, !Associator F, !Braiding F}
  (** The hexagon identity for an associator and a braiding. *)
  := hexagon_identity a b c
    : fmap10 F (braid b a) c $o associator b a c $o fmap01 F b (braid c a)
      $== associator a b c $o braid (F b c) a $o associator b c a.
Coercion hexagon_identity : HexagonIdentity >-> Funclass.
Arguments hexagon_identity {A _ _ _ _ _} F {_ _}.

(** ** Monoidal Categories *)

(** A monoidal 1-category is a 1-category with equivalences together with the following: *)
Class IsMonoidal (A : Type) `{HasEquivs A}
  (** It has a binary operation [cat_tensor] called the tensor product. *)
  (cat_tensor : A -> A -> A)
  (** It has a unit object [cat_tensor_unit] called the tensor unit. *)
  (cat_tensor_unit : A)
  (** These all satisfy the following properties: *)
  := {
  (** A [cat_tensor] is a 1-bifunctor. *)
  is0bifunctor_cat_tensor : Is0Bifunctor cat_tensor;
  is1bifunctor_cat_tensor : Is1Bifunctor cat_tensor;
  (** A natural isomorphism [associator] witnessing the associativity of the tensor product. *)
  cat_tensor_associator :: Associator cat_tensor;
  (** A natural isomorphism [left_unitor] witnessing the left unit law. *)
  cat_tensor_left_unitor :: LeftUnitor cat_tensor cat_tensor_unit;
  (** A natural isomorphism [right_unitor] witnessing the right unit law. *)
  cat_tensor_right_unitor :: RightUnitor cat_tensor cat_tensor_unit;
  (** The triangle identity. *)
  cat_tensor_triangle_identity :: TriangleIdentity cat_tensor cat_tensor_unit;
  (** The pentagon identity. *)
  cat_tensor_pentagon_identity :: PentagonIdentity cat_tensor;
}.

Existing Instance is0bifunctor_cat_tensor | 10.
Existing Instance is1bifunctor_cat_tensor | 10.

(** TODO: Braided monoidal categories *)

(** ** Symmetric Monoidal Categories *)

(** A symmetric monoidal 1-category is a 1-category with equivalences together with the following: *)
Class IsSymmetricMonoidal (A : Type) `{HasEquivs A}
  (** A binary operation [cat_tensor] called the tensor product. *)
  (cat_tensor : A -> A -> A)
  (** A unit object [cat_tensor_unit] called the tensor unit. *)
  (cat_tensor_unit : A)
  := {
  (** A monoidal structure with [cat_tensor] and [cat_tensor_unit]. *)
  issymmetricmonoidal_ismonoidal :: IsMonoidal A cat_tensor cat_tensor_unit;
  (** A natural transformation [braid] witnessing the symmetry of the tensor product such that [braid] is its own inverse. *)
  cat_symm_tensor_braiding :: SymmetricBraiding cat_tensor;
  (** The hexagon identity. *)
  cat_symm_tensor_hexagon :: HexagonIdentity cat_tensor;
}.

(** *** Theory about [Associator] *)

Section Associator.
  Context {A : Type} `{HasEquivs A} {F : A -> A -> A}
    `{!Is0Bifunctor F, !Is1Bifunctor F, assoc : !Associator F}.

  Definition associator_nat {x x' y y' z z'}
    (f : x $-> x') (g : y $-> y') (h : z $-> z')
    : associator x' y' z' $o fmap11 F f (fmap11 F g h)
      $== fmap11 F (fmap11 F f g) h $o associator x y z.
  Proof.
    destruct assoc as [asso nat].
    exact (nat (x, y, z) (x', y', z') (f, g, h)).
  Defined.

  Definition associator_nat_l {x x' : A} (f : x $-> x') (y z : A)
    : associator x' y z $o fmap10 F f (F y z)
      $== fmap10 F (fmap10 F f y) z $o associator x y z.
  Proof.
    refine ((_ $@L _^$) $@ _ $@ (_ $@R _)).
    2: rapply (associator_nat f (Id _) (Id _)).
    - exact (fmap12 _ _ (fmap11_id _ _ _) $@ fmap10_is_fmap11 _ _ _).
    - exact (fmap21 _ (fmap10_is_fmap11 _ _ _) _ $@ fmap10_is_fmap11 _ _ _).
  Defined.

  Definition associator_nat_m (x : A) {y y' : A} (g : y $-> y') (z : A)
    : associator x y' z $o fmap01 F x (fmap10 F g z)
      $== fmap10 F (fmap01 F x g) z $o associator x y z.
  Proof.
    refine ((_ $@L _^$) $@ _ $@ (_ $@R _)).
    2: nrapply (associator_nat (Id _) g (Id _)).
    - exact (fmap12 _ _ (fmap10_is_fmap11 _ _ _) $@ fmap01_is_fmap11 _ _ _).
    - exact (fmap21 _ (fmap01_is_fmap11 _ _ _) _ $@ fmap10_is_fmap11 _ _ _).
  Defined.

  Definition associator_nat_r (x y : A) {z z' : A} (h : z $-> z')
    : associator x y z' $o fmap01 F x (fmap01 F y h)
      $== fmap01 F (F x y) h $o associator x y z.
  Proof.
    refine ((_ $@L _^$) $@ _ $@ (_ $@R _)).
    2: nrapply (associator_nat (Id _) (Id _) h).
    - exact (fmap12 _ _ (fmap01_is_fmap11 _ _ _) $@ fmap01_is_fmap11 _ _ _).
    - exact (fmap21 _ (fmap11_id _ _ _) _ $@ fmap01_is_fmap11 F _ _).
  Defined.

  Global Instance associator_op : Associator (A:=A^op) F
    := natequiv_inverse (natequiv_op assoc).

End Associator.

Definition associator_op' {A : Type} `{HasEquivs A} {F : A -> A -> A}
  `{!Is0Bifunctor F, !Is1Bifunctor F, assoc : !Associator (A:=A^op) F}
  : Associator F
  := associator_op (A:=A^op) (assoc := assoc).

(** ** Theory about [LeftUnitor] and [RightUnitor] *)

Section LeftUnitor.
  Context {A : Type} `{HasEquivs A} {F : A -> A -> A} (unit : A)
    `{!Is0Bifunctor F, !Is1Bifunctor F, !LeftUnitor F unit, !RightUnitor F unit}.

  Global Instance left_unitor_op : LeftUnitor (A:=A^op) F unit
    := natequiv_inverse (natequiv_op left_unitor).
  
  Global Instance right_unitor_op : RightUnitor (A:=A^op) F unit
    := natequiv_inverse (natequiv_op right_unitor).

End LeftUnitor.

(** ** Theory about [Braiding] *)

Global Instance braiding_op {A : Type} `{HasEquivs A} {F : A -> A -> A}
  `{!Is0Bifunctor F, !Is1Bifunctor F, braid : !Braiding F}
  : Braiding (A:=A^op) F
  := nattrans_op (nattrans_flip braid).

Definition braiding_op' {A : Type} `{HasEquivs A} {F : A -> A -> A}
  `{!Is0Bifunctor F, !Is1Bifunctor F, braid : !Braiding (A:=A^op) F}
  : Braiding F
  := braiding_op (A:=A^op) (braid := braid).

(** ** Theory about [SymmetricBraid] *)

Section SymmetricBraid.
  Context {A : Type} {F : A -> A -> A} `{SymmetricBraiding A F, !HasEquivs A}.

  (** [braid] is its own inverse and therefore an equivalence. *)
  Instance catie_braid a b : CatIsEquiv (braid a b)
    := catie_adjointify (braid a b) (braid b a) (braid_braid a b) (braid_braid b a).

  (** [braide] is the bundled equivalence whose underlying map is [braid]. *)
  Definition braide a b
    : F a b $<~> F b a
    := Build_CatEquiv (braid a b).

  Definition moveL_braidL a b c f (g : c $-> _)
    : braid a b $o f $== g -> f $== braid b a $o g.
  Proof.
    intros p.
    apply (cate_monic_equiv (braide a b)).
    refine ((cate_buildequiv_fun _ $@R _) $@ p $@ _ $@ cat_assoc _ _ _).
    refine ((cat_idl _)^$ $@ (_^$ $@R _)).
    refine ((cate_buildequiv_fun _ $@R _) $@ _).
    apply braid_braid.
  Defined.

  Definition moveL_braidR a b c f (g : _ $-> c)
    : f $o braid a b $== g -> f $== g $o braid b a.
  Proof.
    intros p.
    apply (cate_epic_equiv (braide a b)).
    refine (_ $@ (cat_assoc _ _ _)^$).
    refine (_ $@ (_ $@L ((_ $@L cate_buildequiv_fun _) $@ _)^$)).
    2: apply braid_braid.
    refine ((_ $@L _) $@ _ $@ (cat_idr _)^$).
    1: apply cate_buildequiv_fun.
    exact p.
  Defined.

  Definition moveR_braidL a b c f (g : c $-> _)
    : f $== braid b a $o g -> braid a b $o f $== g.
  Proof.
    intros p; symmetry; apply moveL_braidL; symmetry; exact p.
  Defined.

  Definition moveR_braidR a b c f (g : _ $-> c)
    : f $== g $o braid b a -> f $o braid a b $== g.
  Proof.
    intros p; symmetry; apply moveL_braidR; symmetry; exact p.
  Defined.

  Definition moveL_fmap01_braidL a b c d f (g : d $-> _)
    : fmap01 F a (braid b c) $o f $== g
      -> f $== fmap01 F a (braid c b) $o g.
  Proof.
    intros p.
    apply (cate_monic_equiv (emap01 F a (braide b c))).
    refine (_ $@ cat_assoc _ _ _).
    refine (_ $@ (_ $@R _)).
    2: { refine (_ $@ (_^$ $@R _)).
      2: apply cate_buildequiv_fun.
      refine ((fmap_id _ _)^$ $@ fmap2 _ _ $@ fmap_comp _ _ _).
      refine ((_ $@R _) $@ _)^$.
      1: apply cate_buildequiv_fun.
      apply braid_braid. }
    refine ((_ $@R _) $@ p $@ (cat_idl _)^$).
    refine (_ $@ fmap2 _ _);
    apply cate_buildequiv_fun.
  Defined.

  Definition moveL_fmap01_braidR a b c d f (g : _ $-> d)
    :  f $o fmap01 F a (braid b c) $== g
      -> f $== g $o fmap01 F a (braid c b).
  Proof.
    intros p.
    apply (cate_epic_equiv (emap01 F a (braide b c))).
    refine (_ $@ (cat_assoc _ _ _)^$).
    refine (_ $@ (_ $@L _)).
    2: { refine (_^$ $@ (_ $@L _^$)).
      2: apply cate_buildequiv_fun.
      refine ((fmap_comp _ _ _)^$ $@ fmap2 _ _ $@ fmap_id _ _).
      refine ((_ $@L _) $@ _).
      1: apply cate_buildequiv_fun.
      apply braid_braid. }
    refine ((_ $@L _) $@ p $@ (cat_idr _)^$).
    refine (_ $@ fmap2 _ _);
    apply cate_buildequiv_fun.
  Defined.

  Definition moveR_fmap01_braidL a b c d f (g : d $-> _)
    : f $== fmap01 F a (braid c b) $o g
      -> fmap01 F a (braid b c) $o f $== g.
  Proof.
    intros p; symmetry; apply moveL_fmap01_braidL; symmetry; exact p.
  Defined.

  Definition moveR_fmap01_braidR a b c d f (g : _ $-> d)
    : f $== g $o fmap01 F a (braid c b)
      -> f $o fmap01 F a (braid b c) $== g.
  Proof.
    intros p; symmetry; apply moveL_fmap01_braidR; symmetry; exact p.
  Defined.

  Definition moveL_fmap01_fmap01_braidL a b c d e f (g : e $-> _)
    : fmap01 F a (fmap01 F b (braid c d)) $o f $== g
      -> f $== fmap01 F a (fmap01 F b (braid d c)) $o g.
  Proof.
    intros p.
    apply (cate_monic_equiv (emap01 F a (emap01 F b (braide c d)))).
    refine (_ $@ cat_assoc _ _ _).
    refine (_ $@ (_ $@R _)).
    2: { refine (_ $@ (_^$ $@R _)).
      2: apply cate_buildequiv_fun.
      refine ((fmap_id _ _)^$ $@ fmap2 _ _ $@ fmap_comp _ _ _).
      refine (_ $@ (_^$ $@R _)).
      2: apply cate_buildequiv_fun.
      refine ((fmap_id _ _)^$ $@ fmap2 _ _ $@ fmap_comp _ _ _).
      refine ((_ $@R _) $@ _)^$.
      1: apply cate_buildequiv_fun.
      apply braid_braid. }
    refine ((_ $@R _) $@ p $@ (cat_idl _)^$).
    refine (cate_buildequiv_fun _ $@ fmap02 _ _ _).
    refine (cate_buildequiv_fun _ $@ fmap02 _ _ _).
    apply cate_buildequiv_fun.
  Defined.

  Definition moveL_fmap01_fmap01_braidR a b c d e f (g : _ $-> e)
    : f $o fmap01 F a (fmap01 F b (braid c d)) $== g
      -> f $== g $o fmap01 F a (fmap01 F b (braid d c)).
  Proof.
    intros p.
    apply (cate_epic_equiv (emap01 F a (emap01 F b (braide c d)))).
    refine (_ $@ (cat_assoc _ _ _)^$).
    refine (_ $@ (_ $@L _)).
    2: { refine (_^$ $@ (_ $@L _^$)).
      2: apply cate_buildequiv_fun.
      refine ((fmap_comp _ _ _)^$ $@ fmap2 _ _ $@ fmap_id _ _).
      refine ((_ $@L _) $@ _).
      1: apply cate_buildequiv_fun.
      refine ((fmap_comp _ _ _)^$ $@ fmap2 _ _ $@ fmap_id _ _).
      refine ((_ $@L _) $@ _).
      1: apply cate_buildequiv_fun.
      apply braid_braid. }
    refine ((_ $@L _) $@ p $@ (cat_idr _)^$).
    refine (cate_buildequiv_fun _ $@ fmap02 _ _ _).
    refine (cate_buildequiv_fun _ $@ fmap02 _ _ _).
    apply cate_buildequiv_fun.
  Defined.

  Definition moveR_fmap01_fmap01_braidL a b c d e f (g : e $-> _)
    : f $== fmap01 F a (fmap01 F b (braid d c)) $o g
      -> fmap01 F a (fmap01 F b (braid c d)) $o f $== g.
  Proof.
    intros p; symmetry; apply moveL_fmap01_fmap01_braidL; symmetry; exact p.
  Defined.

  Definition moveR_fmap01_fmap01_braidR a b c d e f (g : _ $-> e)
    : f $== g $o fmap01 F a (fmap01 F b (braid d c))
      -> f $o fmap01 F a (fmap01 F b (braid c d)) $== g.
  Proof.
    intros p; symmetry; apply moveL_fmap01_fmap01_braidR; symmetry; exact p.
  Defined.

  Definition braid_nat {a b c d} (f : a $-> c) (g : b $-> d)
    : braid c d $o fmap11 F f g $== fmap11 F g f $o braid a b.
  Proof.
    exact (isnat braid_uncurried (a := (a, b)) (a' := (c, d)) (f, g)).
  Defined.

  Definition braid_nat_l {a b c} (f : a $-> b)
    : braid b c $o fmap10 F f c $== fmap01 F c f $o braid a c.
  Proof.
    refine ((_ $@L (fmap10_is_fmap11 _ _ _)^$) $@ _ $@ (fmap01_is_fmap11 _ _ _ $@R _)).
    exact (isnat braid_uncurried (a := (a, c)) (a' := (b, c)) (f, Id _)).
  Defined.

  (** This is just the inverse of above. *)
  Definition braid_nat_r {a b c} (g : b $-> c)
    : braid a c $o fmap01 F a g $== fmap10 F g a $o braid a b.
  Proof.
    refine ((_ $@L (fmap01_is_fmap11 _ _ _)^$) $@ _ $@ (fmap10_is_fmap11 _ _ _ $@R _)).
    exact (isnat braid_uncurried (a := (a, b)) (a' := (a, c)) (Id _ , g)).
  Defined.
  
  Global Instance symmetricbraiding_op : SymmetricBraiding (A:=A^op) F.
  Proof.
    snrapply Build_SymmetricBraiding.
    - exact _.
    - intros a b.
      rapply braid_braid.
  Defined.

End SymmetricBraid.

Definition symmetricbraiding_op' {A : Type} {F : A -> A -> A}
  `{HasEquivs A, !Is0Bifunctor F, !Is1Bifunctor F,
    H' : !SymmetricBraiding (A:=A^op) F}
  : SymmetricBraiding F
  := symmetricbraiding_op (A:=A^op) (F := F).

(** ** Opposite Monoidal Categories *)

Global Instance ismonoidal_op {A : Type} (tensor : A -> A -> A) (unit : A)
  `{IsMonoidal A tensor unit}
  : IsMonoidal A^op tensor unit.
Proof.
  snrapply Build_IsMonoidal.
  1-5: exact _.
  - intros a b; unfold op in a, b; simpl.
    refine (_^$ $@ _ $@ (_ $@L _)).
    1,3: exact (emap_inv _ _ $@ cate_buildequiv_fun _).
    nrefine (cate_inv2 _ $@ cate_inv_compose' _ _).
    refine (cate_buildequiv_fun _ $@ _ $@ ((cate_buildequiv_fun _)^$ $@R _)
      $@ (cate_buildequiv_fun _)^$).
    rapply cat_tensor_triangle_identity.
  - intros a b c d; unfold op in a, b, c, d; simpl.
    refine (_ $@ ((_ $@L _) $@@ _)).
    2,3: exact (emap_inv _ _ $@ cate_buildequiv_fun _).
    refine ((cate_inv_compose' _ _)^$ $@ cate_inv2 _ $@ cate_inv_compose' _ _
      $@ (_ $@L cate_inv_compose' _ _)). 
    refine (cate_buildequiv_fun _ $@ _ $@ ((cate_buildequiv_fun _)^$ $@R _)
      $@ (cate_buildequiv_fun _)^$).
    refine (_ $@ (cate_buildequiv_fun _ $@@ (cate_buildequiv_fun _ $@R _))^$).
    rapply cat_tensor_pentagon_identity.
Defined.

Definition ismonoidal_op' {A : Type} (tensor : A -> A -> A) (unit : A)
  `{HasEquivs A} `{!IsMonoidal A^op tensor unit}
  : IsMonoidal A tensor unit
  := ismonoidal_op (A:=A^op) tensor unit.

Global Instance issymmetricmonoidal_op {A : Type} (tensor : A -> A -> A) (unit : A)
  `{IsSymmetricMonoidal A tensor unit}
  : IsSymmetricMonoidal A^op tensor unit.
Proof.
  snrapply Build_IsSymmetricMonoidal.
  - rapply ismonoidal_op.
  - rapply symmetricbraiding_op.
  - intros a b c; unfold op in a, b, c; simpl.
    snrefine (_ $@ (_ $@L (_ $@R _))).
    2: exact ((braide _ _)^-1$).
    2: { nrapply cate_moveR_V1.
      symmetry.
      nrefine ((_ $@R _) $@ _).
      1: nrapply cate_buildequiv_fun.
      rapply braid_braid. }
    snrefine ((_ $@R _) $@ _).
    { refine (emap _ _)^-1$.
      rapply braide. }
    { symmetry.
      refine (cate_inv_adjointify _ _ _ _ $@ fmap2 _ _).
      nrapply cate_inv_adjointify. }
    snrefine ((_ $@L (_ $@L _)) $@ _).
    { refine (emap (flip tensor c) _)^-1$.
      rapply braide. }
    { symmetry.
      refine (cate_inv_adjointify _ _ _ _ $@ fmap2 _ _).
      nrapply cate_inv_adjointify. }
    refine ((_ $@L _)^$ $@ _^$ $@ cate_inv2 _ $@ _ $@ (_ $@L _)).
    1,2,4,5: rapply cate_inv_compose'.
    refine (_ $@ (_ $@@ _) $@ _ $@ (_ $@R _)^$ $@ _^$).
    1-3,5-6: rapply cate_buildequiv_fun.
    refine ((fmap02 _ _ _ $@@ ((_ $@ fmap20 _ _ _) $@R _)) $@ cat_symm_tensor_hexagon a b c $@ ((_ $@L _^$) $@R _)).
    1-4: nrapply cate_buildequiv_fun.
Defined.

Definition issymmetricmonoidal_op' {A : Type} (tensor : A -> A -> A) (unit : A)
  `{HasEquivs A} `{H' : !IsSymmetricMonoidal A^op tensor unit}
  : IsSymmetricMonoidal A tensor unit
  := issymmetricmonoidal_op (A:=A^op) tensor unit.

(** ** Further Coherence Conditions *)
(** In MacLane's original axiomatisation of a monoidal category, 3 extra coherence conditions were given in addition to the pentagon and triangle identities. It was later shown by Kelly that these axioms are redundant and follow from the rest. We reproduce these arguments here. *)

(** The left unitor of a tensor can be decomposed as an associator and a functorial action of the tensor on a left unitor. *)
Definition left_unitor_associator {A} (tensor : A -> A -> A) (unit : A)
  `{IsMonoidal A tensor unit} (x y : A)
  : (left_unitor (tensor x y) : _ $-> _)
    $== fmap10 tensor (left_unitor x) y $o associator unit x y.
Proof.
  refine ((cate_moveR_eV _ _ _ (isnat_natequiv left_unitor _))^$
    $@ ((_ $@L _) $@R _) $@ cate_moveR_eV _ _ _ (isnat_natequiv left_unitor _)).
  refine (_ $@ (fmap01_comp _ _ _ _)^$).
  refine (_ $@ (cate_moveR_Ve _ _ _ (associator_nat_m _  _ _)^$ $@R _)).
  nrefine (_ $@ cat_assoc_opp _ _ _).
  change (fmap (tensor ?x) ?f) with (fmap01 tensor x f).
  change (cate_fun' _ _ (cat_tensor_left_unitor ?x))
    with (cate_fun (cat_tensor_left_unitor x)).
  apply cate_moveL_Ve.
  refine ((_ $@L triangle_identity _ _ _ _ _ _) $@ _).
  nrefine (cat_assoc_opp _ _ _ $@ _ $@ cat_assoc_opp _ _ _).
  refine (_ $@ ((fmap20 _ (triangle_identity _ _ _ _ _ _) _
    $@ fmap10_comp _ _ _ _)^$ $@R _)).
  refine (_ $@ cat_assoc_opp _ _ _).
  refine (_ $@ (_ $@L (pentagon_identity _ _ _ _ _ _ $@ cat_assoc _ _ _))).
  refine ((_ $@R _) $@ cat_assoc _ _ _).
  exact (associator_nat_l _ _ _).
Defined.

(** The right unitor of a tensor can be decomposed as an inverted associator and a functorial action of the tensor on a right unitor. *)
Definition right_unitor_associator {A} (tensor : A -> A -> A) (unit : A)
  `{IsMonoidal A tensor unit} (x y : A)
  : (fmap01 tensor x (right_unitor y) : _ $-> _)
    $== right_unitor (tensor x y) $o associator x y unit.
Proof.
  refine ((cate_moveR_eV _ _ _ (isnat_natequiv right_unitor _))^$
    $@ ((_ $@L _) $@R _) $@ cate_moveR_eV _ _ _ (isnat_natequiv right_unitor _)).
  refine (_ $@ (fmap10_comp tensor _ _ _)^$).
  refine ((cate_moveR_eV _ _ _ (associator_nat_m _ _ _))^$ $@ _).
  refine (_ $@ (cate_moveR_eV _ _ _ (triangle_identity _ _ _ _ _ _) $@R _)).
  apply cate_moveR_eV.
  refine ((_ $@L
    (fmap02 _ _ (cate_moveR_eV _ _ _ (triangle_identity _ _ _ _ _ _))^$
    $@ fmap01_comp _ _ _ _)) $@ _).
  refine (cat_assoc_opp _ _ _ $@ _).
  nrefine ((associator_nat_r _ _ _ $@R _) $@ cat_assoc _ _ _ $@ _).
  do 2 nrefine (_ $@ cat_assoc_opp _ _ _).
  refine (_ $@L _).
  refine ((_ $@L (emap_inv' _ _)^$) $@ _).
  apply cate_moveR_eV.
  refine (_ $@ (_ $@L cate_buildequiv_fun _)^$).
  nrefine (_ $@ cat_assoc_opp _ _ _).
  apply cate_moveL_Ve.
  rapply pentagon_identity.
Defined.

(** The left unitor at the unit is the right unitor at the unit. *)
Definition left_unitor_unit_right_unitor_unit {A} (tensor : A -> A -> A) (unit : A)
  `{IsMonoidal A tensor unit}
  : (left_unitor unit : tensor unit unit $-> _) $== right_unitor unit.
Proof.
  refine ((cate_moveR_eV _ _ _ (isnat_natequiv left_unitor (left_unitor unit)))^$
    $@ _).
  apply cate_moveR_eV.
  refine (_ $@ (_ $@L left_unitor_associator _ _ _ _)^$).
  nrefine (_ $@ (_ $@R _) $@ cat_assoc _ _ _). 
  2: rapply (isnat_natequiv right_unitor _)^$.
  nrefine ((_ $@L _) $@ cat_assoc_opp _ _ _).
  refine (triangle_identity _ _ _ _ _ _ $@ _).
  nrefine (_ $@R _).
  nrapply cate_monic_equiv.
  exact (isnat_natequiv right_unitor (right_unitor unit)).
Defined.

(** TODO: Kelly also shows that there are redundant coherence conditions for symmetric monoidal categories also, but we leave these out for now. *)

(** ** Monoidal functors *)

(** A (lax) monoidal functor [F] between two monoidal categories [A] and [B] is a functor [F : A -> B] together with: *)
Class IsMonoidalFunctor {A B : Type}
  {tensorA : A -> A -> A} {tensorB : B -> B -> B} {IA : A} {IB : B}
  `{IsMonoidal A tensorA IA, IsMonoidal B tensorB IB}
  (F : A -> B) `{!Is0Functor F, !Is1Functor F} := {

  (** A natural transformation [fmap_tensor] from [F a ⊗ F b] to [F (a ⊗ b)]. *)
  fmap_tensor
    : NatTrans
        (uncurry (fun a b => tensorB (F a) (F b)))
        (uncurry (fun a b => F (tensorA a b)));

  (** A morphism [fmap_unit] relating the two unit objects. *)
  fmap_unit : IB $-> F (IA);

  (** Such that the following coherence conditions hold: 
  
  [F] preserves the [associator]s in a suitable way. *)
  fmap_tensor_assoc a b c
    : fmap F (associator a b c)
        $o fmap_tensor (a, tensorA b c)
        $o fmap01 tensorB (F a) (fmap_tensor (b, c))
      $== fmap_tensor (tensorA a b, c)
        $o fmap10 tensorB (fmap_tensor (a, b)) (F c)
        $o associator (F a) (F b) (F c);
  
  (** [F] preserves the [left_unitor]s in a suitable way. *)
  fmap_tensor_left_unitor a
    : trans_nattrans left_unitor (F a)
      $== fmap F (left_unitor a)
        $o fmap_tensor (IA, a)
        $o fmap10 tensorB fmap_unit (F a);

  (** [F] preserves the [right_unitors]s in a suitable way. *)
  fmap_tensor_right_unitor a
    : trans_nattrans right_unitor (F a)
      $== fmap F (right_unitor a)
        $o fmap_tensor (a, IA)
        $o fmap01 tensorB (F a) fmap_unit;
}.

Arguments fmap_tensor {A B tensorA tensorB IA IB _ _ _ _ _ _ _ _ _ _ _ _}
  F {_ _ _}.

Definition fmap_tensor_nat {A B : Type}
  {tensorA : A -> A -> A} {tensorB : B -> B -> B} {IA : A} {IB : B}
  (F : A -> B) `{IsMonoidalFunctor A B tensorA tensorB IA IB F}
  {x x' y y': A} (f : x $-> x') (g : y $-> y')
  : fmap_tensor F (x', y') $o fmap11 tensorB (fmap F f) (fmap F g)
    $== fmap F (fmap11 tensorA f g) $o fmap_tensor F (x, y).
Proof.
  destruct (fmap_tensor F) as [fmap_tensor_F nat].
  exact (nat (x, y) (x', y') (f, g)).
Defined.

Definition fmap_tensor_nat_l {A B : Type}
  {tensorA : A -> A -> A} {tensorB : B -> B -> B} {IA : A} {IB : B}
  (F : A -> B) `{IsMonoidalFunctor A B tensorA tensorB IA IB F}
  {x x' y : A} (f : x $-> x')
  : fmap_tensor F (x', y) $o fmap10 tensorB (fmap F f) (F y)
    $== fmap F (fmap10 tensorA f y) $o fmap_tensor F (x, y).
Proof.
  refine ((_ $@L (fmap12 tensorB _ (fmap_id _ _)
    $@ fmap10_is_fmap11 _ _ _)^$) $@ _). 
  refine (_ $@ (fmap2 F (fmap10_is_fmap11 _ _ _) $@R _)).
  snrapply fmap_tensor_nat.
Defined.

Definition fmap_tensor_nat_r {A B : Type}
  {tensorA : A -> A -> A} {tensorB : B -> B -> B} {IA : A} {IB : B}
  (F : A -> B) `{IsMonoidalFunctor A B tensorA tensorB IA IB F}
  {x y y' : A} (g : y $-> y')
  : fmap_tensor F (x, y') $o fmap01 tensorB (F x) (fmap F g)
    $== fmap F (fmap01 tensorA x g) $o fmap_tensor F (x, y).
Proof.
  refine ((_ $@L (fmap21 tensorB (fmap_id _ _) _
    $@ fmap01_is_fmap11 _ _ _)^$) $@ _).
  refine (_ $@ (fmap2 F (fmap01_is_fmap11 _ _ _) $@R _)).
  snrapply fmap_tensor_nat.
Defined.
