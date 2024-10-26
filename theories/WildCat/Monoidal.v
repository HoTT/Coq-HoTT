Require Import Basics.Overture Basics.Tactics Types.Forall.
Require Import WildCat.Core WildCat.Bifunctor WildCat.Prod WildCat.Equiv.
Require Import WildCat.NatTrans WildCat.Square WildCat.Opposite.

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

  Local Definition associator_nat {x x' y y' z z'}
    (f : x $-> x') (g : y $-> y') (h : z $-> z')
    : associator x' y' z' $o fmap11 F f (fmap11 F g h)
      $== fmap11 F (fmap11 F f g) h $o associator x y z.
  Proof.
    destruct assoc as [asso nat].
    exact (nat (x, y, z) (x', y', z') (f, g, h)).
  Defined.

  Local Definition associator_nat_l {x x' : A} (f : x $-> x') (y z : A)
    : associator x' y z $o fmap10 F f (F y z)
      $== fmap10 F (fmap10 F f y) z $o associator x y z.
  Proof.
    refine ((_ $@L _^$) $@ _ $@ (_ $@R _)).
    2: rapply (associator_nat f (Id _) (Id _)).
    - exact (fmap12 _ _ (fmap11_id _ _ _) $@ fmap10_is_fmap11 _ _ _).
    - exact (fmap21 _ (fmap10_is_fmap11 _ _ _) _ $@ fmap10_is_fmap11 _ _ _).
  Defined.

  Local Definition associator_nat_m (x : A) {y y' : A} (g : y $-> y') (z : A)
    : associator x y' z $o fmap01 F x (fmap10 F g z)
      $== fmap10 F (fmap01 F x g) z $o associator x y z.
  Proof.
    refine ((_ $@L _^$) $@ _ $@ (_ $@R _)).
    2: nrapply (associator_nat (Id _) g (Id _)).
    - exact (fmap12 _ _ (fmap10_is_fmap11 _ _ _) $@ fmap01_is_fmap11 _ _ _).
    - exact (fmap21 _ (fmap01_is_fmap11 _ _ _) _ $@ fmap10_is_fmap11 _ _ _).
  Defined.

  Local Definition associator_nat_r (x y : A) {z z' : A} (h : z $-> z')
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
  Local Instance catie_braid a b : CatIsEquiv (braid a b)
    := catie_adjointify (braid a b) (braid b a) (braid_braid a b) (braid_braid b a).

  (** [braide] is the bundled equivalence whose underlying map is [braid]. *)
  Definition braide a b
    : F a b $<~> F b a
    := Build_CatEquiv (braid a b).

  Local Definition moveL_braidL a b c f (g : c $-> _)
    : braid a b $o f $== g -> f $== braid b a $o g.
  Proof.
    intros p.
    apply (cate_monic_equiv (braide a b)).
    refine ((cate_buildequiv_fun _ $@R _) $@ p $@ _ $@ cat_assoc _ _ _).
    refine ((cat_idl _)^$ $@ (_^$ $@R _)).
    refine ((cate_buildequiv_fun _ $@R _) $@ _).
    apply braid_braid.
  Defined.

  Local Definition moveL_braidR a b c f (g : _ $-> c)
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

  Local Definition moveR_braidL a b c f (g : c $-> _)
    : f $== braid b a $o g -> braid a b $o f $== g.
  Proof.
    intros p; symmetry; apply moveL_braidL; symmetry; exact p.
  Defined.

  Local Definition moveR_braidR a b c f (g : _ $-> c)
    : f $== g $o braid b a -> f $o braid a b $== g.
  Proof.
    intros p; symmetry; apply moveL_braidR; symmetry; exact p.
  Defined.

  Local Definition moveL_fmap01_braidL a b c d f (g : d $-> _)
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

  Local Definition moveL_fmap01_braidR a b c d f (g : _ $-> d)
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

  Local Definition moveR_fmap01_braidL a b c d f (g : d $-> _)
    : f $== fmap01 F a (braid c b) $o g
      -> fmap01 F a (braid b c) $o f $== g.
  Proof.
    intros p; symmetry; apply moveL_fmap01_braidL; symmetry; exact p.
  Defined.

  Local Definition moveR_fmap01_braidR a b c d f (g : _ $-> d)
    : f $== g $o fmap01 F a (braid c b)
      -> f $o fmap01 F a (braid b c) $== g.
  Proof.
    intros p; symmetry; apply moveL_fmap01_braidR; symmetry; exact p.
  Defined.

  Local Definition moveL_fmap01_fmap01_braidL a b c d e f (g : e $-> _)
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

  Local Definition moveL_fmap01_fmap01_braidR a b c d e f (g : _ $-> e)
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

  Local Definition moveR_fmap01_fmap01_braidL a b c d e f (g : e $-> _)
    : f $== fmap01 F a (fmap01 F b (braid d c)) $o g
      -> fmap01 F a (fmap01 F b (braid c d)) $o f $== g.
  Proof.
    intros p; symmetry; apply moveL_fmap01_fmap01_braidL; symmetry; exact p.
  Defined.

  Local Definition moveR_fmap01_fmap01_braidR a b c d e f (g : _ $-> e)
    : f $== g $o fmap01 F a (fmap01 F b (braid d c))
      -> f $o fmap01 F a (fmap01 F b (braid c d)) $== g.
  Proof.
    intros p; symmetry; apply moveL_fmap01_fmap01_braidR; symmetry; exact p.
  Defined.

  Local Definition braid_nat {a b c d} (f : a $-> c) (g : b $-> d)
    : braid c d $o fmap11 F f g $== fmap11 F g f $o braid a b.
  Proof.
    exact (isnat braid_uncurried (a := (a, b)) (a' := (c, d)) (f, g)).
  Defined.

  Local Definition braid_nat_l {a b c} (f : a $-> b)
    : braid b c $o fmap10 F f c $== fmap01 F c f $o braid a c.
  Proof.
    refine ((_ $@L (fmap10_is_fmap11 _ _ _)^$) $@ _ $@ (fmap01_is_fmap11 _ _ _ $@R _)).
    exact (isnat braid_uncurried (a := (a, c)) (a' := (b, c)) (f, Id _)).
  Defined.

  (** This is just the inverse of above. *)
  Local Definition braid_nat_r {a b c} (g : b $-> c)
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

(** ** Building Symmetric Monoidal Categories *)

(** The following construction is what we call the "twist construction". It is a way to build a symmetric monoidal category from simpler pieces than the axioms ask for.

The core observation is that the associator can be broken up into a [braid] and what we call a [twist] map. The twist map takes a right associated triple [(A, (B, C))] and swaps the first two factors [(B, (A, C)]. Together with functoriality of the tensor and the braiding, here termed [braid] we can simplify the axioms we ask for.

For instance, the hexagon identity is about associators, but if we unfold the definition and simplify the diagram, we get a diagram about only twists and braids.

This means in practice, you can show a category has a symmetric monoidal structure by proving some simpler axioms. This idea has been used in TriJoin.v to show the associativity of join for example. *)

Section TwistConstruction.
  (** The aim of this section is to build a symmetric monoidal category. We do this piecewise so that the separate steps are useful in and of themselves.

  Our basic starting assumption is that we have a category with equivalences, a bifunctor called the tensor product, and a unit object. *)
  Context (A : Type) `{HasEquivs A}
    (cat_tensor : A -> A -> A) (cat_tensor_unit : A)
    `{!Is0Bifunctor cat_tensor, !Is1Bifunctor cat_tensor}

    (** Next we postulate the existence of a [braid] map. This takes a tensor pair and swaps the factors. We also postulate that [braid] is natural in both factors and self-inverse. *)
    (braid : SymmetricBraiding cat_tensor)

    (** We postulate the existence of a [twist] map. This takes a right associated triple [(A, (B, C))] and swaps the first two factors [(B, (A, C)]. We also postulate that [twist] is natural in all three factors and self-inverse. *)
    (twist : forall a b c, cat_tensor a (cat_tensor b c) $-> cat_tensor b (cat_tensor a c))
    (twist_twist : forall a b c, twist a b c $o twist b a c $== Id _)
    (twist_nat : forall a a' b b' c c' (f : a $-> a') (g : b $-> b') (h : c $-> c'),
      twist a' b' c' $o fmap11 cat_tensor f (fmap11 cat_tensor g h)
      $== fmap11 cat_tensor g (fmap11 cat_tensor f h) $o twist a b c)

    (** We assume that there is a natural isomorphism [right_unitor] witnessing the right unit law. The left unit law will be derived from this one. We also assume a coherence called [twist_unitor] which determines how the right_unitor interacts with [braid] and [twist]. This is the basis of the triangle axiom. *)
    (right_unitor : RightUnitor cat_tensor cat_tensor_unit)
    (twist_unitor : forall a b, fmap01 cat_tensor a (right_unitor b)
      $== braid b a $o fmap01 cat_tensor b (right_unitor a) $o twist a b cat_tensor_unit)

    (** The hexagon identity is about the interaction of associators and braids. We will derive this axiom from an analogous one for twists and braids. *)
    (twist_hexagon : forall a b c,
      fmap01 cat_tensor c (braid b a) $o twist b c a $o fmap01 cat_tensor b (braid a c)
      $== twist a c b $o fmap01 cat_tensor a (braid b c) $o twist b a c)

    (** The 9-gon identity. TODO: explain this *)
    (twist_9_gon : forall a b c d,
        fmap01 cat_tensor c (braid (cat_tensor a b) d)
        $o twist (cat_tensor a b) c d
        $o braid (cat_tensor c d) (cat_tensor a b)
        $o twist a (cat_tensor c d) b
        $o fmap01 cat_tensor a (braid b (cat_tensor c d))
      $== fmap01 cat_tensor c (twist a d b)
        $o fmap01 cat_tensor c (fmap01 cat_tensor a (braid b d))
        $o twist a c (cat_tensor b d)
        $o fmap01 cat_tensor a (twist b c d))
  .

  (** *** Setup *)

  (** Before starting the proofs, we need to setup some useful definitions and helpful lemmas for working with diagrams. *)

  (** We give notations and abbreviations to the morphisms that will appear in diagrams. This helps us read the goal and understand what is happening, otherwise it is too verbose. *)
  Declare Scope monoidal_scope.
  Local Infix "⊗" := cat_tensor (at level 40) : monoidal_scope.
  Local Infix "⊗R" := (fmap01 cat_tensor) (at level 40) : monoidal_scope.
  Local Infix "⊗L" := (fmap10 cat_tensor) (at level 40) : monoidal_scope.
  Local Notation "f ∘ g" := (f $o g) (at level 61, left associativity, format "f  '/' '∘'  g") : monoidal_scope.
  (** TODO: in 8.19 this notation causes issues, when updating to 8.20 we should uncomment this. *)
  (* Local Notation "f $== g :> A" := (GpdHom (A := A) f g)
    (at level 70, format "'[v' '[v' f ']' '/'  $== '/'  '[v' g ']'  '/' :>  '[' A ']' ']'")
    : long_path_scope. *)
  Local Open Scope monoidal_scope.

  (** [twist] is an equivalence which we will call [twiste]. *)
  Local Definition twiste a b c
    : cat_tensor a (cat_tensor b c) $<~> cat_tensor b (cat_tensor a c)
    := cate_adjointify (twist a b c) (twist b a c)
        (twist_twist a b c) (twist_twist b a c).

  (** *** Finer naturality *)

  (** The naturality postulates we have for [twist] are natural in all their arguments similtaneously. We show the finer naturality of [twist] in each argument separately as this becomes more useful in practice. *)

  Local Definition twist_nat_l {a a'} (f : a $-> a') b c
    : twist a' b c $o fmap10 cat_tensor f (cat_tensor b c)
      $== fmap01 cat_tensor b (fmap10 cat_tensor f c) $o twist a b c.
  Proof.
    refine ((_ $@L _^$) $@ twist_nat a a' b b c c f (Id _) (Id _) $@ (_ $@R _)).
    - refine (fmap12 _ _ _ $@ fmap10_is_fmap11 _ _ _).
      rapply fmap11_id.
    - refine (fmap12 _ _ _ $@ fmap01_is_fmap11 _ _ _).
      rapply fmap10_is_fmap11.
  Defined.

  Local Definition twist_nat_m a {b b'} (g : b $-> b') c
    : twist a b' c $o fmap01 cat_tensor a (fmap10 cat_tensor g c)
      $== fmap10 cat_tensor g (cat_tensor a c) $o twist a b c.
  Proof.
    refine ((_ $@L _^$) $@ twist_nat a a b b' c c (Id _) g (Id _) $@ (_ $@R _)).
    - refine (fmap12 _ _ _ $@ fmap01_is_fmap11 _ _ _).
      rapply fmap10_is_fmap11.
    - refine (fmap12 _ _ _ $@ fmap10_is_fmap11 _ _ _).
      rapply fmap11_id.
  Defined.

  Local Definition twist_nat_r a b {c c'} (h : c $-> c')
    : twist a b c' $o fmap01 cat_tensor a (fmap01 cat_tensor b h)
      $== fmap01 cat_tensor b (fmap01 cat_tensor a h) $o twist a b c.
  Proof.
    refine ((_ $@L _^$) $@ twist_nat a a b b c c' (Id _) (Id _) h $@ (_ $@R _)).
    - refine (fmap12 _ _ _ $@ fmap01_is_fmap11 _ _ _).
      rapply fmap01_is_fmap11.
    - refine (fmap12 _ _ _ $@ fmap01_is_fmap11 _ _ _).
      rapply fmap01_is_fmap11.
  Defined.

  (** *** Movement lemmas *)

  (** Here we collect lemmas about moving morphisms around in a diagram. We could have created [cate_moveL_eM]-style lemmas for [CatIsEquiv] but this leads to a lot of unnecessary unfolding and duplication. It is typically easier to use a hand crafted lemma for each situation. *)

  (** TODO: A lot of these proofs are copy and pasted between lemmas. We need to work out an efficient way of proving them. *)

  (** **** Moving [twist] *)

  Local Definition moveL_twistL a b c d f (g : d $-> _)
    : twist a b c $o f $== g -> f $== twist b a c $o g.
  Proof.
    intros p.
    apply (cate_monic_equiv (twiste a b c)).
    nrefine ((cate_buildequiv_fun _ $@R _) $@ p $@ _ $@ cat_assoc _ _ _).
    refine ((cat_idl _)^$ $@ (_^$ $@R _)).
    refine ((cate_buildequiv_fun _ $@R _) $@ _).
    apply twist_twist.
  Defined.

  Local Definition moveL_twistR a b c d f (g : _ $-> d)
    : f $o twist a b c $== g -> f $== g $o twist b a c.
  Proof.
    intros p.
    apply (cate_epic_equiv (twiste a b c)).
    refine (_ $@ (cat_assoc _ _ _)^$).
    refine (_ $@ (_ $@L ((_ $@L cate_buildequiv_fun _) $@ _)^$)).
    2: apply twist_twist.
    refine ((_ $@L _) $@ _ $@ (cat_idr _)^$).
    1: apply cate_buildequiv_fun.
    exact p.
  Defined.

  Local Definition moveR_twistL a b c d f (g : d $-> _)
    : f $== twist b a c $o g -> twist a b c $o f $== g.
  Proof.
    intros p; symmetry; apply moveL_twistL; symmetry; exact p.
  Defined.

  Local Definition moveR_twistR a b c d f (g : _ $-> d)
    : f $== g $o twist b a c -> f $o twist a b c $== g.
  Proof.
    intros p; symmetry; apply moveL_twistR; symmetry; exact p.
  Defined.

  Local Definition moveL_fmap01_twistL a b c d e f (g : e $-> _)
    : fmap01 cat_tensor a (twist b c d) $o f $== g
      -> f $== fmap01 cat_tensor a (twist c b d) $o g.
  Proof.
    intros p.
    apply (cate_monic_equiv (emap01 cat_tensor a (twiste b c d))).
    refine (_ $@ cat_assoc _ _ _).
    refine (_ $@ (_ $@R _)).
    2: { refine (_ $@ (_^$ $@R _)).
      2: apply cate_buildequiv_fun.
      refine ((fmap_id _ _)^$ $@ fmap2 _ _ $@ fmap_comp _ _ _).
      refine (_^$ $@ (_^$ $@R _)).
      2: apply cate_buildequiv_fun.
      apply twist_twist. }
    refine ((_ $@R _) $@ p $@ (cat_idl _)^$).
    refine (cate_buildequiv_fun _ $@ fmap02 _ _ _).
    apply cate_buildequiv_fun.
  Defined.

  Local Definition moveL_fmap01_twistR a b c d e f (g : _ $-> e)
    : f $o fmap01 cat_tensor a (twist b c d) $== g
      -> f $== g $o fmap01 cat_tensor a (twist c b d).
  Proof.
    intros p.
    apply (cate_epic_equiv (emap01 cat_tensor a (twiste b c d))).
    refine (_ $@ (cat_assoc _ _ _)^$).
    refine (_ $@ (_ $@L _)).
    2: { refine (_^$ $@ (_ $@L _^$)).
      2: apply cate_buildequiv_fun.
      refine ((fmap_comp _ _ _)^$ $@ fmap2 _ _ $@ fmap_id _ _).
      refine ((_ $@L _) $@ _).
      1: apply cate_buildequiv_fun.
      apply twist_twist. }
    refine ((_ $@L _) $@ p $@ (cat_idr _)^$).
    refine (cate_buildequiv_fun _ $@ fmap02 _ _ _).
    apply cate_buildequiv_fun.
  Defined.

  Local Definition moveR_fmap01_twistL a b c d e f (g : e $-> _)
    : f $== fmap01 cat_tensor a (twist c b d) $o g
      -> fmap01 cat_tensor a (twist b c d) $o f $== g.
  Proof.
    intros p; symmetry; apply moveL_fmap01_twistL; symmetry; exact p.
  Defined.

  Local Definition moveR_fmap01_twistR a b c d e f (g : _ $-> e)
    : f $== g $o fmap01 cat_tensor a (twist c b d)
      -> f $o fmap01 cat_tensor a (twist b c d) $== g.
  Proof.
    intros p; symmetry; apply moveL_fmap01_twistR; symmetry; exact p.
  Defined.

  (** *** The associator *)

  (** Using [braide] and [twiste] we can build an associator. *)
  Local Definition associator_twist' a b c
    : cat_tensor a (cat_tensor b c) $<~> cat_tensor (cat_tensor a b) c.
  Proof.
    (** We can build the associator out of [braide] and [twiste]. *)
    refine (braide _ _ $oE _).
    nrefine (twiste _ _ _ $oE _).
    exact (emap01 cat_tensor a (braide _ _)).
  Defined.

  (** We would like to be able to unfold [associator_twist'] to the underlying morphisms. We use this lemma to make that process easier. *)
  Local Definition associator_twist'_unfold a b c
    : cate_fun (associator_twist' a b c)
    $== braid c (cat_tensor a b) $o (twist a c b $o fmap01 cat_tensor a (braid b c)).
  Proof.
    refine (cate_buildequiv_fun _ $@ (_ $@@ cate_buildequiv_fun _)).
    nrefine (cate_buildequiv_fun _ $@ (_ $@@ cate_buildequiv_fun _)).
    refine (cate_buildequiv_fun _ $@ fmap2 _ _).
    apply cate_buildequiv_fun.
  Defined.

  (** Now we can use [associator_twist'] and show that it is a natural equivalence in each variable. *)
  Local Instance associator_twist : Associator cat_tensor.
  Proof.
    snrapply Build_Associator.
    - exact associator_twist'.
    - snrapply Build_Is1Natural.
      simpl; intros [[a b] c] [[a' b'] c'] [[f g] h]; simpl in f, g, h.
      (** To prove naturality it will be easier to reason about squares. *)
      change (?w $o ?x $== ?y $o ?z) with (Square z w x y).
      (** First we remove all the equivalences from the equation. *)
      nrapply hconcatL.
      1: apply associator_twist'_unfold.
      nrapply hconcatR.
      2: apply associator_twist'_unfold.
      (** The first square involving [braid] on its own is a naturality square. *)
      nrapply vconcat.
      2: rapply braid_nat.
      (** The second square is just the naturality of twist. *)
      nrapply vconcat.
      2: apply twist_nat.
      nrapply hconcatL.
      2: nrapply hconcatR.
      1,3: symmetry; rapply fmap01_is_fmap11.
      (** Leaving us with a square with a functor application. *)
      rapply fmap11_square.
      1: rapply vrefl.
      (** We are finally left with the naturality of braid. *)
      apply braid_nat.
  Defined.

  (** We abbreviate the associator to [α] for the remainder of the section. *)
  Local Notation α := associator_twist.

  (** *** Unitors *)

  (** Since we assume the [right_unitor] exists, we can derive the [left_unitor] from it together with [braid]. *)
  Local Instance left_unitor_twist : LeftUnitor cat_tensor cat_tensor_unit.
  Proof.
    snrapply Build_NatEquiv'.
    - snrapply Build_NatTrans.
      + exact (fun a => right_unitor a $o braid cat_tensor_unit a).
      + snrapply Build_Is1Natural.
        intros a b f.
        change (?w $o ?x $== ?y $o ?z) with (Square z w x y).
        nrapply vconcat.
        2: rapply (isnat right_unitor f).
        rapply braid_nat_r.
    - intros a.
      rapply compose_catie'.
      rapply catie_braid.
  Defined.

  (** *** Triangle *)

  (** The triangle identity can easily be proven by rearranging the diagram, cancelling and using naturality of [braid]. *)
  Local Instance triangle_twist : TriangleIdentity cat_tensor cat_tensor_unit.
  Proof.
    intros a b.
    refine (_ $@ (_ $@L _)^$).
    2: apply associator_twist'_unfold.
    refine (fmap02 _ a (cate_buildequiv_fun _) $@ _); cbn.
    refine (fmap01_comp _ _ _ _ $@ _).
    do 2 refine (_ $@ cat_assoc _ _ _).
    refine ((twist_unitor _ _ $@ (_ $@R _)) $@R _).
    apply braid_nat_r.
  Defined.

  (** *** Pentagon *)

  Local Open Scope long_path_scope.

  Local Instance pentagon_twist : PentagonIdentity cat_tensor.
  Proof.
    clear twist_unitor right_unitor cat_tensor_unit.
    intros a b c d.
    refine ((_ $@@ _) $@ _ $@ ((fmap02 _ _ _ $@ _)^$ $@@ (_ $@@ (fmap20 _ _ _ $@ _))^$)).
    1,2,4,6,7: apply associator_twist'_unfold.
    2: refine (fmap01_comp _ _ _ _ $@ (_ $@L (fmap01_comp _ _ _ _))).
    2: refine (fmap10_comp _ _ _ _ $@ (_ $@L (fmap10_comp _ _ _ _))).
    (** We use a notation defined above that shows the base type of the groupoid hom and formats the equation in a way that is easier to read. *)
    (** Normalize brackets on LHS *)
    refine (cat_assoc _ _ _ $@ _).
    refine (_ $@L (cat_assoc _ _ _) $@ _).
    do 4 refine ((cat_assoc _ _ _)^$ $@ _).
    (** Normalize brackets on RHS *)
    refine (_ $@ (((cat_assoc _ _ _) $@R _) $@R _)).
    do 2 refine (_ $@ ((cat_assoc _ _ _) $@R _)).
    do 2 refine (_ $@ cat_assoc _ _ _).
    (** Cancel two braids next to eachother. *)
    apply moveL_fmap01_fmap01_braidR.
    apply moveL_fmap01_twistR.
    refine (_ $@ (cat_assoc _ _ _)^$).
    refine (_ $@ ((_ $@L _) $@ cat_idr _)^$).
    2: refine ((fmap01_comp _ _ _ _)^$ $@ fmap02 _ _ _ $@ fmap01_id _ _ _).
    2: apply braid_braid.
    (** *)
    apply moveL_twistR.
    refine (_ $@ (cat_assoc _ _ _)^$).
    refine (_ $@ (_ $@L _)).
    2: apply braid_nat_r.
    refine (_ $@ cat_assoc _ _ _).
    apply moveL_fmap01_fmap01_braidR.
    refine (_ $@ (cat_assoc _ _ _)^$).
    refine (_ $@ (_ $@L _)).
    2: apply braid_nat_r.
    refine (_ $@ cat_assoc _ _ _).
    apply moveL_fmap01_twistR.
    refine (_ $@ _).
    2: apply braid_nat_r.
    (** Putting things back. *)
    apply moveR_fmap01_twistR.
    apply moveR_fmap01_fmap01_braidR.
    apply moveR_twistR.
    apply moveR_fmap01_twistR.
    (** There are two braids on the RHS of the LHS that can be swapped. *)
    refine (cat_assoc _ _ _ $@ _).
    refine ((_ $@L _) $@ _).
    1: refine ((fmap01_comp _ _ _ _)^$ $@ fmap02 _ _ _ $@ fmap01_comp _ _ _ _).
    1: apply braid_nat_r.
    refine ((cat_assoc _ _ _)^$ $@ _).
    apply moveR_fmap01_braidR.
    (** Naturality of twist on the RHS of the LHS. *)
    refine (cat_assoc _ _ _ $@ _).
    refine ((_ $@L _) $@ _).
    1: apply twist_nat_m.
    refine ((cat_assoc _ _ _)^$ $@ _).
    (** Moving some things to the RHS so that we can braid and cancel on the LHS. *)
    apply moveR_twistR.
    refine (cat_assoc _ _ _ $@ _).
    refine ((_ $@L _) $@ _).
    1: apply braid_nat_l.
    refine ((cat_assoc _ _ _)^$ $@ _).
    apply moveR_braidR.
    refine (cat_assoc _ _ _ $@ _).
    refine ((_ $@L _) $@ cat_idr _ $@ _).
    1: refine ((fmap01_comp _ _ _ _)^$ $@ fmap02 _ _ _ $@ fmap01_id _ _ _).
    1: apply braid_braid.
    apply moveL_braidR.
    apply moveL_twistR.
    apply moveL_fmap01_braidR.
    (** We are almost at the desired 9-gon. Now we cancel the inner braid on the LHS. *)
    do 4 refine (_ $@ (cat_assoc _ _ _)^$).
    do 3 refine (cat_assoc _ _ _ $@ _).
    refine (_ $@L _).
    apply moveR_twistL.
    do 4 refine (_ $@ cat_assoc _ _ _).
    refine ((cat_assoc _ _ _)^$ $@ _).
    (** Now we move terms around in order to get a homotopy in [a ⊗ (b ⊗ (d ⊗ c)) $-> d ⊗ (c ⊗ (a ⊗ b))]. *)
    apply moveL_fmap01_twistR.
    apply moveL_twistR.
    do 2 refine (_ $@ (cat_assoc _ _ _)^$).
    do 3 refine (cat_assoc _ _ _ $@ _).
    apply moveL_twistL.
    refine (_ $@ cat_assoc _ _ _).
    do 4 refine ((cat_assoc _ _ _)^$ $@ _).
    apply moveR_twistR.
    apply moveR_fmap01_twistR.
    do 3 refine (_ $@ (cat_assoc _ _ _)^$).
    do 2 refine (cat_assoc _ _ _ $@ _).
    apply moveL_fmap01_braidL.
    do 2 refine (_ $@ cat_assoc _ _ _).
    do 3 refine ((cat_assoc _ _ _)^$ $@ _).
    (** And finally, this is the 9-gon we asked for. *)
    apply twist_9_gon.
  Defined.

  Local Close Scope long_path_scope.

  (** *** Hexagon *)

  Local Instance hexagon_twist : HexagonIdentity cat_tensor.
  Proof.
    intros a b c; simpl.
    refine (((_ $@L _) $@R _) $@ _ $@ (_ $@@ (_ $@R _))^$).
    1,3,4: apply associator_twist'_unfold.
    do 2 refine (((cat_assoc _ _ _)^$ $@R _) $@ _).
    refine (cat_assoc _ _ _ $@ (_ $@L _) $@ _).
    { refine ((fmap_comp _ _ _)^$ $@ fmap2 _ _ $@ fmap_id _ _).
      apply braid_braid. }
    refine (cat_idr _ $@ _).
    refine (_ $@ cat_assoc _ _ _).
    refine (_ $@ ((cat_assoc _ _ _)^$ $@R _)).
    refine (_ $@ (((cat_idr _)^$ $@ (_ $@L _^$)) $@R _)).
    2: apply braid_braid.
    refine (((braid_nat_r _)^$ $@R _) $@ _).
    refine (cat_assoc _ _ _ $@ (_ $@L _) $@ (cat_assoc _ _ _)^$).
    refine (_ $@ cat_assoc _ _ _).
    apply moveL_fmap01_braidR.
    apply twist_hexagon.
  Defined.

  (** *** Conclusion *)

  (** In conclusion, we have proven the following: *)

  (** There is a monoidal structure on [A]. *)
  Local Instance ismonoidal_twist
    : IsMonoidal A cat_tensor cat_tensor_unit
    := {}.

  (** There is a symmetric monoidal category on [A]. *)
  Local Instance issymmetricmonoidal_twist
    : IsSymmetricMonoidal A cat_tensor cat_tensor_unit
    := {}.

  (** TODO: WIP *)

  (** Here is a hexagon involving only twist *)
  Definition twist_hex' a b c d
    : fmap01 cat_tensor c (twist a b d)
      $o twist a c (cat_tensor b d)
      $o fmap01 cat_tensor a (twist b c d)
    $== twist b c (cat_tensor a d)
      $o fmap01 cat_tensor b (twist a c d)
      $o twist a b (cat_tensor c d).
  Proof.
    pose proof (twist_hexagon c a d $@ cat_assoc _ _ _) as p.
    apply moveR_twistL in p.
    apply moveR_fmap01_braidL in p.
    apply (fmap02 cat_tensor b) in p.
    refine (_ $@ ((_ $@L p) $@R _)); clear p.
    apply moveL_twistR.
    apply moveL_twistL.
    refine (_ $@ (fmap01_comp _ _ _ _)^$).
    (** TODO simplify *)
    apply moveR_twistL.
    refine (_ $@ cat_assoc _ _ _).
  Abort.

End TwistConstruction.

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
