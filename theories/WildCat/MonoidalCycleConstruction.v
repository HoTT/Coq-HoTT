Require Import Basics.Overture Basics.Tactics Types.Forall WildCat.Monoidal.
Require Import WildCat.Core WildCat.Bifunctor WildCat.Prod WildCat.Equiv.
Require Import WildCat.NatTrans WildCat.Square WildCat.Opposite.

(** * Cycle Construction for Symmetric Monoidal Categories *)

(** The following construction is what we call the "cycle construction". Like the "twist construction" found in MonoidalTwistConstruction.v, this procedure allows one to build a symmetric monoidal category from simpler pieces.

Here we use a braid [AB -> BA] and cycle [ABC -> CAB]. *)

Section CycleConstruction.
  Context (A : Type) `{HasEquivs A}
    (cat_tensor : A -> A -> A) (cat_tensor_unit : A)
    `{!Is0Bifunctor cat_tensor, !Is1Bifunctor cat_tensor}

    (braid : SymmetricBraiding cat_tensor)

    (cycle : forall a b c,
      cat_tensor a (cat_tensor b c) $-> cat_tensor c (cat_tensor a b))
    (cycle_cycle_cycle : forall a b c,
      cycle a b c $o cycle b c a $o cycle c a b $== Id _)
    (cycle_nat : forall a a' b b' c c'
      (f : a $-> a') (g : b $-> b') (h : c $-> c'),
      cycle a' b' c' $o fmap11 cat_tensor f (fmap11 cat_tensor g h)
      $== fmap11 cat_tensor h (fmap11 cat_tensor f g) $o cycle a b c)
    
    (right_unitor : RightUnitor cat_tensor cat_tensor_unit)
    (cycle_unitor : forall a b,
      fmap01 cat_tensor a (right_unitor b)
        $o fmap01 cat_tensor a (braid _ _)
      $== braid b a
        $o fmap01 cat_tensor b (right_unitor a)
        $o cycle a cat_tensor_unit b)
    
    (cycle_octagon : forall a b c d,
      fmap01 cat_tensor d (braid (cat_tensor a b) c)
        $o cycle (cat_tensor a b) c d
        $o braid (cat_tensor c d) (cat_tensor a b)
        $o cycle a b (cat_tensor c d)
      $== fmap01 cat_tensor d (cycle a b c)
        $o cycle a (cat_tensor b c) d
        $o fmap01 cat_tensor a (braid d (cat_tensor b c))
        $o fmap01 cat_tensor a (cycle b c d))
    
    (cycle_braid : forall a b c,
      fmap01 cat_tensor a (braid b c)
      $== cycle _ _ _ $o fmap01 cat_tensor c (braid a b) $o cycle _ _ _).
  
  Local Instance catie_cycle a b c : CatIsEquiv (cycle a b c)
    := catie_adjointify
        (cycle a b c)
        (cycle b c a $o cycle c a b)
        (cat_assoc_opp _ _ _ $@ cycle_cycle_cycle a b c)
        (cycle_cycle_cycle b c a).

  Local Definition cyclee a b c
    : cat_tensor a (cat_tensor b c) $<~> cat_tensor c (cat_tensor a b)
    := Build_CatEquiv (cycle a b c). 

  (** *** Movement lemmas *)
  
  Definition moveL_cycleR a b c d f (g : _ $-> d)
    : f $o cycle b c a $o cycle c a b $== g -> f $== g $o cycle a b c.
  Proof.
    intros p.
    apply (cate_epic_equiv (cyclee b c a)).
    refine ((_ $@L _) $@ _ $@ (_ $@L _^$)). 
    1,3: apply cate_buildequiv_fun.
    nrefine (_ $@ cat_assoc_opp _ _ _).
    apply (cate_epic_equiv (cyclee c a b)).
    refine ((_ $@L _) $@ _ $@ (_ $@L _^$)). 
    1,3: apply cate_buildequiv_fun.
    nrefine (_ $@ cat_assoc_opp _ _ _).
    refine (p $@ (cat_idr _)^$ $@ (g $@L _^$)).
    apply cycle_cycle_cycle.
  Defined.
  
  Definition moveL_cycle_cycleR a b c d f (g : _ $-> d)
    : f $o cycle c a b $== g -> f $== g $o cycle a b c $o cycle b c a.
  Proof.
    intros p.
    apply moveL_cycleR.
    exact (p $@R _).
  Defined.

  (** *** The associator *)
  
  Instance associator_cycle : Associator cat_tensor.
  Proof.
    snrapply Build_Associator.
    - exact (fun a b c => braide _ _ $oE cyclee a b c).
    - snrapply Build_Is1Natural.
      intros [[a b] c] [[a' b'] c'] [[f g] h]; simpl in f, g, h.
      cbn zeta; unfold fst, snd.
      change (?w $o ?x $== ?y $o ?z) with (Square z w x y).
      nrapply hconcatL.
      1: nrefine (_ $@ (_ $@@ _)). 
      1,2,3: apply cate_buildequiv_fun.
      nrapply hconcatR.
      2: nrefine (_ $@ (_ $@@ _)). 
      2,3,4: apply cate_buildequiv_fun.
      nrapply vconcat.
      1: apply cycle_nat.
      apply braid_nat.
  Defined.
  
  Local Notation α := associator_cycle.
  
  Definition associator_cycle_unfold a b c
    : cate_fun (α a b c) $== braid c (cat_tensor a b) $o cycle a b c
    := cate_buildequiv_fun _
      $@ (cate_buildequiv_fun _ $@@ cate_buildequiv_fun _).
  
  (** *** Unitors *)

  (** Since we assume the [right_unitor] exists, we can derive the [left_unitor] from it together with [braid]. *)
  Instance left_unitor_cycle : LeftUnitor cat_tensor cat_tensor_unit.
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
  Instance triangle_cycle : TriangleIdentity cat_tensor cat_tensor_unit.
  Proof.
    clear cycle_octagon cycle_braid.
    intros a b.
    refine (_ $@ (_ $@L associator_cycle_unfold _ _ _)^$).
    refine (fmap02 _ a (cate_buildequiv_fun _) $@ _); cbn.
    refine (fmap01_comp _ _ _ _ $@ _).
    nrefine (_ $@ cat_assoc _ _ _).
    nrefine (_ $@ (_ $@R _)).
    2: apply braid_nat_r.
    exact (cycle_unitor a b).
  Defined.

  (** *** Pentagon *)
  
  Instance pentagon_cycle : PentagonIdentity cat_tensor.
  Proof.
    intros a b c d.
    refine (_ $@ (_^$ $@R _)).
    2: { refine ((_ $@@ (fmap20 _ _ _ $@ fmap10_comp _ _ _ _)) $@ _).
      1,2: apply associator_cycle_unfold.
      refine (cat_assoc _ _ _ $@ (_ $@L (cat_assoc_opp _ _ _ $@ (_^$ $@R _)))).
      apply braid_nat_r. }
    nrefine (_ $@ cat_assoc_opp _ _ _).
    nrefine (_ $@ (_ $@L cat_assoc_opp _ _ _)).
    nrefine (_ $@ (_ $@L cat_assoc_opp _ _ _)).
    nrefine (_ $@ cat_assoc _ _ _).
    nrefine (_ $@ (_ $@R _)).
    2: apply braid_nat_r.
    nrefine ((_ $@@ _) $@ _).
    1,2: apply associator_cycle_unfold.
    nrefine (cat_assoc _ _ _ $@ (_ $@L _) $@ cat_assoc_opp _ _ _).
    nrefine (cat_assoc_opp _ _ _ $@ _).
    apply moveL_fmap01_braidL.
    nrefine (cat_assoc_opp _ _ _ $@ (cat_assoc_opp _ _ _ $@R _) $@ _).
    nrefine (cycle_octagon _ _ _ _ $@ _).
    nrefine (cat_assoc _ _ _ $@ cat_assoc _ _ _ $@ (_ $@L (_ $@L _))).
    refine ((fmap01_comp _ _ _ _)^$ $@ fmap02 _ _ _^$).
    apply associator_cycle_unfold.
  Defined.

  (** *** Hexagon *)

  Instance hexagon_cycle : HexagonIdentity cat_tensor.
  Proof.
    clear cycle_octagon.
    intros a b c; simpl.
    refine (((_ $@L _) $@R _) $@ _ $@ (_ $@@ (_ $@R _))^$).
    1,3,4: apply associator_cycle_unfold.
    nrefine ((cat_assoc_opp _ _ _ $@R _) $@ _).
    refine (_ $@ cat_assoc _ _ _).
    refine (_ $@ (cat_assoc_opp _ _ _ $@R _)).
    refine (_ $@ (((cat_idr _)^$ $@ (_ $@L _^$)) $@R _)).
    2: apply braid_braid.
    refine ((((braid_nat_r _)^$ $@R _) $@R _) $@ _).
    refine (cat_assoc _ _ _ $@ cat_assoc _ _ _ $@ (_ $@L _) $@ cat_assoc_opp _ _ _).
    apply moveR_fmap01_braidL.
    refine (_ $@ cat_assoc _ _ _).
    apply moveL_cycle_cycleR.
    symmetry.
    apply cycle_braid.
  Defined.
  
  Instance ismonoidal_cycle
    : IsMonoidal A cat_tensor cat_tensor_unit
    := {}.
  
  Instance issymmetricmonoidal_cycle
    : IsSymmetricMonoidal A cat_tensor cat_tensor_unit
    := {}.

End CycleConstruction.