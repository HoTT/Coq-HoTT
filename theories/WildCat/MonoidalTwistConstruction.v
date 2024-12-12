Require Import Basics.Overture Basics.Tactics Types.Forall WildCat.Monoidal.
Require Import WildCat.Core WildCat.Bifunctor WildCat.Prod WildCat.Equiv.
Require Import WildCat.NatTrans WildCat.Square WildCat.Opposite.

(** * Building Symmetric Monoidal Categories *)

(** The following construction is what we call the "twist construction". It is a way to build a symmetric monoidal category from simpler pieces than the axioms ask for.

The core observation is that the associator can be broken up into a [braid] and what we call a [twist] map. The twist map takes a right associated triple [(A, (B, C))] and swaps the first two factors [(B, (A, C)]. Together with functoriality of the tensor and the braiding, here termed [braid] we can simplify the axioms we ask for.

For instance, the hexagon identity is about associators, but if we unfold the definition and simplify the diagram, we get a diagram about only twists and braids.

This means in practice, you can show a category has a symmetric monoidal structure by proving some simpler axioms. This idea has been used in TriJoin.v to show the associativity of join for example. *)

Section TwistConstruction.
  (** The aim of this section is to build a symmetric monoidal category. We do this piecewise so that the separate steps are useful in and of themselves.

  Our basic starting assumption is that we have a category with equivalences, a bifunctor called the tensor product, and a unit object.*)
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

  Definition twist_nat_l {a a'} (f : a $-> a') b c
    : twist a' b c $o fmap10 cat_tensor f (cat_tensor b c)
      $== fmap01 cat_tensor b (fmap10 cat_tensor f c) $o twist a b c.
  Proof.
    refine ((_ $@L _^$) $@ twist_nat a a' b b c c f (Id _) (Id _) $@ (_ $@R _)).
    - refine (fmap12 _ _ _ $@ fmap10_is_fmap11 _ _ _).
      rapply fmap11_id.
    - refine (fmap12 _ _ _ $@ fmap01_is_fmap11 _ _ _).
      rapply fmap10_is_fmap11.
  Defined.

  Definition twist_nat_m a {b b'} (g : b $-> b') c
    : twist a b' c $o fmap01 cat_tensor a (fmap10 cat_tensor g c)
      $== fmap10 cat_tensor g (cat_tensor a c) $o twist a b c.
  Proof.
    refine ((_ $@L _^$) $@ twist_nat a a b b' c c (Id _) g (Id _) $@ (_ $@R _)).
    - refine (fmap12 _ _ _ $@ fmap01_is_fmap11 _ _ _).
      rapply fmap10_is_fmap11.
    - refine (fmap12 _ _ _ $@ fmap10_is_fmap11 _ _ _).
      rapply fmap11_id.
  Defined.

  Definition twist_nat_r a b {c c'} (h : c $-> c')
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

  Definition moveL_twistL a b c d f (g : d $-> _)
    : twist a b c $o f $== g -> f $== twist b a c $o g.
  Proof.
    intros p.
    apply (cate_monic_equiv (twiste a b c)).
    nrefine ((cate_buildequiv_fun _ $@R _) $@ p $@ _ $@ cat_assoc _ _ _).
    refine ((cat_idl _)^$ $@ (_^$ $@R _)).
    refine ((cate_buildequiv_fun _ $@R _) $@ _).
    apply twist_twist.
  Defined.

  Definition moveL_twistR a b c d f (g : _ $-> d)
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

  Definition moveR_twistL a b c d f (g : d $-> _)
    : f $== twist b a c $o g -> twist a b c $o f $== g.
  Proof.
    intros p; symmetry; apply moveL_twistL; symmetry; exact p.
  Defined.

  Definition moveR_twistR a b c d f (g : _ $-> d)
    : f $== g $o twist b a c -> f $o twist a b c $== g.
  Proof.
    intros p; symmetry; apply moveL_twistR; symmetry; exact p.
  Defined.

  Definition moveL_fmap01_twistL a b c d e f (g : e $-> _)
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

  Definition moveL_fmap01_twistR a b c d e f (g : _ $-> e)
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

  Definition moveR_fmap01_twistL a b c d e f (g : e $-> _)
    : f $== fmap01 cat_tensor a (twist c b d) $o g
      -> fmap01 cat_tensor a (twist b c d) $o f $== g.
  Proof.
    intros p; symmetry; apply moveL_fmap01_twistL; symmetry; exact p.
  Defined.

  Definition moveR_fmap01_twistR a b c d e f (g : _ $-> e)
    : f $== g $o fmap01 cat_tensor a (twist c b d)
      -> f $o fmap01 cat_tensor a (twist b c d) $== g.
  Proof.
    intros p; symmetry; apply moveL_fmap01_twistR; symmetry; exact p.
  Defined.

  (** *** The associator *)

  (** Using [braide] and [twiste] we can build an associator. *)
  Definition associator_twist' a b c
    : cat_tensor a (cat_tensor b c) $<~> cat_tensor (cat_tensor a b) c.
  Proof.
    (** We can build the associator out of [braide] and [twiste]. *)
    refine (braide _ _ $oE _).
    nrefine (twiste _ _ _ $oE _).
    exact (emap01 cat_tensor a (braide _ _)).
  Defined.

  (** We would like to be able to unfold [associator_twist'] to the underlying morphisms. We use this lemma to make that process easier. *)
  Definition associator_twist'_unfold a b c
    : cate_fun (associator_twist' a b c)
    $== braid c (cat_tensor a b) $o (twist a c b $o fmap01 cat_tensor a (braid b c)).
  Proof.
    refine (cate_buildequiv_fun _ $@ (_ $@@ cate_buildequiv_fun _)).
    nrefine (cate_buildequiv_fun _ $@ (_ $@@ cate_buildequiv_fun _)).
    refine (cate_buildequiv_fun _ $@ fmap2 _ _).
    apply cate_buildequiv_fun.
  Defined.

  (** Now we can use [associator_twist'] and show that it is a natural equivalence in each variable. *)
  Instance associator_twist : Associator cat_tensor.
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
  Instance left_unitor_twist : LeftUnitor cat_tensor cat_tensor_unit.
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
  Instance triangle_twist : TriangleIdentity cat_tensor cat_tensor_unit.
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

  Instance pentagon_twist : PentagonIdentity cat_tensor.
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

  Instance hexagon_twist : HexagonIdentity cat_tensor.
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
  Instance ismonoidal_twist
    : IsMonoidal A cat_tensor cat_tensor_unit
    := {}.

  (** There is a symmetric monoidal category on [A]. *)
  Instance issymmetricmonoidal_twist
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
