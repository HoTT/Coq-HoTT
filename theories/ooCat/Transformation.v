(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.
Require Export ooCat.Cat1 ooCat.Laxity.

Generalizable Variables m n p A B C.

(** * Inserters and natural transformations *)

(** ** Dependent inserters *)

Definition GenDInserter (ls : Stream Laxity) `{IsGlob m A} `{HasEquivs n B}
           (F G : A -> B) `{!IsFunctor0 F, !IsFunctor0 G}
           (a : A)
  := lHom (head ls) (F a) (G a).

CoFixpoint isdglob_gendinserter (ls : Stream Laxity)
           `{IsGlob m A} `{HasEquivs n B}
           (F G : A -> B) `{!IsFunctor0 F, !IsFunctor0 G}
  : IsDGlob n (GenDInserter ls F G).
Proof.
  unshelve econstructor.
  - intros a b f ta tb; revert f.
    unfold GenDInserter in ta, tb.
    destruct (head ls).
    + exact (GenDInserter (tail ls) (cat_postcomp (F a) tb o fmap F)
                          (cat_precomp (G b) ta o fmap G)).
    + exact (GenDInserter (tail ls) (cat_postcomp (F a) tb o fmap F)
                          (cat_precomp (G b) ta o fmap G)).
    + exact (GenDInserter (tail ls) (cat_postcomp (G a) tb o fmap G)
                          (cat_precomp (F b) ta o fmap F)).
  - intros a b ta tb; cbn.
    unfold GenDInserter in ta, tb.
    set (l := head ls) in *.
    destruct l;
    apply isdglob_gendinserter.
Defined.
Global Existing Instance isdglob_gendinserter.

(** We can forget the invertibility of an iso-inserter. *)
Definition colax_pseudo_inserter
           (ls : Stream Laxity) `{IsGlob m A} `{HasEquivs n B}
           (F G : A -> B) `{!IsFunctor0 F, !IsFunctor0 G} (a : A)
  : (GenDInserter (SCons pseudo ls) F G a) -> (GenDInserter (SCons colax ls) F G a)
  := fun f => cate_fun f.

Global Instance isdfunctor0_colax_pseudo_inserter
       (ls : Stream Laxity) `{IsGlob m A} `{HasEquivs n B}
       (F G : A -> B) `{!IsFunctor0 F, !IsFunctor0 G}
  : IsDFunctor0 idmap (colax_pseudo_inserter ls F G).
Proof.
  unshelve econstructor.
  - cbn; intros a b u v f g.
    exact g.
  - cbn; intros a b u v.
    apply isdfunctor0_idmap.
Defined.

(** And we can turn around a lax inserter into a colax one. *)
Definition colax_lax_inserter
           (ls : Stream Laxity) `{IsGlob m A} `{HasEquivs n B}
           (F G : A -> B) `{!IsFunctor0 F, !IsFunctor0 G} (a : A)
  : (GenDInserter (SCons lax ls) G F a) -> (GenDInserter (SCons colax ls) F G a)
  := fun f => f.

Global Instance isdfunctor0_colax_lax_inserter
       (ls : Stream Laxity) `{IsGlob m A} `{HasEquivs n B}
       (F G : A -> B) `{!IsFunctor0 F, !IsFunctor0 G}
  : IsDFunctor0 idmap (colax_lax_inserter ls F G).
Proof.
  unshelve econstructor.
  - cbn; intros a b u v f g.
    exact g.
  - cbn; intros a b u v.
    apply isdfunctor0_idmap.
Defined.

(*
CoFixpoint iscat0_gendinserter (ls : Stream Laxity)
           `{IsCat0 m A} `{IsCat1 n B} (F G : A -> B)
           `{!IsFunctor0 F, !IsFunctor1 F, !IsFunctor0 G, !IsFunctor1 G}
  : IsDCat0 n (GenDInserter ls F G).
Proof.
  unshelve econstructor.
  - intros a b c ta tb tc g f.
    unfold GenDInserter in ta, tb, tc.
    cbn; destruct (head ls); cbn; intros p q.
    all: unfold GenDInserter in p, q.
    all: unfold GenDInserter.
    all: destruct (head (tail ls)); cbn in *.
    all: unfold cat_precomp, cat_postcomp in *.
    (** Should really be using a library for squares. *)
    1,4,7:refine (_ $o (_ $<o fmap_comp _ _ _)).
    1-3:refine (_ $o (cat_assoc _ _ _)^-1$).
    1-3:refine (((fmap_comp _ _ _)^-1$ $o> _) $o _).
    1-3:refine ((cat_assoc _ _ _)^-1$ $o _).
    1-3:refine (_ $o (p $o> _)).
    1-3:refine ((_ $<o q) $o _).
    1-3:by apply cat_assoc.
    1,3,5:refine (_ $oE (_ $<oE fmap_comp _ _ _)).
    1-3:refine (_ $oE (cat_assoc _ _ _)^-1$).
    1-3:refine (((fmap_comp _ _ _)^-1$ $o>E _) $oE _).
    1-3:refine ((cat_assoc _ _ _)^-1$ $oE _).
    1-3:refine (_ $oE (p $o>E _)).
    1-3:refine ((_ $<oE q) $oE _).
    1-3:by apply cat_assoc.
    all:refine (_ $o (fmap_comp _ _ _ $o> _)).
    all:refine (_ $o (cat_assoc _ _ _)).
    all:refine ((_ $<o (fmap_comp _ _ _)^-1$) $o _).
    all:refine ((cat_assoc _ _ _) $o _).
    all:refine (_ $o (_ $<o q)).
    all:refine ((p $o> _) $o _).
    all:exact (cat_assoc _ _ _)^-1$.
  - unfold GenDInserter; cbn; intros a ta.
    destruct (head ls); cbn.
    all: unfold GenDInserter.
    all: destruct (head (tail ls)); cbn in *.
    all: unfold cat_precomp, cat_postcomp in *.
    1,4,7:refine (_ $o (_ $<o fmap_id _ _)).
    1-3:refine (((fmap_id _ _)^-1$ $o> _) $o _).
    1-3:exact ((cat_idl _)^-1$ $o (cat_idr _)).
    1,3,5:refine (_ $oE (_ $<oE fmap_id _ _)).
    1-3:refine (((fmap_id _ _)^-1$ $o>E _) $oE _).
    1-3:exact ((cat_idl _)^-1$ $oE (cat_idr _)).
    all:refine (_ $o (fmap_id _ _ $o> _)).
    all:refine ((_ $<o (fmap_id _ _)^-1$) $o _).
    all:exact ((cat_idr _)^-1$ $o (cat_idl _)).
Abort.
*)

Notation DIsoInserter := (GenDInserter all_pseudo).
Notation DInserter := (GenDInserter one_colax).

Definition GenInserter (l : Stream Laxity)
           `{IsGlob m A} `{HasEquivs n B}
           (F G : A -> B) `{!IsFunctor0 F, !IsFunctor0 G}
  := sig (GenDInserter l F G).

Notation IsoInserter := (GenInserter all_pseudo).
Notation Inserter := (GenInserter one_colax).

(** For instance, the category of prespectra (resp. spectra) should be the inserter (resp. isoinserter) of the identity functor of (nat -> pType) over a functor [shift o loops]. *)


(** ** Natural transformations *)

(** A natural transformation [F $=> G] is a section of their displayed inserter.  The freedom to choose laxities at all dimensions carries over, although we insist that a transformation always goes from [F] to [G] so that the inserter is colax at the bottom level. *)

Definition Transformation {A} `{IsGlob n B} (F G : A -> B)
  := forall a, F a $-> G a.
Notation "F $=> G" := (Transformation F G).

Notation IsGenNatural1 l F G :=
  (@IsCatSect0 _ _ _ (GenDInserter (SCons colax l) F G) _ _).

Definition isgennat (ls : Stream Laxity) `{IsGlob m A} `{HasEquivs n B}
      {F : A -> B} `{!IsFunctor0 F} {G : A -> B} `{!IsFunctor0 G}
      (alpha : F $=> G) {alnat : IsGenNatural1 ls F G alpha}
      {x y : A} (f : x $-> y)
  : lHom (head ls) (alpha y $o fmap F f) (fmap G f $o alpha x)
  := fmapD (B := GenDInserter (SCons colax ls) F G) alpha f.

Notation IsNatural1 F G := (IsGenNatural1 all_pseudo F G).

Definition isnat `{IsGlob m A} `{HasEquivs n B}
      {F : A -> B} `{!IsFunctor0 F} {G : A -> B} `{!IsFunctor0 G}
      (alpha : F $=> G) {alnat : IsNatural1 F G alpha}
      {x y : A} (f : x $-> y)
  : (alpha y $o fmap F f) $<~> (fmap G f $o alpha x)
  := isgennat all_pseudo alpha f.

Global Instance isgennat_iscolaxnat (ls : Stream Laxity) `{IsGlob m A} `{HasEquivs n B}
      {F : A -> B} `{!IsFunctor0 F} {G : A -> B} `{!IsFunctor0 G}
      (alpha : F $=> G)
      {alnat : IsGenNatural1 (SCons colax ls) F G alpha}
      (x y : A)
  : IsGenNatural1 ls ((cat_postcomp (F x) (alpha y)) o (fmap' F x y))
                  ((cat_precomp (G y) (alpha x)) o (fmap' G x y))
                  (isgennat (SCons colax ls) alpha)
  := iscatsect0_fmapD alpha alnat x y.

Global Instance isgennat_ispseudonat (ls : Stream Laxity) `{IsGlob m A} `{HasEquivs n B}
      {F : A -> B} `{!IsFunctor0 F} {G : A -> B} `{!IsFunctor0 G}
      (alpha : F $=> G)
      {alnat : IsGenNatural1 (SCons pseudo ls) F G alpha}
      (x y : A)
  : IsGenNatural1 ls ((cat_postcomp (F x) (alpha y)) o (fmap' F x y))
                  ((cat_precomp (G y) (alpha x)) o (fmap' G x y))
                  (fun f => cate_fun (isgennat (SCons pseudo ls) alpha f)).
Proof.
  (** We have to nudge this from a section of the iso-inserter to a section of the inserter. *)
  pose (iscatsect0_fmapD alpha alnat x y).
  exact (iscatsect0_isdfunctor0_compose
           (colax_pseudo_inserter ls ((cat_postcomp (F x) (alpha y)) o (fmap' F x y))
                              ((cat_precomp (G y) (alpha x)) o (fmap' G x y)))
           (@fmapD _ _ _ _ _ _ alpha alnat x y)).
Defined.

Global Instance isgennat_islaxnat (ls : Stream Laxity) `{IsGlob m A} `{HasEquivs n B}
      {F : A -> B} `{!IsFunctor0 F} {G : A -> B} `{!IsFunctor0 G}
      (alpha : F $=> G)
      {alnat : IsGenNatural1 (SCons lax ls) F G alpha}
      (x y : A)
  : IsGenNatural1 ls ((cat_precomp (G y) (alpha x)) o (fmap' G x y))
                  ((cat_postcomp (F x) (alpha y)) o (fmap' F x y))
                  (isgennat (SCons lax ls) alpha).
Proof.
  (** Similarly here, we have to nudge from a section of the lax inserter in one direction to a section of the colax inserter in the other direction. *)
  pose (iscatsect0_fmapD alpha alnat x y).
  exact (iscatsect0_isdfunctor0_compose
           (colax_lax_inserter ls ((cat_precomp (G y) (alpha x)) o (fmap' G x y))
                                ((cat_postcomp (F x) (alpha y)) o (fmap' F x y)))
           (@fmapD _ _ _ _ _ _ alpha alnat x y)).
Defined.

(** If we generalized comma categories (and hence inserters) to act on category-sections rather than just functors, we could in principle iterate this approach to define modifications and higher transfors, analogously to how we iterate [isglob_forall] to define all the higher structure of [Type] and similarly for [pType].  Such a generalization seems to require either that the displayed category is an isofibration, or that we define a more general notion of inserter over a given natural transformation, and either one seems to require 2-coherent categories.  In fact, since the level of coherence seems to go down by one each time we apply a comma construction, we probably wouldn't be able to use this to define a whole oo-category of oo-categories at any fixed coherence level.  *)
