Require Import Basics.Equivalences Basics.Overture Basics.Tactics Basics.Trunc.
Require Import Limits.Pullback.
Require Import WildCat.Core WildCat.Equiv WildCat.EquivGpd.
Require Import WildCat.Universe WildCat.Yoneda WildCat.Graph WildCat.ZeroGroupoid.
Require Import WildCat.Induced.

(** * Categories with pullbacks *)

(** When [pb] is the source object in a commuting square, then for any object [z] we get a commuting square of 0-groupoids by applying the functor [z $-> -], which is [opyon_0gpd z].  Thus there is a natural map of 0-groupoids from [z $-> pb] to the 0-groupoid pullback of
<<
                      (z $-> b)
                          |
                          |
                          v
        (z $-> a) --> (z $-> c)
>>
In this diagram, the hom sets are regarded as 0-groupoids and the top-level arrows are morphisms of 0-groupoids (0-functors). *)

Definition cat_pb_corec_inv {A : Type} `{Is1Cat A}
  {a b c : A} (f : a $-> c) (g : b $-> c)
  (pb : A) (pra : pb $-> a) (prb : pb $-> b) (glue : f $o pra $== g $o prb)
  (z : A)
  : opyon_0gpd z pb $-> pullback_0gpd (fmap (opyon_0gpd z) f) (fmap (opyon_0gpd z) g).
Proof.
  snapply equiv_pullback_0gpd_corec.
  exists (fmap _ pra).  (* The underscores are [opyon_0gpd z]. *)
  exists (fmap _ prb).
  refine ((fmap_comp _ pra f)^$ $@ _ $@ fmap_comp _ prb g).
  exact (fmap2 _ glue).
Defined.

(** A pullback is an object completing [f] and [g] to a commuting square such that the map above is an equivalence of 0-groupoids for each [z].  The name [Pullback] is used for the construction in Limits.Pullback, so we use CatPullback here. *)
Class CatPullback {A : Type} `{Is1Cat A} {a b c : A} (f : a $-> c) (g : b $-> c)
  := Build_CatPullback' {
    cat_pb : A;
    cat_pb_pr1 : cat_pb $-> a;
    cat_pb_pr2 : cat_pb $-> b;
    cat_pb_glue : f $o cat_pb_pr1 $== g $o cat_pb_pr2;
    cat_isequiv_cat_pullback_corec_inv
      :: forall z : A, CatIsEquiv (cat_pb_corec_inv f g
                                cat_pb cat_pb_pr1 cat_pb_pr2 cat_pb_glue z);
  }.

Arguments Build_CatPullback' {A IsGraph Is2Graph Is01Cat H a b c}
  f g cat_pb cat_pb_pr1 cat_pb_pr2 cat_pb_glue eq : rename.
Arguments cat_pb {A IsGraph Is2Graph Is01Cat H a b c} f g {pb} : rename.

Definition cate_pb_corec_inv {A : Type} `{Is1Cat A}
  {a b c : A} (f : a $-> c) (g : b $-> c)
  {pb : CatPullback f g}
  (z : A)
  : opyon_0gpd z (cat_pb _ _) $<~>
      pullback_0gpd (fmap (opyon_0gpd z) f) (fmap (opyon_0gpd z) g)
  := Build_CatEquiv _.

Definition cat_pb_corec {A : Type} `{Is1Cat A}
  {a b c : A} {f : a $-> c} {g : b $-> c}
  {pb : CatPullback f g} {z : A}
  (h : z $-> a) (k : z $-> b) (p : f $o h $== g $o k)
  : opyon_0gpd z (cat_pb f g).
Proof.
  apply (cate_pb_corec_inv f g z)^-1$.
  simpl.
  exact (h; k; p).
Defined.

Definition cat_pb_corec_beta_pr1 {A : Type} `{Is1Cat A}
  {a b c : A} (f : a $-> c) (g : b $-> c)
  {pb : CatPullback f g} (z : A)
  (h : z $-> a) (k : z $-> b) (p : f $o h $== g $o k)
  : cat_pb_pr1 $o cat_pb_corec h k p $== h
  := fst (cate_isretr (cate_pb_corec_inv f g z) (h; k; p)).

Definition cat_pb_corec_beta_pr2 {A : Type} `{Is1Cat A}
  {a b c : A} (f : a $-> c) (g : b $-> c)
  {pb : CatPullback f g} (z : A)
  (h : z $-> a) (k : z $-> b) (p : f $o h $== g $o k)
  : cat_pb_pr2 $o cat_pb_corec h k p $== k
  := snd (cate_isretr (cate_pb_corec_inv f g z) (h; k; p)).

(** A convenience wrapper for building pullbacks. *)
(** TODO: maybe unbundle khp?  Or bundle them above to match? *)
Definition Build_CatPullback {A : Type} `{Is1Cat A} {a b c : A} (f : a $-> c) (g : b $-> c)
  (cat_pb : A) (cat_pb_pr1 : cat_pb $-> a) (cat_pb_pr2 : cat_pb $-> b)
  (cat_pb_glue : f $o cat_pb_pr1 $== g $o cat_pb_pr2)
  (cat_pb_corec : forall z : A,
      pullback_0gpd (fmap (opyon_0gpd z) f) (fmap (opyon_0gpd z) g) -> (z $-> cat_pb))
  (cat_pb_beta_pr1 : forall z khp, cat_pb_pr1 $o cat_pb_corec z khp $-> khp.1)
  (cat_pb_beta_pr2 : forall z khp, cat_pb_pr2 $o cat_pb_corec z khp $-> khp.2.1)
  (cat_pb_eta : forall z (k : z $-> cat_pb) (h : z $-> cat_pb)
                (p1 : cat_pb_pr1 $o k $== cat_pb_pr1 $o h)
                (p2 : cat_pb_pr2 $o k $== cat_pb_pr2 $o h), k $== h)
  : CatPullback f g.
Proof.
  snapply (Build_CatPullback' f g cat_pb cat_pb_pr1 cat_pb_pr2 cat_pb_glue).
  intros z.
  napply isequiv_0gpd_issurjinj.
  napply Build_IsSurjInj.
  - intros khp.
    exists (cat_pb_corec z khp).
    exact (cat_pb_beta_pr1 z khp, cat_pb_beta_pr2 z khp).
  - intros k h p.
    exact (cat_pb_eta z k h (fst p) (snd p)).
Defined.

Class HasPullbacks (A : Type) `{Is1Cat A}
  := has_pullbacks :: forall {a b c} (f : a $-> c) (g : b $-> c), CatPullback f g.

(** ** Uniqueness of pullbacks *)

Definition compare_cat_pb {A : Type} `{Is1Cat A}
  {a b c : A} {f : a $-> c} {g : b $-> c}
  (pb1 pb2 : CatPullback f g)
  : pb1.(cat_pb _ _) $-> pb2.(cat_pb _ _)
  := cat_pb_corec pb1.(cat_pb_pr1) pb1.(cat_pb_pr2) pb1.(cat_pb_glue).

Definition compose_compare_cat_pb {A : Type} `{Is1Cat A}
  {a b c : A} {f : a $-> c} {g : b $-> c}
  (pb1 pb2 : CatPullback f g)
  : compare_cat_pb pb1 pb2 $o compare_cat_pb pb2 pb1 $== Id pb2.(cat_pb f g).
Proof.
  apply (isinj_equiv_0gpd (cate_pb_corec_inv f g _)).
  simpl; unfold cat_postcomp.
  split.
  - refine (cat_assoc_opp _ _ _ $@ _ $@ (cat_idr _)^$).
    refine ((cat_pb_corec_beta_pr1 _ _ _ _ _ _ $@R _) $@ _).
    apply cat_pb_corec_beta_pr1.
  - refine (cat_assoc_opp _ _ _ $@ _ $@ (cat_idr _)^$).
    refine ((cat_pb_corec_beta_pr2 _ _ _ _ _ _ $@R _) $@ _).
    apply cat_pb_corec_beta_pr2.
Defined.

Definition catie_compare_cat_pb {A : Type} `{Is1Cat A} `{!HasEquivs A}
  {a b c : A} (f : a $-> c) (g : b $-> c)
  (pb1 pb2 : CatPullback f g)
  : CatIsEquiv (compare_cat_pb pb1 pb2).
Proof.
  srapply catie_adjointify.
  1: exact (compare_cat_pb pb2 pb1).
  all: apply compose_compare_cat_pb.
Defined.

(** ** Symmetry of pullbacks *)

Definition flip_cat_pb_corec_inv {A : Type} `{Is1Cat A}
  {a b c : A} (f : a $-> c) (g : b $-> c)
  (pb : A) (pra : pb $-> a) (prb : pb $-> b) (glue : f $o pra $== g $o prb)
  (z : A)
  : cate_flip_pullback_0gpd _ _ $o
      cat_pb_corec_inv f g pb pra prb glue z $==
      cat_pb_corec_inv g f pb prb pra (glue^$) z.
Proof.
  intro h; cbn.
  split; reflexivity.
Defined.

Definition flip_cat_pb {A : Type} `{Is1Cat A}
  {a b c : A} (f : a $-> c) (g : b $-> c)
  (pb : CatPullback f g)
  : CatPullback g f.
Proof.
  napply (Build_CatPullback' g f).
  intro z.
  rapply (catie_homotopic _ (flip_cat_pb_corec_inv f g _ _ _ _ z)).
Defined.

Definition flip_cat_pb_pr1_pr2 {A : Type} `{Is1Cat A}
  {a b c : A} (f : a $-> c) (g : b $-> c)
  (pb : CatPullback f g)
  : (flip_cat_pb f g pb).(cat_pb_pr1) $== cat_pb_pr2
  := Id _.

Definition flip_pullback_pr2_pr1 {A : Type} `{Is1Cat A}
  {a b c : A} (f : a $-> c) (g : b $-> c)
  (pb : CatPullback f g)
  : (flip_cat_pb f g pb).(cat_pb_pr2) $== cat_pb_pr1
  := Id _.

(** ** Pullbacks in induced wild categories *)

Section Induced.

  (** If the 1-category structure on [A] is induced from that on [B] along a map [F], the pullback of [F f] and [F g] exists in [B], and that pullback object is in the image of [F], then the preimage is also a pullback.  Typically this will be applied with [h] being [idpath], but it would be awkward to state this lemma assuming that. *)
  Instance cat_pb_induced {A B} `{Is1Cat B}
    (F : A -> B)
    {a b c : A} (f : F a $-> F c) (g : F b $-> F c)
    {p : CatPullback f g}
    (q : A) (h : F q = cat_pb f g)
    : CatPullback (A:=A) (H:=is1cat_induced F) f g.
  Proof.
    destruct p as [pb pr1 pr2 glue iseq].
    unfold cat_pb in h; destruct h.
    exact (Build_CatPullback' (H:=is1cat_induced F) f g q pr1 pr2 glue (iseq o F)).
  Defined.

  Instance haspullbacks_induced {A B} `{HasPullbacks B}
    (F : A -> B)
    (K : forall (a b c : A) (f : F a $-> F c) (g : F b $-> F c), exists q, F q = cat_pb f g)
    : HasPullbacks A (H:=is1cat_induced F).
  Proof.
    intros a b c f g.
    destruct (K a b c f g) as [q h].
    exact (cat_pb_induced F f g q h).
  Defined.

End Induced.

(** ** Examples *)

(** These examples are here for dependency reasons. *)

(** *** Pullbacks in Type *)

(** Because these are 1-categorical pullbacks, the standard pullbacks of types only satisfy our definition when the corner type is 0-truncated.  It is unlikely that general diagrams have 1-pullbacks. *)

Instance haspullbacks_type {A B C : Type} `{IsTrunc 0 C}
  (f : A $-> C) (g : B $-> C)
  : CatPullback f g.
Proof.
  snapply (Build_CatPullback f g (Pullback f g) pullback_pr1 pullback_pr2).
  - apply pullback_commsq.
  - intros Z khp.
    exact (pullback_corec_uncurried f g khp).
  - reflexivity.
  - reflexivity.
  - intros Z k h p1 p2.
    srapply (pullback_homotopic k h p1 p2).
    intro z.
    apply path_ishprop. (* Here we use that [C] is 0-truncated. *)
Defined.

(** *** Pullbacks in ZeroGpd *)

Instance haspullbacks_0gpd : HasPullbacks ZeroGpd.
Proof.
  intros G H K f g.
  snapply (Build_CatPullback f g (pullback_0gpd f g)
             (pullback_0gpd_pr1 f g) (pullback_0gpd_pr2 f g) (pullback_0gpd_glue f g)).
  - intros Z khp.
    exact (equiv_pullback_0gpd_corec f g khp).
  - reflexivity.
  - reflexivity.
  - exact (pullback_0gpd_homotopic f g).
Defined.
