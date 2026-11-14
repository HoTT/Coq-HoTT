Require Import Basics.Equivalences Basics.Overture Basics.Tactics Basics.Trunc.
Require Import Limits.Pullback.
Require Import WildCat.Core WildCat.Equiv WildCat.EquivGpd.
Require Import WildCat.Universe WildCat.Yoneda WildCat.ZeroGroupoid.
Require Import WildCat.Induced WildCat.Opposite WildCat.NatTrans WildCat.FunctorCat.

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
Class IsCatPullback {A : Type} `{Is1Cat A} {a b c : A} (f : a $-> c) (g : b $-> c) (cat_pb : A)
  := Build_IsCatPullback' {
    cat_pb_pr1 : cat_pb $-> a;
    cat_pb_pr2 : cat_pb $-> b;
    cat_pb_glue : f $o cat_pb_pr1 $== g $o cat_pb_pr2;
    catie_cat_pb_corec_inv
      :: forall z : A, CatIsEquiv (cat_pb_corec_inv f g
                                cat_pb cat_pb_pr1 cat_pb_pr2 cat_pb_glue z);
  }.

Arguments Build_IsCatPullback' {A IsGraph Is2Graph Is01Cat H a b c}
  f g cat_pb cat_pb_pr1 cat_pb_pr2 cat_pb_glue eq : rename.

Class CatPullback {A : Type} `{Is1Cat A} {a b c : A} (f : a $-> c) (g : b $-> c)
  := Build_CatPullback' {
    cat_pb : A;
    cat_ispb :: IsCatPullback f g cat_pb;
  }.

Arguments Build_CatPullback' {A IsGraph Is2Graph Is01Cat H a b c}
  f g : rename.
Arguments cat_pb {A IsGraph Is2Graph Is01Cat H a b c} f g {pb} : rename.

Section PullbackConstructors.

  Context {A : Type} `{Is1Cat A} {a b c : A} (f : a $-> c) (g : b $-> c)
    (cat_pb : A) (cat_pb_pr1 : cat_pb $-> a) (cat_pb_pr2 : cat_pb $-> b)
    (cat_pb_glue : f $o cat_pb_pr1 $== g $o cat_pb_pr2)
    (cat_pb_corec : forall (z : A) (h : z $-> a) (k : z $-> b)
      (sq : f $o h $== g $o k), (z $-> cat_pb))
    (cat_pb_beta_pr1 : forall z h k p, cat_pb_pr1 $o cat_pb_corec z h k p $== h)
    (cat_pb_beta_pr2 : forall z h k p, cat_pb_pr2 $o cat_pb_corec z h k p $== k)
    (cat_pb_eta : forall z (k h : z $-> cat_pb)
      (p1 : cat_pb_pr1 $o k $== cat_pb_pr1 $o h)
      (p2 : cat_pb_pr2 $o k $== cat_pb_pr2 $o h), k $== h).

  (** A convenience wrapper for building [IsCatPullback]. *)
  Definition Build_IsCatPullback : IsCatPullback f g cat_pb.
  Proof.
    snapply (Build_IsCatPullback' f g cat_pb cat_pb_pr1 cat_pb_pr2 cat_pb_glue).
    intros z.
    napply isequiv_0gpd_issurjinj.
    napply Build_IsSurjInj.
    - intros [h [k p]]; simpl in h, k, p.
      exists (cat_pb_corec z h k p).
      exact (cat_pb_beta_pr1 z h k p, cat_pb_beta_pr2 z h k p).
    - intros k h p; simpl in k, h, p.
      exact (cat_pb_eta z k h (fst p) (snd p)).
  Defined.

  (** A convenience wrapper for building pullbacks. *)
  Definition Build_CatPullback : CatPullback f g
    := Build_CatPullback' f g cat_pb Build_IsCatPullback.

End PullbackConstructors.

Section Lemmata.

  Context {A : Type} `{Is1Cat A}
    {a b c : A} (f : a $-> c) (g : b $-> c)
    {cat_pb : A}
    `{!IsCatPullback f g cat_pb}
    (z : A).

  Definition cate_pb_corec_inv
    : opyon_0gpd z cat_pb $<~>
        pullback_0gpd (fmap (opyon_0gpd z) f) (fmap (opyon_0gpd z) g)
    := Build_CatEquiv _.

  Definition cate_pb_corec
    : pullback_0gpd (fmap (opyon_0gpd z) f) (fmap (opyon_0gpd z) g)
      $<~> opyon_0gpd z cat_pb
    := cate_pb_corec_inv^-1$.

  Definition cat_pb_corec
    (h : z $-> a) (k : z $-> b) (p : f $o h $== g $o k)
    : z $-> cat_pb.
  Proof.
    apply cate_pb_corec.
    simpl.
    exact (h; k; p).
  Defined.

  Definition cat_pb_corec_beta_pr1
    (h : z $-> a) (k : z $-> b) (p : f $o h $== g $o k)
    : cat_pb_pr1 $o cat_pb_corec h k p $== h
    := fst (cate_isretr cate_pb_corec_inv (h; k; p)).

  Definition cat_pb_corec_beta_pr2
    (h : z $-> a) (k : z $-> b) (p : f $o h $== g $o k)
    : cat_pb_pr2 $o cat_pb_corec h k p $== k
    := snd (cate_isretr cate_pb_corec_inv (h; k; p)).

  Definition cat_pb_postcomp_glue (h : z $-> cat_pb)
    : f $o (cat_pb_pr1 $o h) $== g $o (cat_pb_pr2 $o h)
    := (cat_assoc _ _ _)^$ $@ (cat_pb_glue $@R h) $@ cat_assoc _ _ _.

  Definition cat_pb_corec_eta_pr (h : z $-> cat_pb)
    : cat_pb_corec (cat_pb_pr1 $o h) (cat_pb_pr2 $o h) (cat_pb_postcomp_glue h) $== h
    := cate_issect cate_pb_corec_inv h.

  Definition cat_pb_corec_eta (h h' : z $-> a) (k k' : z $-> b)
    (glue_hk : f $o h $== g $o k) (glue_h'k' : f $o h' $== g $o k')
    (p1 : h $== h') (p2 : k $== k')
    : cat_pb_corec h k glue_hk $== cat_pb_corec h' k' glue_h'k'.
  Proof.
    apply (isinj_equiv_0gpd cate_pb_corec_inv).
    cbn.
    split.
    - lhs' apply (cat_pb_corec_beta_pr1 h k glue_hk).
      lhs' apply p1.
      exact (cat_pb_corec_beta_pr1 h' k' glue_h'k')^$.
    - lhs' apply (cat_pb_corec_beta_pr2 h k glue_hk).
      lhs' apply p2.
      exact (cat_pb_corec_beta_pr2 h' k' glue_h'k')^$.
  Defined.

  Definition cat_pb_pr_eta (h h' : z $-> cat_pb)
    (p1 : cat_pb_pr1 $o h $== cat_pb_pr1 $o h')
    (p2 : cat_pb_pr2 $o h $== cat_pb_pr2 $o h')
    : h $== h'.
  Proof.
    apply (isinj_equiv_0gpd cate_pb_corec_inv).
    exact (p1, p2).
  Defined.

End Lemmata.

Local Instance is0functor_pullback_0gpd_helper {A : Type} `{Is1Cat A}
  {a b c : A} (f : a $-> c) (g : b $-> c)
  : Is0Functor (A:=A^op)
    (fun z : A => pullback_0gpd (fmap (opyon_0gpd z) f) (fmap (opyon_0gpd z) g)).
Proof.
  napply Build_Is0Functor.
  intros z1 z2 k; unfold op in *.
  snapply Build_Fun01'.
  - intros [h [l p]].
    exists (h $o k).
    exists (l $o k).
    exact ((cat_assoc _ _ _)^$ $@ (p $@R k) $@ cat_assoc _ _ _).
  - intros [h1 [l1 p1]] [h2 [l2 p2]] [qh ql].
    exact (qh $@R k, ql $@R k).
Defined.

Local Instance is1functor_pullback_0gpd_helper {A : Type} `{Is1Cat A}
  {a b c : A} (f : a $-> c) (g : b $-> c)
  : Is1Functor (A:=A^op)
    (fun z : A => pullback_0gpd (fmap (opyon_0gpd z) f) (fmap (opyon_0gpd z) g)).
Proof.
  napply Build_Is1Functor.
  - intros z1 z2 k1 k2 p [h [l glue]].
    exact (h $@L p, l $@L p).
  - intros z [h [l glue]].
    exact (cat_idr h, cat_idr l).
  - intros z1 z2 z3 k1 k2 [h [l glue]].
    split; napply cat_assoc_opp; exact _.
Defined.

Definition natequiv_cat_pb_corec_inv {A : Type} `{Is1Cat A}
  {a b c : A} (f : a $-> c) (g : b $-> c) (cat_pb : A) `{!IsCatPullback f g cat_pb}
  : NatEquiv (A:=A^op) (yon_0gpd cat_pb)
    (fun z : A => pullback_0gpd (fmap (opyon_0gpd z) f) (fmap (opyon_0gpd z) g)).
Proof.
  snapply Build_NatEquiv.
  - exact (cate_pb_corec_inv f g).
  - exact (is1natural_yoneda_0gpd cat_pb
      (fun z : A => pullback_0gpd (fmap (opyon_0gpd z) f) (fmap (opyon_0gpd z) g))
      (cat_pb_pr1; (cat_pb_pr2; cat_pb_glue))).
Defined.

(** ** Uniqueness of pullbacks *)

Definition cat_pb_unique {A : Type} `{HasEquivs A}
  {a b c : A} (f : a $-> c) (g : b $-> c)
  (pb1 : A) `{!IsCatPullback f g pb1}
  (pb2 : A) `{!IsCatPullback f g pb2}
  : pb1 $<~> pb2.
Proof.
  napply yon_equiv_0gpd.
  refine (natequiv_compose _ (natequiv_cat_pb_corec_inv f g pb1)).
  exact (natequiv_inverse (natequiv_cat_pb_corec_inv f g pb2)).
Defined.

(** ** Induced pullbacks *)

Section InducedFromEquiv.

  Context {A : Type} `{he : HasEquivs A} {a b c : A} {f : a $-> c} {g : b $-> c}
    (cat_pb : A) `{!IsCatPullback f g cat_pb}
    (y : A) (h : y $<~> cat_pb).

  (** A categorical equivalence into a pullback induces a pullback structure on the domain. *)
  Local Instance cat_pb_equiv_pb : IsCatPullback f g y.
  Proof.
    snapply (Build_IsCatPullback f g y).
    - exact (cat_pb_pr1 $o h).
    - exact (cat_pb_pr2 $o h).
    - exact (cat_pb_postcomp_glue f g _ h).
    - intros z k1 k2 p.
      exact (h^-1$ $o cat_pb_corec f g z k1 k2 p).
    - intros z k1 k2 p; cbn beta.
      refine (_ $@ cat_pb_corec_beta_pr1 f g z k1 k2 p).
      refine (cat_assoc _ _ _ $@ _).
      apply cat_postwhisker.
      apply compose_h_Vh.
    - intros z k1 k2 p; cbn beta.
      refine (_ $@ cat_pb_corec_beta_pr2 f g z k1 k2 p).
      refine (cat_assoc _ _ _ $@ _).
      apply cat_postwhisker.
      apply compose_h_Vh.
    - cbn beta; intros z k k' p1 p2.
      napply (cate_monic_equiv h).
      napply (cat_pb_pr_eta f g z).
      + exact (cat_assoc_opp _ _ _ $@ p1 $@ cat_assoc _ _ _).
      + exact (cat_assoc_opp _ _ _ $@ p2 $@ cat_assoc _ _ _).
  Defined.

  (** The induced first projection is given by the equivalence. *)
  Definition cat_pb_pr1_comp
    : cat_pb_pr1 (cat_pb:=y) $== cat_pb_pr1 $o h
    := Id _.

  (** The induced second projection is given by the equivalence. *)
  Definition cat_pb_pr2_comp
    : cat_pb_pr2 (cat_pb:=y) $== cat_pb_pr2 $o h
    := Id _.

  (** The induced corecursion is given by the equivalence. *)
  Definition cat_pb_corec_comp {z : A} (k1 : z $-> a) (k2 : z $-> b) (p : f $o k1 $== g $o k2)
    : h $o cat_pb_corec (cat_pb:=y) f g z k1 k2 p
      $== cat_pb_corec f g z k1 k2 p
    := compose_h_Vh _ _.

End InducedFromEquiv.

(** ** Symmetry of pullbacks *)

Definition iscatpullback_sym {A : Type} `{Is1Cat A}
  {a b c : A} {f : a $-> c} {g : b $-> c}
  (cat_pb : A) `{!IsCatPullback f g cat_pb}
  : IsCatPullback g f cat_pb.
Proof.
  snapply (Build_IsCatPullback g f cat_pb).
  - exact cat_pb_pr2.
  - exact cat_pb_pr1.
  - exact cat_pb_glue^$.
  - intros z h k p.
    exact (cat_pb_corec f g z k h p^$).
  - intros z h k p.
    exact (cat_pb_corec_beta_pr2 f g z k h p^$).
  - intros z h k p.
    exact (cat_pb_corec_beta_pr1 f g z k h p^$).
  - intros z k h p1 p2.
    exact (cat_pb_pr_eta f g z k h p2 p1).
Defined.


(** ** Categories with pullbacks *)

Class HasPullbacks (A : Type) `{Is1Cat A}
  := has_pullbacks :: forall {a b c} (f : a $-> c) (g : b $-> c), CatPullback f g.

(** ** Pullbacks in induced wild categories *)

Section Induced.

  (** If the 1-category structure on [A] is induced from that on [B] along a map [F], the pullback of [F f] and [F g] exists in [B], and that pullback object is in the image of [F] up to categorical equivalence, then the preimage is also a pullback.  Typically this will be applied with [h] being an identity equivalence (or [reflexivity]), but it would be awkward to state this lemma assuming that. *)
  Instance cat_pb_induced {A B} `{Is1Cat B} `{!HasEquivs B}
    (F : A -> B)
    {a b c : A} (f : F a $-> F c) (g : F b $-> F c)
    {cat_pb_b : B} `{!IsCatPullback f g cat_pb_b}
    (cat_pb_a : A) (h : F cat_pb_a $<~> cat_pb_b)
    : CatPullback (A:=A) (H:=is1cat_induced F) f g.
  Proof.
    pose (cat_pb_equiv_pb (A:=B) cat_pb_b (F cat_pb_a) h).
    napply (Build_CatPullback (H:=is1cat_induced F) f g cat_pb_a).
    - exact (cat_pb_glue (cat_pb:=F cat_pb_a)).
    - intro z; exact (cat_pb_corec_beta_pr1 f g (F z)).
    - intro z; exact (cat_pb_corec_beta_pr2 f g (F z)).
    - intro z; exact (cat_pb_pr_eta f g (F z)).
  Defined.

  Instance haspullbacks_induced {A B} `{HasPullbacks B} `{!HasEquivs B}
    (F : A -> B)
    (K : forall (a b c : A) (f : F a $-> F c) (g : F b $-> F c), exists q, F q $<~> cat_pb f g)
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
  - intros Z h k p.
    exact (fun z => (h z; k z; p z)).
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
  - intros Z h k p.
    exact (equiv_pullback_0gpd_corec f g (h; k; p)).
  - reflexivity.
  - reflexivity.
  - exact (pullback_0gpd_homotopic f g).
Defined.
