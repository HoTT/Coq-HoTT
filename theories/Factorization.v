(* -*- mode: coq; mode: visual-line -*- *)

(** * Factorizations and factorization systems. *)

Require Import HoTT.Basics.
Require Import types.Record types.Sigma types.Universe types.Arrow types.Forall types.Paths.
Require Import ReflectiveSubuniverse Modality HProp.
Require Import HoTT.Tactics.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** ** Factorizations *)

Section Factorization.

  (** It's important that these are all declared with a single [Context] command, so that the marker [@{i}] refers to the same universe level in all of them. *)
  Context (class1 class2 : forall (X Y : Type@{i}), (X -> Y) -> Type@{i})
          `{forall (X Y : Type@{i}) (g:X->Y), IsHProp (class1 _ _ g)}
          `{forall (X Y : Type@{i}) (g:X->Y), IsHProp (class2 _ _ g)}
          {A B : Type@{i}} (f : A -> B).

  (** A factorization of [f] into a first factor lying in [class1] and a second factor lying in [class2]. *)
  Record Factorization :=
    { intermediate : Type ;
      factor1 : A -> intermediate ;
      factor2 : intermediate -> B ;
      fact_factors : factor2 o factor1 == f ;
      inclass1 : class1 _ _ factor1 ;
      inclass2 : class2 _ _ factor2
    }.

  Lemma issig_Factorization :
    { I : Type & { g : A -> I & { h : I -> B & { p : h o g == f &
      { gin1 : class1 _ _ g & class2 _ _ h }}}}}
      <~> Factorization.
  Proof.
    issig5 Build_Factorization intermediate factor1 factor2 fact_factors inclass1 inclass2.
  Defined.

  (* This enables [simpl rewrite] to unfold [compose]. *)
  Local Arguments compose / .

  (** A path between factorizations is equivalent to a structure of the following sort. *)
  Record PathFactorization (fact fact' : Factorization) :=
    { path_intermediate : intermediate fact <~> intermediate fact' ;
      path_factor1 : path_intermediate o factor1 fact == factor1 fact' ;
      path_factor2 : factor2 fact == factor2 fact' o path_intermediate ;
      path_fact_factors : forall a, path_factor2 (factor1 fact a)
                          @ ap (factor2 fact') (path_factor1 a)
                          @ fact_factors fact' a
                          = fact_factors fact a
    }.

  (** It's easy to extract such a structure from an actual path between factorizations. *)
  Definition pathfactorization_path (fact fact' : Factorization)
    : (fact = fact') -> PathFactorization fact fact'.
  Proof.
    intros [].
    exact (Build_PathFactorization fact fact
             (equiv_idmap (intermediate fact))
             (fun a => 1) (fun x => 1) (fun a => concat_1p _)).
  Defined.

  (** The converse, however, is more work. In the proof of Theorem 7.6.6, the book glosses over this theorem with the phrase "by univalence and the characterization of paths and transport in Sigma-types, function types, and path types".  Which is arguably fair informally, because it's "obvious", but it turns out to be a good deal of work to keep track of all the transport lemmas and apply naturality in the right places. *)
  Definition path_factorization `{Univalence} (fact fact' : Factorization)
  : PathFactorization fact fact' -> (fact = fact').
  Proof.
    intros pf.
    pose (II := path_intermediate _ _ pf).
    pose (ff1 := path_factor1 _ _ pf).
    pose (ff2 := path_factor2 _ _ pf).
    pose (fff := path_fact_factors _ _ pf).
    (* The idea is of course to decompose [Factorization] as a sigma and use [path_sigma] over and over again.  It's fairly easy to insert [II], [ff1], and [ff2] in the right places. *)
    apply ((ap issig_Factorization^-1)^-1); cbn.
    refine (path_sigma' _ _ _); cbn.
    { (* Here we use [II]. *)
      refine (path_universe II). }
    refine (transport_sigma_' _ _ @ _); cbn.
    refine (path_sigma' _ _ _); cbn.
    { (* Here we use [ff1]. *)
      apply path_arrow; intros a.
      refine (transport_arrow_fromconst (C := idmap) _ _ a @ _).
      etransitivity; [ apply transport_path_universe | ].
      apply ff1. }
    refine (transport_sigma' _ _ @ _); cbn.
    refine (path_sigma' _ _ _); cbn.
    { (* Here we use [ff2].  It's a bit more complicated because the way we stated [ff2] isn't exactly the way it appears naturally here. *)
      apply path_arrow; intros a.
      refine (transport_arrow_toconst (B := idmap) _ _ a @ _).
      etransitivity; [ apply ap, transport_path_universe_V | ].
      etransitivity; [ apply ff2 | ].
      unfold compose; apply ap.
      apply eisretr. }
    (* Now we have a gigantic mess, but fortunately it simplifies a great deal because the last two components are hprops. *)
    refine (transport_sigma (A := intermediate fact' -> B)
                            (B := fun g => g o factor1 fact' == f)
                            _ _ @ _); cbn.
    refine (path_sigma' _ _ _); cbn.
    2:apply path_ishprop.
    (* It's still pretty scary-looking, but we press ahead undaunted, looking for transport redexes and path redexes. *)
    apply path_forall; intros a.
    unfold pointwise_paths.
    rewrite transport_forall_constant, transport_paths_Fl.
    rewrite ap_apply_l, ap10_path_arrow.
    rewrite transport_sigma_'; cbn.
    rewrite transport_forall_constant, transport_paths_Fl.
    simpl rewrite (@ap_compose _ _ _
                    (fun g:A->intermediate fact' => g a)
                    (fun x => transport (fun X => X -> B) (path_universe II)
                                        (factor2 fact) x)).
    rewrite ap_apply_l, ap10_path_arrow.
    (* Now we start having to look for naturality properties, so [long_path_scope] is useful. *)
    Open Scope long_path_scope.
    do 2 apply moveR_Vp; repeat rewrite concat_p_pp.
    (* We begin with [ap_transport_arrow_toconst] *)
    rewrite (ap_transport_arrow_toconst (B := idmap) (C := B)).
    (* Now we set up for a naturality *)
    simpl rewrite (@ap_compose _ _ _ (transport idmap (path_universe II)^)
                               (factor2 fact)).
    rewrite <- ap_p_pp; rewrite_moveL_Mp_p.
    Fail rewrite (concat_Ap ff2). (* Maybe one day rewrite will be smarter *)
    refine (_ @ (((concat_Ap ff2 _)^ @@ 1) @@ 1)).
    (* Next is another naturality  *)
    rewrite ap_compose.
    Fail rewrite <- ap_p_pp.    (* Yeah, rewrite. *)
    refine (_ @ (ap_p_pp (factor2 fact') _ _ _ @@ 1)).
    repeat rewrite (ap_pp (transport idmap (path_universe II)^)).
    rewrite concat_pA_p.
    (* And another one *)
    repeat rewrite (ap_pp II).
    rewrite <- (ap_compose (II^-1) II); unfold compose.
    rewrite (concat_pA1_p (eisretr II) (ff1 a)).
    (* Now we use the triangle identity of our equivalence [II]. *)
    rewrite (ap_pp (factor2 fact')).
    unfold compose; rewrite eisadj.
    (* And one more naturality *)
    repeat rewrite concat_p_pp.
    repeat rewrite <- ap_pp.
    rewrite <- ap_compose.
    (* Here we [refine] rather than [rewrite] to specify exactly *where* we want to apply naturality. *)
    refine (_ @ (((concat_Ap ff2 _) @@ 1) @@ 1)).
    rewrite_moveL_Mp_p.
    (* Finally we can use [fff]! *)
    refine (_ @ (fff a)^).
    do 2 rewrite_moveR_Vp_p.
    (* Now we still have a mess, but with a little futzing we can put it into a form that we can do path induction over.  The point is to make it all a function of [path_universe II].  In particular, we need to eliminate [eissect II], which we do with [transport_path_universe_Vp]. *)
    rewrite (ap_pp (transport idmap (path_universe II)^)).
    with_rassoc ltac:(rewrite (ap_pp (factor2 fact))).
    rewrite transport_path_universe_Vp.
    (* This mess is completely general in [path_universe II]! *)
    fold II. set (p := path_universe II); clearbody p.
    case p; cbn. auto with path_hints.
    Close Scope long_path_scope.
  Qed.

End Factorization.

Arguments PathFactorization {class1 class2 A B f} fact fact'.

(** ** Factorization Systems *)

(** A ("unique" or "orthogonal") factorization system consists of a couple of classes of maps, closed under composition, such that every map admits a unique factorization. *)
Record FactorizationSystem :=
  { class1 : forall {X Y : Type@{i}}, (X -> Y) -> Type ;
    ishprop_class1 : forall {X Y : Type@{i}} (g:X->Y), IsHProp (class1 g) ;
    class1_compose : forall {X Y Z : Type@{i}} (g:X->Y) (h:Y->Z),
                       class1 g -> class1 h -> class1 (h o g) ;
    class2 : forall {X Y : Type@{i}}, (X -> Y) -> hProp ;
    ishprop_class2 : forall {X Y : Type@{i}} (g:X->Y), IsHProp (class2 g) ;
    class2_compose : forall {X Y Z : Type@{i}} (g:X->Y) (h:Y->Z),
                       class2 g -> class2 h -> class2 (h o g) ;
    (** Morally, the uniqueness of factorizations says that [Factorization class1 class2 f] is contractible.  However, in practice we always *prove* that by way of [path_factorization], and we frequently want to *use* the components of a [PathFactorization] as well.  Thus, as data we store the canonical factorization and a [PathFactorization] between any two such, and prove in a moment that this implies contractibility of the space of factorizations. *)
    factor : forall {X Y : Type@{i}} (f:X->Y), Factorization@{i i} (@class1) (@class2) f ;
    path_factor : forall {X Y : Type@{i}} (f:X->Y)
                         (fact : Factorization@{i i} (@class1) (@class2) f)
                         (fact' : Factorization@{i i} (@class1) (@class2) f),
                    PathFactorization@{i i i} fact fact'
  }.

Global Existing Instances ishprop_class1 ishprop_class2.

Section FactSys.

  Context `{Univalence} (factsys : FactorizationSystem).

  Definition Build_Factorization' {X Y}
    := @Build_Factorization (@class1 factsys) (@class2 factsys) X Y.

  Definition Build_PathFactorization' {X Y}
    := @Build_PathFactorization (@class1 factsys) (@class2 factsys) X Y.

  (** The type of factorizations is, as promised, contractible. *)
  Theorem contr_factor {X Y} (f : X -> Y)
  : Contr (Factorization (@class1 factsys) (@class2 factsys) f).
  Proof.
    apply contr_inhabited_hprop.
    - apply hprop_allpath.
      intros fact fact'.
      apply path_factorization; try exact _.
      apply path_factor.
    - apply factor.
  Defined.

  (** The two classes of maps are automatically orthogonal, i.e. any commutative square from a [class1] map to a [class2] map has a unique diagonal filler.  For now, we only bother to define the lift; in principle we ought to show that the type of lifts is contractible. *)
  Context {A B X Y : Type@{i}}
          (i : A -> B) (c1i : class1 factsys i)
          (p : X -> Y) (c2p : class2 factsys p)
          (f : A -> X) (g : B -> Y) (h : p o f == g o i).

  (** We define the lift together with all the data proving that it is a lift at once, so we only have to do the setup once. *)
  Local Definition lift_factsys_all
  : { s : B -> X & { k : s o i == f & { l : p o s == g &
      forall a, ap p (k a)^ @ l (i a) = h a }}}.
  Proof.
    destruct (factor factsys f) as [C f1 f2 ff c1f1 c2f2].
    destruct (factor factsys g) as [D g1 g2 gf c1g1 c2g2].
    pose (fact := Build_Factorization' (p o f) C f1 (p o f2)
                    (fun a => ap p (ff a))
                    c1f1 (class2_compose factsys f2 p c2f2 c2p)).
    pose (fact' := Build_Factorization' (p o f) D (g1 o i) g2
                    (fun a => gf (i a) @ (h a)^)
                    (class1_compose factsys i g1 c1i c1g1) c2g2).
    destruct (path_factor factsys (p o f) fact fact')
      as [q q1 q2 r]; simpl in *; clear fact fact'.
    exists (f2 o q^-1 o g1).
    refine (_ ; (_ ; _)); intros x; unfold compose.
    - refine (ap (f2 o q^-1) (q1 x)^ @ _); unfold compose.
      transitivity (f2 (f1 x)).
      + apply ap, eissect.
      + apply ff.
    - refine (q2 _ @ _); unfold compose.
      transitivity (g2 (g1 x)).
      + apply ap, eisretr.
      + apply gf.
    - Open Scope long_path_scope.
      (* First we massage the hypothesis [r] and apply it. *)
      specialize (r x); rewrite concat_p_pp in r.
      apply moveL_pM, moveR_Vp in r.
      refine (_ @ r); clear r.
      (* Now we can cancel some whiskered paths on both sides. *)
      repeat rewrite inv_pp; repeat rewrite ap_pp; rewrite ap_V.
      repeat rewrite concat_pp_p; apply whiskerL.
      repeat rewrite concat_p_pp; apply whiskerR.
      (* Next we set up for a naturality. *)
      rewrite ap_compose, <- ap_pp, <- inv_pp.
      Fail rewrite <- ap_pp.    (* rewrite, I hardly knew ye *)
      refine (((ap (ap p) (inverse2 (ap_pp f2 _ _)^) @@ 1) @@ 1) @ _).
      rewrite <- ap_V, <- ap_compose.
      Fail rewrite concat_Ap.   (* la la la *)
      refine ((concat_Ap q2 _ @@ 1) @ _).
      (* Now we can cancel another path *)
      rewrite concat_pp_p; apply whiskerL.
      (* And set up for an application of [ap]. *)
      rewrite ap_compose.
      Fail rewrite <- ap_pp.    (* again? *)
      refine ((ap_pp g2 _ _)^ @ _).
      apply ap.
      (* Now we apply the triangle identity [eisadj]. *)
      rewrite inv_pp, ap_pp, ap_V.
      Fail rewrite <- eisadj.   (* oh, let this be the last time please *)
      refine ((((inverse2 (eisadj q (f1 x))^) @@ 1) @@ 1) @ _).
      (* Finally, we rearrange and it becomes a naturality square. *)
      rewrite concat_pp_p; apply moveR_Vp.
      rewrite <- ap_V, inv_V, <- ap_compose.
      exact (concat_A1p (eisretr q) (q1 x)).
      Close Scope long_path_scope.
  Defined.

  Definition lift_factsys : B -> X
    := lift_factsys_all.1.

  Definition lift_factsys_tri1 : lift_factsys o i == f
    := lift_factsys_all.2.1.

  Definition lift_factsys_tri2 : p o lift_factsys == g
    := lift_factsys_all.2.2.1.

  (* Make this abstract, because we used [rewrite] in that part of the proof. *)
  Definition lift_factsys_square
  : forall a, ap p (lift_factsys_tri1 a)^ @ lift_factsys_tri2 (i a) = h a.
  Proof.
    exact lift_factsys_all.2.2.2.
  Qed.

End FactSys.
