(** * Factorizations and factorization systems. *)

Require Import HoTT.Basics HoTT.Types.
Require Import Extensions Homotopy.IdentitySystems.
Local Open Scope path_scope.


(** ** Factorizations *)

Section Factorization.
  Universes ctxi.
  Context {class1 class2 : forall (X Y : Type@{ctxi}), (X -> Y) -> Type@{ctxi}}
          `{forall (X Y : Type@{ctxi}) (g:X->Y), IsHProp (class1 _ _ g)}
          `{forall (X Y : Type@{ctxi}) (g:X->Y), IsHProp (class2 _ _ g)}
          {A B : Type@{ctxi}} {f : A -> B}.

  (** A factorization of [f] into a first factor lying in [class1] and a second factor lying in [class2]. *)
  Record Factorization :=
    { intermediate : Type@{ctxi} ;
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
    issig.
  Defined.

  (** A path between factorizations is equivalent to a structure of the following sort. *)
  Record PathFactorization {fact fact' : Factorization} :=
    { path_intermediate : intermediate fact <~> intermediate fact' ;
      path_factor1 : path_intermediate o factor1 fact == factor1 fact' ;
      path_factor2 : factor2 fact == factor2 fact' o path_intermediate ;
      path_fact_factors : forall a, path_factor2 (factor1 fact a)
                          @ ap (factor2 fact') (path_factor1 a)
                          @ fact_factors fact' a
                          = fact_factors fact a
    }.
  Arguments PathFactorization fact fact' : clear implicits.

  Lemma issig_PathFactorization (fact fact' : Factorization) :
    { path_intermediate : intermediate fact <~> intermediate fact' &
    { path_factor1 : path_intermediate o factor1 fact == factor1 fact' &
    { path_factor2 : factor2 fact == factor2 fact' o path_intermediate &
       forall a, path_factor2 (factor1 fact a)
                              @ ap (factor2 fact') (path_factor1 a)
                              @ fact_factors fact' a
                 = fact_factors fact a }}}
      <~> PathFactorization fact fact'.
  Proof.
    issig.
  Defined.

  Definition equiv_path_factorization `{Univalence}
             (fact fact' : Factorization)
    : PathFactorization fact fact' <~> fact = fact'.
  Proof.
    refine (_ oE (issig_PathFactorization fact fact')^-1).
    revert fact fact'; apply (equiv_path_issig_contr issig_Factorization).
    { intros [I [f1 [f2 [ff [oc1 oc2]]]]].
      exists (equiv_idmap I); cbn.
      exists (fun x:A => 1%path); cbn.
      exists (fun x:I => 1%path); cbn.
      intros; apply concat_1p. }
    intros [I [f1 [f2 [ff [oc1 oc2]]]]].
    contr_sigsig I (equiv_idmap I); cbn.
    contr_sigsig f1 (fun x:A => idpath (f1 x)); cbn.
    contr_sigsig f2 (fun x:I => idpath (f2 x)); cbn.
    refine (contr_equiv' {ff' : f2 o f1 == f & ff == ff'} _).
    symmetry; srefine (equiv_functor_sigma' (equiv_sigma_contr _) _).
    { intros h; cbn.
      srefine (@istrunc_sigma _ _ _ _ _); [ | intros a];
        apply contr_inhabited_hprop; try exact _; assumption. }
    intros [ff' [oc1' oc2']]; cbn.
    refine (equiv_functor_forall' (equiv_idmap _) _); intros a.
    refine (equiv_path_inverse _ _ oE _).
    apply equiv_concat_l; symmetry; apply concat_1p.
  Defined.

  Definition path_factorization `{Univalence} (fact fact' : Factorization)
    : PathFactorization fact fact' -> fact = fact'
    := equiv_path_factorization fact fact'.

End Factorization.

Arguments Factorization class1 class2 {A B} f.
Arguments PathFactorization {class1 class2 A B f} fact fact'.

(* This enables us to talk about "the image of a map" as a factorization but also as the intermediate object appearing in it, as is common in informal mathematics. *)
Coercion intermediate : Factorization >-> Sortclass.

(** ** Factorization Systems *)

(** A ("unique" or "orthogonal") factorization system consists of a couple of classes of maps, closed under composition, such that every map admits a unique factorization. *)
Record FactorizationSystem@{i j k} :=
  { class1 : forall {X Y : Type@{i}}, (X -> Y) -> Type@{j} ;
    ishprop_class1 : forall {X Y : Type@{i}} (g:X->Y), IsHProp (class1 g) ;
    class1_isequiv : forall {X Y : Type@{i}} (g:X->Y) {geq:IsEquiv g}, class1 g ;
    class1_compose : forall {X Y Z : Type@{i}} (g:X->Y) (h:Y->Z),
                       class1 g -> class1 h -> class1 (h o g) ;
    class2 : forall {X Y : Type@{i}}, (X -> Y) -> Type@{k} ;
    ishprop_class2 : forall {X Y : Type@{i}} (g:X->Y), IsHProp (class2 g) ;
    class2_isequiv : forall {X Y : Type@{i}} (g:X->Y) {geq:IsEquiv g}, class2 g ;
    class2_compose : forall {X Y Z : Type@{i}} (g:X->Y) (h:Y->Z),
                       class2 g -> class2 h -> class2 (h o g) ;
    (** Morally, the uniqueness of factorizations says that [Factorization class1 class2 f] is contractible.  However, in practice we always *prove* that by way of [path_factorization], and we frequently want to *use* the components of a [PathFactorization] as well.  Thus, as data we store the canonical factorization and a [PathFactorization] between any two such, and prove in a moment that this implies contractibility of the space of factorizations. *)
    factor : forall {X Y : Type@{i}} (f:X->Y), Factorization@{i} (@class1) (@class2) f ;
    path_factor : forall {X Y : Type@{i}} (f:X->Y)
                         (fact : Factorization@{i} (@class1) (@class2) f)
                         (fact' : Factorization@{i} (@class1) (@class2) f),
                    PathFactorization@{i} fact fact'
  }.

Global Existing Instances ishprop_class1 ishprop_class2.

(** The type of factorizations is, as promised, contractible. *)
Theorem contr_factor `{Univalence} (factsys : FactorizationSystem)
        {X Y : Type} (f : X -> Y)
  : Contr (Factorization (@class1 factsys) (@class2 factsys) f).
Proof.
  apply contr_inhabited_hprop.
  - apply hprop_allpath.
    intros fact fact'.
    apply path_factorization; try exact _.
    apply path_factor.
  - apply factor.
Defined.

Section FactSys.

  Context (factsys : FactorizationSystem).

  Definition Build_Factorization' {X Y}
    := @Build_Factorization (@class1 factsys) (@class2 factsys) X Y.

  Definition Build_PathFactorization' {X Y}
    := @Build_PathFactorization (@class1 factsys) (@class2 factsys) X Y.

  (** The left class is right-cancellable and the right class is left-cancellable. *)
  Definition cancelR_class1 `{Funext} {X Y Z} (f : X -> Y) (g : Y -> Z)
  : class1 factsys f -> class1 factsys (g o f) -> class1 factsys g.
  Proof.
    intros c1f c1gf.
    destruct (factor factsys g) as [I g1 g2 gf c1g1 c2g2].
    pose (fact  := Build_Factorization' (g o f) Z (g o f) (idmap)
                     (fun x => 1) c1gf (class2_isequiv factsys idmap)).
    pose (fact' := Build_Factorization' (g o f) I (g1 o f) g2
                     (fun x => gf (f x))
                     (class1_compose factsys f g1 c1f c1g1) c2g2).
    destruct (path_factor factsys (g o f) fact' fact)
             as [q q1 q2 qf]; simpl in *.
    refine (transport (class1 factsys) (path_arrow _ _ gf) _).
    refine (class1_compose factsys g1 g2 c1g1 _).
    apply class1_isequiv.
    apply (isequiv_homotopic _ (fun i => (q2 i)^)).
  Defined.

  Definition cancelL_class2 `{Funext} {X Y Z} (f : X -> Y) (g : Y -> Z)
  : class2 factsys g -> class2 factsys (g o f) -> class2 factsys f.
  Proof.
    intros c2g c2gf.
    destruct (factor factsys f) as [I f1 f2 ff c1f1 c2f2].
    pose (fact  := Build_Factorization' (g o f) X (idmap) (g o f)
                     (fun x => 1) (class1_isequiv factsys idmap) c2gf).
    pose (fact' := Build_Factorization' (g o f) I f1 (g o f2)
                     (fun x => ap g (ff x))
                     c1f1 (class2_compose factsys f2 g c2f2 c2g)).
    destruct (path_factor factsys (g o f) fact fact')
             as [q q1 q2 qf]; simpl in *.
    refine (transport (class2 factsys) (path_arrow _ _ ff) _).
    refine (class2_compose factsys f1 f2 _ c2f2).
    apply class2_isequiv.
    apply (isequiv_homotopic _ q1).
  Defined.

  (** The two classes of maps are automatically orthogonal, i.e. any commutative square from a [class1] map to a [class2] map has a unique diagonal filler.  For now, we only bother to define the lift; in principle we ought to show that the type of lifts is contractible. *)
  Universe ctxi.
  Context {A B X Y : Type@{ctxi}}
          (i : A -> B) (c1i : class1 factsys i)
          (p : X -> Y) (c2p : class2 factsys p)
          (f : A -> X) (g : B -> Y) (h : p o f == g o i).

  (** First we factor [f] *)
  Let C  : Type         := intermediate (factor factsys f).
  Let f1 : A -> C       := factor1      (factor factsys f).
  Let f2 : C -> X       := factor2      (factor factsys f).
  Let ff : f2 o f1 == f := fact_factors (factor factsys f).

  (** and [g] *)
  Let D  : Type         := intermediate (factor factsys g).
  Let g1 : B -> D       := factor1      (factor factsys g).
  Let g2 : D -> Y       := factor2      (factor factsys g).
  Let gf : g2 o g1 == g := fact_factors (factor factsys g).

  (** Now we observe that [p o f2] and [f1], and [g2] and [g1 o i], are both factorizations of the common diagonal of the commutative square (for which we use [p o f], but we could equally well use [g o i]. *)
  Let fact  : Factorization (@class1 factsys) (@class2 factsys) (p o f)
            := Build_Factorization' (p o f) C f1 (p o f2)
                 (fun a => ap p (ff a))
                 (inclass1 (factor factsys f))
                 (class2_compose factsys f2 p
                                 (inclass2 (factor factsys f))
                                 c2p).
  Let fact' : Factorization (@class1 factsys) (@class2 factsys) (p o f)
            := Build_Factorization' (p o f) D (g1 o i) g2
                 (fun a => gf (i a) @ (h a)^)
                 (class1_compose factsys i g1 c1i
                                 (inclass1 (factor factsys g)))
                 (inclass2 (factor factsys g)).

  (** Therefore, by the uniqueness of factorizations, we have an equivalence [q] relating them. *)
  Let q  : C <~> D          := path_intermediate
                                 (path_factor factsys (p o f) fact fact').
  Let q1 : q o f1 == g1 o i := path_factor1
                                 (path_factor factsys (p o f) fact fact').
  Let q2 : p o f2 == g2 o q := path_factor2
                                 (path_factor factsys (p o f) fact fact').

  (** Using this, we can define the lift. *)
  Definition lift_factsys : B -> X
    := f2 o q^-1 o g1.

  (** And the commutative triangles making it a lift *)
  Definition lift_factsys_tri1 : lift_factsys o i == f.
  Proof.
    intros x.
    refine (ap (f2 o q^-1) (q1 x)^ @ _).
    transitivity (f2 (f1 x)).
    + apply ap, eissect.
    + apply ff.
  Defined.

  Definition lift_factsys_tri2 : p o lift_factsys == g.
  Proof.
    intros x.
    refine (q2 _ @ _).
    transitivity (g2 (g1 x)).
    + apply ap, eisretr.
    + apply gf.
  Defined.

  (** And finally prove that these two triangles compose to the given commutative square. *)
  Definition lift_factsys_square (x : A)
  : ap p (lift_factsys_tri1 x)^ @ lift_factsys_tri2 (i x) = h x.
  Proof.
    unfold lift_factsys_tri1, lift_factsys_tri2.
    Open Scope long_path_scope.
    (* First we use the one aspect of the uniqueness of factorizations that we haven't mentioned yet. *)
    pose (r := path_fact_factors (path_factor factsys (p o f) fact fact') x
            : q2 (f1 x) @ ap g2 (q1 x) @ (gf (i x) @ (h x)^) = ap p (ff x)).
    rewrite concat_p_pp in r.
    apply moveL_pM, moveR_Vp in r.
    refine (_ @ r); clear r.
    (* Now we can cancel some whiskered paths on both sides. *)
    repeat rewrite inv_pp; repeat rewrite ap_pp; rewrite ap_V.
    repeat rewrite concat_pp_p; apply whiskerL.
    repeat rewrite concat_p_pp; apply whiskerR.
    (* Next we set up for a naturality. *)
    rewrite (ap_compose q^-1 f2), <- ap_pp, <- inv_pp.
    (* The next line appears to do nothing, but in fact it is necessary for the subsequent [rewrite] to succeed, because [lift_factsys] appears in the invisible implicit point-arguments of [paths].  One way to discover issues of that sort is to turn on printing of all implicit argumnets with [Set Printing All]; another is to use [Set Debug Tactic Unification] and inspect the output to see what [rewrite] is trying and failing to unify. *)
    unfold lift_factsys.
    rewrite <- ap_pp.
    rewrite <- ap_V, <- ap_compose.
    rewrite (concat_Ap q2).
    (* Now we can cancel another path *)
    rewrite concat_pp_p; apply whiskerL.
    (* And set up for an application of [ap]. *)
    rewrite ap_compose.
    rewrite <- ap_pp.
    apply ap.
    (* Now we apply the triangle identity [eisadj]. *)
    rewrite inv_pp, ap_pp, ap_V.
    rewrite <- eisadj.
    (* Finally, we rearrange and it becomes a naturality square. *)
    rewrite concat_pp_p; apply moveR_Vp.
    rewrite <- ap_V, inv_V, <- ap_compose.
    exact (concat_A1p (eisretr q) (q1 x)).
    Close Scope long_path_scope.
  Qed.

End FactSys.

Section FactsysExtensions.
  Context {factsys : FactorizationSystem}.

  (** We can deduce the lifting property in terms of extensions fairly easily from the version in terms of commutative squares. *)
  Definition extension_factsys {A B : Type}
             (f : A -> B) {c1f : class1 factsys f}
             (P : B -> Type) (c2P : class2 factsys (@pr1 B P))
             (d : forall a:A, P (f a))
  : ExtensionAlong f P d.
  Proof.
    pose (e := lift_factsys factsys f c1f pr1 c2P
                            (fun a => (f a ; d a)) idmap
                            (fun a => 1)).
    pose (e2 := lift_factsys_tri2 factsys f c1f pr1 c2P
                            (fun a => (f a ; d a)) idmap
                            (fun a => 1)).
    exists (fun a => (e2 a) # (e a).2).
    intros a.
    pose (e1 := lift_factsys_tri1 factsys f c1f pr1 c2P
                            (fun a => (f a ; d a)) idmap
                            (fun a => 1) a
                : e (f a) = (f a ; d a)).
    pose (e3 := moveL_M1 _ _ (((ap_V _ _)^ @@ 1)
                @ lift_factsys_square factsys f c1f pr1 c2P
                            (fun a => (f a ; d a)) idmap
                            (fun a => 1) a)
                : e2 (f a) = pr1_path e1).
    refine (ap (fun p => transport P p (e (f a)).2) e3 @ _).
    exact (pr2_path e1).
  Defined.

End FactsysExtensions.
