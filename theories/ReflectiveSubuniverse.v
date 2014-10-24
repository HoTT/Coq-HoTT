(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import UnivalenceImpliesFunext EquivalenceVarieties.
Require Import HoTT.Tactics.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

Local Arguments compose / .

(** * Reflective Subuniverses *)

(** ** Unit Subuniverses *)

(** A UnitSubuniverse is the common underlying structure of a reflective subuniverse and a modality.  We make it a separate structure in order to use the same names for its fields and functions in the two cases. *)
Record UnitSubuniverse :=
  {
    inO_internal : Type -> Type ;
    O_reflector : Type -> Type ;
    O_inO_internal : forall T, inO_internal (O_reflector T) ;
    to : forall T, T -> O_reflector T ;
    inO_equiv_inO_internal :
      forall T U (T_inO : inO_internal T) (f : T -> U) (feq : IsEquiv f),
        inO_internal U ;
    (** In most examples, [Funext] is necessary to prove that the predicate of being in the subuniverse is an hprop.  To avoid needing to assume [Funext] as a global hypothesis when constructing such examples, and since [Funext] is often not needed for any of the rest of the theory, we add it as a hypothesis to this specific field of the record. *)
    hprop_inO_internal : Funext -> forall T, IsHProp (inO_internal T)
  }.

(** For reflective subuniverses (and hence also modalities), it will turn out that [inO T] is equivalent to [IsEquiv (O_unit T)].  We could define the former as the latter, and it would simplify some of the general theory.  However, in many examples there is a "more basic" definition of [inO] which is equivalent, but not definitionally identical, to [IsEquiv (O_unit T)].  Thus, including [inO] as data makes more things turn out to be judgmentally what we would expect. *)

(** We choose to allow the name of a subuniverse or modality to be used as the name of its reflector. *)
Coercion O_reflector : UnitSubuniverse >-> Funclass.

(* This makes anomalies, see https://coq.inria.fr/bugs/show_bug.cgi?id=3753 *)
(* Arguments to O T x : rename. *)

(** We now give new names or identities to all the "internal" fields. *)

(** The property of being in the subuniverse, as a typeclass *)
Class In (O : UnitSubuniverse) (T : Type) :=
  in_inO_internal : inO_internal O T.

Typeclasses Transparent In.
Typeclasses Transparent inO_internal.
Typeclasses Transparent O_reflector.

(** We assumed repleteness of the subuniverse in the definition.  Of course, with univalence this would be automatic, but we include it as a hypothesis since this is the only appearance of univalence in the theory of reflective subuniverses and non-lex modalities, and most or all examples can be shown to be replete without using univalence. *)
Definition inO_equiv_inO {O : UnitSubuniverse}
           T {U} {T_inO : In O T} (f : T -> U) {feq : IsEquiv f}
: In O U
:= inO_equiv_inO_internal O T U T_inO f feq.

(** Being in the subuniverse is a mere predicate (by hypothesis) *)
Global Instance hprop_inO {fs : Funext} {O : UnitSubuniverse} (T : Type)
  : IsHProp (In O T)
  := hprop_inO_internal O fs T.

(** [O T] is always in the subuniverse (by hypothesis) *)
Global Instance O_inO {O : UnitSubuniverse} (T : Type) : In O (O T)
  := O_inO_internal O T.

(** The type of types in the subuniverse *)
Definition Type_ (O : UnitSubuniverse) : Type
  := {T : Type & In O T}.

Coercion TypeO_pr1 O (T : Type_ O) := @pr1 Type (In O) T.

(** The second component of [TypeO] is unique *)
Definition path_TypeO {fs : Funext} O (T T' : Type_ O) (p : T.1 = T'.1)
  : T = T'
  := path_sigma_hprop T T' p.

(** ** Reflective Subuniverses *)

(** A reflective subuniverse is a [UnitSubuniverse], as above, whose unit has a universal property.  We express that universal property using the representation [oo_Pointwise_PathSplit_Precompose] of precomposition equivalences, since unlike most other ways to describe such an equivalence, it doesn't need [Funext] to prove or to use. *)
Record ReflectiveSubuniverse :=
  {
    rsubu : UnitSubuniverse ;
    ppp_to_O : forall {P Q : Type} {Q_inO : In rsubu Q},
                 oo_Pointwise_PathSplit_Precompose
                   (fun _ => Q) (to rsubu P)
  }.

Coercion rsubu : ReflectiveSubuniverse >-> UnitSubuniverse.

(** We now extract the recursion principle and the restricted induction principles for paths. *)
Section ORecursion.
  Context {O : ReflectiveSubuniverse}.

  Definition O_rec {P Q : Type} {Q_inO : In O Q}
             (f : P -> Q)
  : O P -> Q
  := (fst (ppp_to_O O 1%nat)).1 f.

  Definition O_rec_beta {P Q : Type} {Q_inO : In O Q}
             (f : P -> Q) (x : P)
  : O_rec f (to O P x) = f x
  := (fst (ppp_to_O O 1%nat)).2 f x.

  Definition O_indpaths {P Q : Type} {Q_inO : In O Q}
             (g h : O P -> Q) (p : g o to O P == h o to O P)
  : g == h
  := (fst (snd (ppp_to_O O 2) g h)).1 p.

  Definition O_indpaths_beta {P Q : Type} {Q_inO : In O Q}
             (g h : O P -> Q) (p : g o (to O P) == h o (to O P)) (x : P)
  : O_indpaths g h p (to O P x) = p x
  := (fst (snd (ppp_to_O O 2) g h)).2 p x.

  Definition O_ind2paths {P Q : Type} {Q_inO : In O Q}
             {g h : O P -> Q} (p q : g == h)
             (r : p oD (to O P) == q oD (to O P))
  : p == q
  := (fst (snd (snd (ppp_to_O O 3) g h) p q)).1 r.

  Definition O_ind2paths_beta {P Q : Type} {Q_inO : In O Q}
             {g h : O P -> Q} (p q : g == h)
             (r : p oD (to O P) == q oD (to O P)) (x : P)
  : O_ind2paths p q r (to O P x) = r x
  := (fst (snd (snd (ppp_to_O O 3) g h) p q)).2 r x.

  (** Clearly we can continue indefinitely as needed. *)

End ORecursion.

(* We never want to see [ppp_to_O]. *)
Arguments O_rec : simpl never.
Arguments O_rec_beta : simpl never.
Arguments O_indpaths : simpl never.
Arguments O_indpaths_beta : simpl never.
Arguments O_ind2paths : simpl never.
Arguments O_ind2paths_beta : simpl never.

(** Given [Funext], we prove the definition of reflective subuniverse in the book. *)
Global Instance isequiv_o_to_O `{Funext}
       (O : ReflectiveSubuniverse) (P Q : Type) `{In O Q}
: IsEquiv (fun g : O P -> Q => g o to O P)
:= isequiv_oo_pointwise_pathsplit _ _ (ppp_to_O O).

Definition equiv_o_to_O `{Funext}
           (O : ReflectiveSubuniverse) (P Q : Type) `{In O Q}
: (O P -> Q) <~> (P -> Q)
:= BuildEquiv _ _ (fun g : O P -> Q => g o to O P) _.

  (* Global Instance isequiv_O_rec *)
  (* : IsEquiv (@O_rec O P Q _) *)
  (* := (@isequiv_inverse _ _ _ isequiv_o_to_O). *)

  (* Definition equiv_O_rec : (P -> Q) <~> (O P -> Q) *)
  (*   := BuildEquiv _ _ O_rec _. *)

(** Conversely, from the book's definition we can reconstruct ours. *)
Definition reflective_subuniverse_from_isequiv
           `{Funext} (O : UnitSubuniverse)
           (H : forall (P Q : Type) {Q_inO : In O Q},
                  IsEquiv (fun g : O P -> Q => g o to O P))
: ReflectiveSubuniverse
  := Build_ReflectiveSubuniverse O
      (fun P Q Q_inO =>
         (equiv_oo_pointwise_pathsplit_isequiv
            (fun _ => Q) (to O P))^-1 (H P Q)).

(** So why do we use a different definition than the book?  Notice that *both* directions of the comparison between our definition and the book's make use of funext.  Moreover, it seems that in order to do anything useful with the book's definition, or construct any interesting examples, also requires funext.  However, this is not the case for our definition!  Thus, our choice has the following advantages:

1. It avoids the funext redexes that otherwise infect the theory, thereby simplifying the proofs and proof terms.  We never have to worry about whether we have a path between functions or a homotopy; we use only homotopies, with no need for [ap10] or [path_arrow] to mediate.

2. It avoids [Funext] hypotheses in some constructions of reflective subuniverses, particularly the construction from a [Modality].  This enables us to declare such constructions as coercions without running afoul of Coq's "uniform inheritance condition", so that a modality can be used as a reflective subuniverse.

3. In fact, the data of a reflective subuniverse according to our definition are precisely a couple of special cases of the data of a modality.  Thus, all the theorems we prove about reflective subuniverses will, when interpreted for a modality (coerced as above to a reflective subuniverse), reduce definitionally to "the way we would have proved them directly for a modality".  *)

(** ** Properties of Reflective Subuniverses *)

(** We now prove a bunch of things about an arbitrary reflective subuniverse. *)
Section Reflective_Subuniverse.
  Context (O : ReflectiveSubuniverse).

  (** Functoriality of [O_rec] homotopies *)
  Definition O_rec_homotopy {P Q} `{In O Q} (f g : P -> Q) (pi : f == g)
  : O_rec f == O_rec g.
  Proof.
    apply O_indpaths; intro x.
    etransitivity.
    { apply O_rec_beta. }
    { etransitivity.
      { exact (pi _). }
      { symmetry; apply O_rec_beta. } }
  Defined.

  (** If [T] is in the subuniverse, then [to O T] is an equivalence. *)
  Global Instance isequiv_to_O_inO (T : Type) `{In O T} : IsEquiv (to O T).
  Proof.
    pose (g := O_rec idmap).
    refine (isequiv_adjointify (to O T) g _ _).
    - refine (O_indpaths (to O T o g) idmap _).
      intros x; unfold compose.
      apply ap.
      apply O_rec_beta.
    - intros x.
      apply O_rec_beta.
  Defined.

  Definition equiv_to_O (T : Type) `{In O T} : T <~> O T
    := BuildEquiv T (O T) (to O T) _.

  Section Functor.

    (** In this section, we see that [O] is a functor. *)
    
    Definition O_functor {A B : Type} (f : A -> B) : O A -> O B
      := O_rec (to O B o f).

    (** Functoriality on composition *)
    Definition O_functor_compose {A B C : Type} (f : A -> B) (g : B -> C)
    : (O_functor (g o f)) == (O_functor g) o (O_functor f).
    Proof.
      apply O_indpaths; intros x; unfold compose.
      refine (O_rec_beta (to O C o g o f) x @ _).
      transitivity (O_functor g (to O B (f x))).
      - symmetry. exact (O_rec_beta (to O C o g) (f x)).
      - apply ap; symmetry.
        exact (O_rec_beta (to O B o f) x).
    Defined.

    (** Functoriality on homotopies (2-functoriality) *)
    Definition O_functor_homotopy {A B : Type} (f g : A -> B) (pi : f == g)
    : O_functor f == O_functor g.
    Proof.
      refine (O_indpaths _ _ _); intros x.
      refine (O_rec_beta (to O B o f) x @ _).
      refine (_ @ (O_rec_beta (to O B o g) x)^).
      unfold compose; apply ap.
      apply pi.
    Defined.

    (** Hence functoriality on commutative squares *)
    Definition O_functor_square {A B C X : Type} (pi1 : X -> A) (pi2 : X -> B)
               (f : A -> C) (g : B -> C) (comm : (f o pi1) == (g o pi2))
    : ( (O_functor f) o (O_functor pi1) )
      == ( (O_functor g) o (O_functor pi2) ).
    Proof.
      intros x.
      transitivity (O_functor (f o pi1) x).
      - symmetry; apply O_functor_compose.
      - transitivity (O_functor (g o pi2) x).
        * apply O_functor_homotopy, comm.
        * apply O_functor_compose.
    Defined.

    (** Functoriality on identities *)
    Definition O_functor_idmap (A : Type)
    : @O_functor A A idmap == idmap.
    Proof.
      refine (O_indpaths _ _ _); intros x.
      apply O_rec_beta.
    Qed.

    (** 3-functoriality, as an example use of [O_ind2paths] *)
    Definition O_functor_2homotopy {A B : Type} {f g : A -> B}
               (p q : f == g) (r : p == q)
    : O_functor_homotopy f g p == O_functor_homotopy f g q.
    Proof.
      refine (O_ind2paths _ _ _); intros x.
      unfold O_functor_homotopy, composeD.
      do 2 rewrite O_indpaths_beta.
      apply whiskerL, whiskerR, ap, r.
    (* Of course, if we wanted to prove 4-functoriality, we'd need to make this transparent. *)
    Qed.

    (** Naturality of [to O] *)
    Definition to_O_natural {A B} (f : A -> B)
    : (O_functor f) o (to O A) == (to O B) o f
    := (O_rec_beta _).

    (** The pointed endofunctor ([O],[to O]) is well-pointed *)
    Definition O_functor_wellpointed (A : Type)
    : O_functor (to O A) == to O (O A).
    Proof.
      refine (O_indpaths _ _ _); intros x.
      apply to_O_natural.
    Defined.

    (** Preservation of equivalences *)
    Global Instance isequiv_O_functor {A B} (f : A -> B) `{IsEquiv _ _ f}
    : IsEquiv (O_functor f).
    Proof.
      refine (isequiv_adjointify (O_functor f) (O_functor f^-1) _ _).
      - intros x.
        refine ((O_functor_compose _ _ x)^ @ _).
        refine (O_functor_homotopy _ idmap _ x @ _).
        + intros y; apply eisretr.
        + apply O_functor_idmap.
      - intros x.
        refine ((O_functor_compose _ _ x)^ @ _).
        refine (O_functor_homotopy _ idmap _ x @ _).
        + intros y; apply eissect.
        + apply O_functor_idmap.
    Defined.
      
    Definition equiv_O_functor {A B} (f : A <~> B)
    : O A <~> O B
    := BuildEquiv _ _ (O_functor f) _.

    (** Postcomposition respects [O_rec] *)
    Definition O_rec_postcompose {A B C} `{In O B} {C_inO : In O C}
               (f : A -> B) (g : B -> C)
    : g o O_rec f == O_rec (g o f).
    Proof.
      refine (O_indpaths _ _ _); intros x; unfold compose.
      transitivity (g (f x)).
      - apply ap. apply O_rec_beta.
      - symmetry. exact (O_rec_beta (g o f) x).
    Defined.

  End Functor.

  Section Replete.

    (** An equivalent formulation of repleteness is that a type lies in the subuniverse as soon as its unit map is an equivalence. *)
    Definition inO_isequiv_to_O (T:Type)
    : IsEquiv (to O T) -> In O T
    := fun _ => inO_equiv_inO (O T) (to O T)^-1.

    (* We don't make this an ordinary instance, but we allow it to solve [In O] constraints if we already have [IsEquiv] as a hypothesis.  *)
    Hint Immediate inO_isequiv_to_O : typeclass_instances.

    Definition inO_iff_isequiv_to_O (T:Type)
    : In O T <-> IsEquiv (to O T).
    Proof.
      split; exact _.
    Defined.

    (** Thus, [T] is in a subuniverse as soon as [to O T] admits a retraction. *)
    Definition inO_to_O_retract (T:Type) (mu : O T -> T)
    : Sect (to O T) mu -> In O T.
    Proof.
      unfold Sect; intros H.
      apply inO_isequiv_to_O.
      apply isequiv_adjointify with (g:=mu).
      - refine (O_indpaths (to O T o mu) idmap _).
        intros x; exact (ap (to O T) (H x)).
      - exact H.
    Defined.

  End Replete.

  Section OInverts.

    (** The maps that are inverted by the reflector.  Note that this notation is NOT GLOBAL, it only exists in this section. *)
    Local Notation O_inverts f := (IsEquiv (O_functor f)).

    Global Instance O_inverts_O_unit (A : Type)
    : O_inverts (to O A).
    Proof.
      refine (isequiv_homotopic (to O (O A)) _).
      intros x; symmetry; apply O_functor_wellpointed.
    Defined.

    (** A map between modal types that is inverted by [O] is already an equivalence. *)
    Definition isequiv_O_inverts {A B} `{In O A} `{In O B}
      (f : A -> B) `{O_inverts f}
    : IsEquiv f.
    Proof.
      refine (isequiv_commsq' f (O_functor f) (to O A) (to O B) _).
      apply to_O_natural.
    Defined.

    Definition equiv_O_inverts {A B} `{In O A} `{In O B}
      (f : A -> B) `{O_inverts f}
    : A <~> B
    := BuildEquiv _ _ f (isequiv_O_inverts f).

    Definition to_O_inv_natural {A B} `{In O A} `{In O B}
               (f : A -> B)
    : (to O B)^-1 o (O_functor f) == f o (to O A)^-1.
    Proof.
      refine (O_indpaths _ _ _); intros x.
      unfold compose; apply moveR_equiv_V.
      refine (to_O_natural f x @ _).
      unfold compose; do 2 apply ap.
      symmetry; apply eissect.
    Defined.

    (** Two maps between modal types that become equal after applying [O_functor] are already equal. *)
    Definition O_functor_faithful_inO {A B} `{In O A} `{In O B}
      (f g : A -> B) (e : O_functor f == O_functor g)
      : f == g.
    Proof.
      intros x.
      refine (ap f (eissect (to O A) x)^ @ _).
      refine (_ @ ap g (eissect (to O A) x)).
      transitivity ((to O B)^-1 (O_functor f (to O A x))).
      + symmetry; apply to_O_inv_natural.
      + transitivity ((to O B)^-1 (O_functor g (to O A x))).
        * apply ap, e.
        * apply to_O_inv_natural.
    Defined.

    (** Any map to a type in the subuniverse that is inverted by [O] must be equivalent to [to O].  More precisely, the type of such maps is contractible. *)
    Definition typeof_to_O (A : Type)
      := { OA : Type & { Ou : A -> OA & ((In O OA) * (O_inverts Ou)) }}.

    Global Instance contr_typeof_O_unit `{Univalence} (A : Type)
    : Contr (typeof_to_O A).
    Proof.
      exists (O A ; (to O A ; (_ , _))).
      intros [OA [Ou [? ?]]].
      pose (f := O_rec Ou : O A -> OA).
      pose (g := (O_functor Ou)^-1 o to O OA : (OA -> O A)).
      assert (IsEquiv f).
      { refine (isequiv_adjointify f g _ _).
        - apply O_functor_faithful_inO; intros x.
          rewrite O_functor_idmap.
          fold (f o g); rewrite O_functor_compose.
          unfold g.
          simpl rewrite (O_functor_compose (to O OA) (O_functor Ou)^-1).
          rewrite O_functor_wellpointed.
          simpl rewrite (to_O_natural (O_functor Ou)^-1 x).
          refine (to_O_natural f _ @ _).
          set (y := (O_functor Ou)^-1 x).
          transitivity (O_functor Ou y); try apply eisretr.
          unfold f, O_functor, compose.
          apply O_rec_postcompose.
        - refine (O_indpaths _ _ _); intros x.
          unfold f, compose.
          rewrite O_rec_beta. unfold g.
          apply moveR_equiv_V.
          symmetry; apply to_O_natural.
      }
      refine (path_sigma _ _ _ _ _); cbn.
      - exact (path_universe f).
      - rewrite transport_sigma.
        refine (path_sigma _ _ _ _ _); cbn; try apply path_ishprop.
        apply path_arrow; intros x.
        rewrite transport_arrow_fromconst.
        rewrite transport_path_universe.
        unfold f; apply O_rec_beta.
    Qed.

  End OInverts.

  Section Types.

    (** ** The [Unit] type *)
    Global Instance inO_unit : In O Unit.
    Proof.
      apply inO_to_O_retract with (mu := fun x => tt).
      exact (@contr Unit _).
    Defined.

    (** It follows that any contractible type is in [O]. *)
    Global Instance inO_contr {A} `{Contr A} : In O A.
    Proof.
      exact (inO_equiv_inO Unit (equiv_inverse equiv_contr_unit)).
    Defined.

    (** And that the reflection of a contractible type is still contractible. *)
    Global Instance contr_O_contr {A} `{Contr A} : Contr (O A).
    Proof.
      exact (contr_equiv A (to O A)).
    Defined.

    (** ** Dependent product and arrows *)
    (** Theorem 7.7.2 *)
    Global Instance inO_forall {fs : Funext} (A:Type) (B:A -> Type) 
    : (forall x, (In O (B x)))
      -> (In O (forall x:A, (B x))).
    Proof.
      intro H.
      pose (ev := fun x => (fun (f:(forall x, (B x))) => f x)).
      pose (zz := fun x:A => O_rec (ev x)).
      apply inO_to_O_retract with (mu := fun z => fun x => zz x z).
      intro phi.
      unfold zz, ev; clear zz; clear ev.
      apply path_forall; intro x.
      exact (O_rec_beta (fun f : forall x0, (B x0) => f x) phi).
    Defined.

    Global Instance inO_arrow {fs : Funext} (A B : Type) `{In O B}
    : In O (A -> B).
    Proof.
      apply inO_forall.
      intro a. exact _.
    Defined.

    (** ** Product *)
    Global Instance inO_prod (A B : Type) `{In O A} `{In O B}
    : In O (A*B).
    Proof.
      apply inO_to_O_retract with
        (mu := fun X => (@O_rec _ (A * B) A _ fst X , O_rec snd X)).
      intros [a b]; apply path_prod; simpl.
      - exact (O_rec_beta fst (a,b)). 
      - exact (O_rec_beta snd (a,b)).
    Defined.

    (** We show that [OA*OB] has the same universal property as [O(A*B)] *)

    Definition equiv_O_prod_unit_precompose
               {fs : Funext} (A B C : Type) `{In O C}
    : ((O A) * (O B) -> C) <~> (A * B -> C).
    Proof.
      apply (equiv_compose' (equiv_uncurry A B C)).
      refine (equiv_compose' _ (equiv_inverse (equiv_uncurry (O A) (O B) C))).
      apply (equiv_compose' (equiv_o_to_O _ A (B -> C))); simpl.
      apply equiv_postcompose'.
      exact (equiv_o_to_O _ B C).
    Defined.

    (** The preceding equivalence turns out to be actually (judgmentally!) precomposition with the following function. *)
    Definition O_prod_unit (A B : Type) : A * B -> O A * O B
      := functor_prod (to O A) (to O B).

    (** From this, we can define the comparison map for products, and show that precomposing with it is also an equivalence. *)
    Definition O_prod_cmp (A B : Type) : O (A * B) -> O A * O B
      := O_rec (O_prod_unit A B).

    Global Instance isequiv_O_prod_cmp (A B : Type)
    : IsEquiv (O_prod_cmp A B).
    Proof.
      refine (isequiv_adjointify _ _ _ _).
      { apply prod_ind; intro a.
        apply O_rec; intro b; revert a.
        apply O_rec; intro a.
        apply (to O).
        exact (a, b). }
      { unfold prod_ind, O_prod_cmp, O_prod_unit.
        intros [oa ob].
        revert ob; refine (O_indpaths _ _ _); intros b.
        revert oa; refine (O_indpaths _ _ _); intros a.
        cbn. abstract (repeat rewrite O_rec_beta; reflexivity). }
      { unfold prod_ind, O_prod_cmp, O_prod_unit.
        refine (O_indpaths _ _ _); intros [a b]; cbn.
        abstract (repeat (rewrite O_rec_beta; cbn); reflexivity). }
    Defined.

    Definition isequiv_O_prod_cmp_precompose
      {fs : Funext} (A B C : Type) {C_inO : In O C}
    : IsEquiv (fun h : O A * O B -> C => h o O_prod_cmp A B).
    Proof.
      apply isequiv_precompose; exact _.
    Defined.

    Definition equiv_O_prod_cmp {fs : Funext} (A B : Type)
    : O (A * B) <~> (O A * O B)
    := BuildEquiv _ _ (O_prod_cmp A B) _.

    (** ** Dependent sums *)
    (** Theorem 7.7.4 *)
    Definition inO_sigma_iff
    : (forall (A:Type) (B:A -> Type) `{In O A} `{forall a, In O (B a)},
         (In O ({x:A & B x})))
      <->
      (forall (A:Type) (B: (O A) -> Type) `{forall a, In O (B a)}
              (g : forall (a:A), (B (to O A a))),
         {f : forall (z:O A), (B z) & forall a:A, f (to O A a) = g a}).
    Proof.
      split.
      - intro H. intros A B ? g.
        pose (Z := sigT B).
        assert (In O Z). apply H; exact _.
        pose (g' := (fun a:A => (to O A a ; g a)) : A -> Z).
        pose (f' := O_rec g').
        pose (eqf := (O_rec_beta g')  : f' o to O A == g').
        pose (eqid := O_indpaths (pr1 o f') idmap
                                  (fun x => ap pr1 (eqf x))).
        exists (fun z => transport B (eqid z) ((f' z).2)); intros a.
        unfold eqid. rewrite O_indpaths_beta.
        exact (pr2_path (O_rec_beta g' a)).
      - intros H A B ? ?.
        pose (h := fun x => @O_rec _ ({x:A & B x}) A _ pr1 x).
        pose (p := (fun z => O_rec_beta pr1 z)
                   : h o (to O _) == pr1).
        pose (g := fun z => (transport B ((p z)^) z.2)).
        simpl in *.
        specialize (H ({x:A & B x}) (B o h) _ g).
        destruct H as [f q].
        apply inO_to_O_retract with (mu := fun w => (h w; f w)).
        intros [x1 x2].
        refine (path_sigma B _ _ _ _); simpl.
        * apply p.
        * rewrite (q (x1;x2)).
          unfold g; simpl. exact (transport_pV B _ _).
    Qed.

    (** ** Paths *)

    Global Instance inO_paths (S : Type) {S_inO : In O S} (x y : S)
    : In O (x=y).
    Proof.
      refine (inO_to_O_retract _ _ _); intro u.
      - assert (p : (fun _ : O (x=y) => x) == (fun _=> y)). 
        { refine (O_indpaths _ _ _); unfold compose; simpl.
          intro v; exact v. }
        exact (p u).
      - hnf.
        rewrite O_indpaths_beta; reflexivity.
    Qed.
    
  End Types.

  Section Monad.

    Definition O_monad_mult A : O (O A) -> O A
      := O_rec idmap.

    Definition O_monad_mult_natural {A B} (f : A -> B)
    : O_functor f o O_monad_mult A == O_monad_mult B o O_functor (O_functor f).
    Proof.
      apply O_indpaths; intros x; unfold compose, O_monad_mult.
      simpl rewrite (to_O_natural (O_functor f) x).
      rewrite (O_rec_beta idmap x).
      rewrite (O_rec_beta idmap (O_functor f x)).
      reflexivity.
    Qed.

    Definition O_monad_unitlaw1 A
    : O_monad_mult A o (to O (O A)) == idmap.
    Proof.
      apply O_indpaths; intros x; unfold compose, O_monad_mult.
      exact (O_rec_beta idmap (to O A x)).
    Defined.

    Definition O_monad_unitlaw2 A
    : O_monad_mult A o (O_functor (to O A)) == idmap.
    Proof.
      apply O_indpaths; intros x; unfold O_monad_mult, O_functor, compose.
      repeat rewrite O_rec_beta.
      reflexivity.
    Qed.

    Definition O_monad_mult_assoc A
    : O_monad_mult A o O_monad_mult (O A) == O_monad_mult A o O_functor (O_monad_mult A).
    Proof.
      apply O_indpaths; intros x; unfold O_monad_mult, O_functor, compose.
      repeat rewrite O_rec_beta.
      reflexivity.
    Qed.

  End Monad.

  Section StrongMonad.
    Context {fs : Funext}.

    Definition O_monad_strength A B : A * O B -> O (A * B)
      := fun aob => O_rec (fun b a => to O (A*B) (a,b)) (snd aob) (fst aob).

    Definition O_monad_strength_natural A A' B B' (f : A -> A') (g : B -> B')
    : O_functor (functor_prod f g) o O_monad_strength A B ==
      O_monad_strength A' B' o functor_prod f (O_functor g).
    Proof.
      intros [a ob]. revert a. apply ap10.
      revert ob; apply O_indpaths.
      intros b; simpl.
      apply path_arrow; intros a.
      unfold O_monad_strength, O_functor, compose; simpl.
      repeat rewrite O_rec_beta.
      reflexivity.
    Qed.
      
    (** The diagrams for strength, see http://en.wikipedia.org/wiki/Strong_monad *)
    Definition O_monad_strength_unitlaw1 A
    : O_functor (@snd Unit A) o O_monad_strength Unit A == @snd Unit (O A).
    Proof.
      intros [[] oa]; revert oa.
      apply O_indpaths; intros x; unfold O_monad_strength, O_functor, compose. simpl. 
      repeat rewrite O_rec_beta.
      reflexivity.
    Qed.

    Definition O_monad_strength_unitlaw2 A B
    : O_monad_strength A B o functor_prod idmap (to O B) == to O (A*B).
    Proof.
      intros [a b].
      unfold O_monad_strength, functor_prod, compose. simpl. 
      repeat rewrite O_rec_beta.
      reflexivity.
    Qed.

    Definition O_monad_strength_assoc1 A B C
    : O_functor (equiv_prod_assoc A B C)^-1 o O_monad_strength (A*B) C ==
      O_monad_strength A (B*C) o functor_prod idmap (O_monad_strength B C) o (equiv_prod_assoc A B (O C))^-1.
    Proof.
      intros [[a b] oc].
      revert a; apply ap10. revert b; apply ap10.
      revert oc; apply O_indpaths.
      intros c; simpl.
      apply path_arrow; intros b. apply path_arrow; intros a.
      unfold O_monad_strength, O_functor, functor_prod, compose. simpl. 
      repeat rewrite O_rec_beta.
      reflexivity.
    Qed.

    Definition O_monad_strength_assoc2 A B
    : O_monad_mult (A*B) o O_functor (O_monad_strength A B) o O_monad_strength A (O B) ==
      O_monad_strength A B o functor_prod idmap (O_monad_mult B).
    Proof.
      intros [a oob]. revert a; apply ap10.
      revert oob; apply O_indpaths. apply O_indpaths.
      intros b; simpl. apply path_arrow; intros a.
      unfold O_monad_strength, O_functor, O_monad_mult, functor_prod, compose. simpl. 
      repeat (rewrite O_rec_beta; simpl).
      reflexivity.
    Qed.
      
  End StrongMonad.
      
End Reflective_Subuniverse.
