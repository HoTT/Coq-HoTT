(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics.
Require Import types.Empty types.Unit types.Arrow types.Sigma types.Paths types.Forall types.Prod types.Universe.
Require Import UnivalenceImpliesFunext.
Require Import HoTT.Tactics.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

Local Arguments compose / .

(** * Reflective Subuniverses *)

(** ** Unit Subuniverses *)

(** A UnitSubuniverse is the common underlying structure of a reflective subuniverse and a modality.  We make it a separate structure in order to use the same names for its fields and functions in the two cases. *)
Class UnitSubuniverse :=
  {
    inO_internal : Type -> Type ;
    O : Type -> Type ;
    O_inO_internal : forall T, inO_internal (O T) ;
    O_unit : forall T, T -> O T ;
    (** In most examples, [Funext] is necessary to prove that the predicate of being in the subuniverse is an hprop.  To avoid needing to assume [Funext] as a global hypothesis when constructing such examples, and since [Funext] is often not needed for any of the rest of the theory, we add it as a hypothesis to this specific field of the record. *)
    hprop_inO_internal : Funext -> forall T, IsHProp (inO_internal T)
  }.

(** For reflective subuniverses (and hence also modalities), it will turn out that [inO T] is equivalent to [IsEquiv (O_unit T)].  We could define the former as the latter, and it would simplify some of the general theory.  However, in many examples there is a "more basic" definition of [inO] which is equivalent, but not definitionally identical, to [IsEquiv (O_unit T)].  Thus, including [inO] as data makes more things turn out to be judgmentally what we would expect. *)

(** We made [UnitSubuniverse] into a typeclass, rather than just a record, so that when there is an assumed one around it doesn't need to be given explicitly as an argument to everything.  You should *not* ever declare a global [Instance] of [UnitSubuniverse].  The things to do with it are:

  1. Assume an arbitrary one for the purposes of general theory, as we will do here.  In this case it is a variable in the context, so typeclass resolution finds it automatically.

  2. Construct a specific one, such as n-types.  You should not define it as a global instance: use [Definition] or [Local Instance].  That way someone else can import your file and still be able to talk about subuniverses other than yours.  (If they do want to use yours, then they can declare it with [Local Existing Instance].)

  3. Apply general theory to a specific example explicitly.  This requires giving the specific example, defined as above, as an explicit argument to the general functions and theorems.

  4. Specify locally that we will be applying the general theory of subuniverses only to a specific example, by declaring that example as a [Local Instance].  (If the subuniverse in question has already been defined somewhere else, you can declare it as an instance locally with [Local Existing Instance].)  This way the instance won't outlast the containing section, module, or file, but inside that section, module, or file, you won't have to give it as an explicit argument.

  The same considerations will apply to [ReflectiveSubuniverse] and [Modality].
 *)

Section Unit_Subuniverse.

  Context {subU : UnitSubuniverse}.

  (** The property of being in the subuniverse.  This is a more usual sort of typeclass, to be inferred automatically in many cases.  Note, however, that you shouldn't write [`{inO A}], since the generalizing binders will then introduce a *new* [UnitSubuniverse] hypothesis rather than using the one you intend; write [{A_inO : inO A}] instead.  *)
  Class inO (T : Type) :=
    isequiv_inO : inO_internal T.

  Typeclasses Transparent inO.

  (** Being in the subuniverse is a mere predicate (by hypothesis) *)
  Global Instance hprop_inO {fs : Funext} (T : Type)
  : IsHProp (inO T)
  := hprop_inO_internal fs T.

  (** [O T] is always in the subuniverse (by hypothesis) *)
  Global Instance O_inO T : inO (O T)
    := O_inO_internal T.

  (** The type of types in the subuniverse *)
  Definition TypeO : Type
    := {T : Type & inO T}.

  Coercion TypeO_pr1 (T : TypeO) := @pr1 Type inO T.

  (** The second component of [TypeO] is unique *)
  Definition path_TypeO {fs : Funext} (T T' : TypeO) (p : T.1 = T'.1)
  : T = T'
  := path_sigma_hprop T T' p.

End Unit_Subuniverse.

(** ** Reflective Subuniverses *)

(** A reflective subuniverse is a [UnitSubuniverse], as above, whose unit has a universal property.  Our definition is somewhat different from that in the book, being instead more similar to the definition of a [Modality]; below we show that it is in fact equivalent. *)
Class ReflectiveSubuniverse :=
  {
    rsubu_usubu : UnitSubuniverse ;
    O_rectnd : forall {P Q : Type} {Q_inO : inO Q} (f : P -> Q), O P -> Q ;
    O_rectnd_beta : forall {P Q : Type} {Q_inO : inO Q} (f : P -> Q) (x : P),
                      O_rectnd f (O_unit P x) = f x ;
    O_rectpaths : forall {P Q : Type} {Q_inO : inO Q}
                         (g h : O P -> Q) (p : g o O_unit P == h o O_unit P),
                    g == h ;
    O_rectpaths_beta : forall {P Q : Type} {Q_inO : inO Q}
                         (g h : O P -> Q) (p : g o O_unit P == h o O_unit P)
                         (x : P),
                         O_rectpaths g h p (O_unit P x) = p x
  }.

Global Existing Instance rsubu_usubu.
Coercion rsubu_usubu : ReflectiveSubuniverse >-> UnitSubuniverse.

(** Here we prove the definition of reflective subuniverse in the book. *)
Section IsEquiv.
  Context {fs : Funext} {subU : ReflectiveSubuniverse}.
  Context (P Q : Type) {Q_inO : inO Q}.

  Global Instance isequiv_o_O_unit 
  : IsEquiv (fun g : O P -> Q => g o O_unit P).
  Proof.
    refine (BuildIsEquiv _ _ _ O_rectnd _ _ _).
    - intros f.
      apply path_arrow; intros x.
      apply O_rectnd_beta.
    - intros g.
      apply path_arrow; intros x.
      apply O_rectpaths; intros a.
      apply O_rectnd_beta.
    - intros f; simpl.
      apply moveR_equiv_M; simpl.
      apply path_forall; intros x; symmetry.
      refine (apD10_ap_precompose (O_unit P) _ x @ _).
      refine (apD10_path_arrow _ _ _ (O_unit P x) @ _).
      exact (O_rectpaths_beta _ f _ x).
  Defined.

  Definition equiv_o_O_unit : (O P -> Q) <~> (P -> Q)
    := BuildEquiv _ _ (fun g : O P -> Q => g o O_unit P) _.

  Global Instance isequiv_O_rectnd
  : IsEquiv (@O_rectnd subU P Q _)
  := (@isequiv_inverse _ _ _ isequiv_o_O_unit).

  Definition equiv_O_rectnd : (P -> Q) <~> (O P -> Q)
    := BuildEquiv _ _ O_rectnd _.

End IsEquiv.

(** Conversely, from the book's definition we can reconstruct ours. *)
Section ReflectiveSubuniverseFromIsEquiv.

  Context {fs : Funext}.
  Context (subU : UnitSubuniverse).
  Let precomp := fun P Q => (fun g : O P -> Q => g o O_unit P).
  Context (H : forall {P Q : Type} {Q_inO : inO Q}, IsEquiv (precomp P Q)).
  
  Local Definition O_rectnd' {P Q : Type} {Q_inO : inO Q} (f : P -> Q)
  : O P -> Q
  := (precomp P Q)^-1 f.

  Local Definition O_rectnd_beta' {P Q : Type} {Q_inO : inO Q} (f : P -> Q) (x : P)
  : O_rectnd' f (O_unit P x) = f x
  := ap10 (eisretr (precomp P Q) f) x.

  Local Definition O_rectpaths' {P Q : Type} {Q_inO : inO Q}
        (g h : O P -> Q) (p : g o O_unit P == h o O_unit P)
  : g == h.
  Proof.
    apply ap10.
    refine ((eissect (precomp P Q) g)^ @ _ @ eissect (precomp P Q) h).
    apply ap.
    apply path_arrow, p.
  Defined.

  Local Definition O_rectpaths_beta' {P Q : Type} {Q_inO : inO Q}
        (g h : O P -> Q) (p : g o O_unit P == h o O_unit P) (x : P)
  : O_rectpaths' g h p (O_unit P x) = p x.
  Proof.
    unfold O_rectpaths'.
    refine ((ap10_ap_precompose (O_unit P) _ x)^ @ _).
    refine (apD10 _ x).
    apply moveR_equiv_M.
    rewrite ap_pp, ap_pp, ap_V, <- ap_compose, concat_pp_p.
    do 2 rewrite <- eisadj.
    apply moveR_Vp.
    exact (concat_A1p (eisretr (precomp P Q)) (path_arrow _ _ p)).
  Qed.

  Definition reflective_subuniverse_from_isequiv
  : ReflectiveSubuniverse
  := Build_ReflectiveSubuniverse subU
       (@O_rectnd') (@O_rectnd_beta') (@O_rectpaths') (@O_rectpaths_beta').

End ReflectiveSubuniverseFromIsEquiv.

(** So why do we use a different definition than the book?  Notice that *both* directions of the comparison between our definition and the book's make use of funext.  Moreover, it seems that in order to do anything useful with the book's definition, or construct any interesting examples, also requires funext.  However, this is not the case for our definition!  Thus, our choice has the following advantages:

1. It avoids the funext redexes that otherwise infect the theory, thereby simplifying the proofs and proof terms.  We never have to worry about whether we have a path between functions or a homotopy; we use only homotopies, with no need for [ap10] or [path_arrow] to mediate.

2. It avoids [Funext] hypotheses in some constructions of reflective subuniverses, particularly the construction from a [Modality].  This enables us to declare such constructions as coercions without running afoul of Coq's "uniform inheritance condition", so that a modality can be used as a reflective subuniverse.

3. In fact, the data of a reflective subuniverse according to our definition are precisely a couple of special cases of the data of a modality.  Thus, all the theorems we prove about reflective subuniverses will, when interpreted for a modality (coerced as above to a reflective subuniverse), reduce definitionally to "the way we would have proved them directly for a modality".  *)

(** ** Replete Subuniverses *)

(** A subuniverse is replete if it is closed under equivalence.  This is also a more usual sort of typeclass.  We are not very interested in non-replete subuniverses; the reason for not including repleteness in the main definition is so that functoriality, below, can not depend on it, so that in turn [Build_Modality_easy] can use functoriality to prove repleteness. *)

Class Replete (subU : UnitSubuniverse) :=
  inO_equiv_inO : forall T U (T_inO : @inO subU T) (f : T -> U) (feq : IsEquiv f), @inO subU U.

(** Of course, with univalence this is automatic.  This is the only appearance of univalence in the theory of reflective subuniverses and (non-lex) modalities. *)
Global Instance replete_univalence `{Univalence} (subU : UnitSubuniverse)
: Replete subU.
Proof.
  intros T U ? f ?.
  refine (transport (@inO subU) _ _).
  apply path_universe with f; exact _.
Defined.

(** ** Properties of Reflective Subuniverses *)

(** We now prove a bunch of things about an arbitrary reflective subuniverse (sometimes replete). *)
Section Reflective_Subuniverse.
  Context {subU : ReflectiveSubuniverse}.

  (** Functoriality of [O_rectnd] homotopies *)
  Definition O_rectnd_homotopy {P Q} {Q_inO : inO Q} (f g : P -> Q) (pi : f == g)
  : O_rectnd f == O_rectnd g.
  Proof.
    apply O_rectpaths; intro x.
    etransitivity.
    { apply O_rectnd_beta. }
    { etransitivity.
      { exact (pi _). }
      { symmetry; apply O_rectnd_beta. } }
  Defined.

  (** If [T] is in the subuniverse, then [O_unit T] is an equivalence. *)
  Global Instance isequiv_O_unit_inO (T : Type) {T_inO : inO T} : IsEquiv (O_unit T).
  Proof.
    pose (g := O_rectnd idmap).
    refine (isequiv_adjointify (O_unit T) g _ _).
    - refine (O_rectpaths (O_unit T o g) idmap _).
      intros x; unfold compose.
      apply ap.
      apply O_rectnd_beta.
    - intros x.
      apply O_rectnd_beta.
  Defined.

  Definition equiv_O_unit (T : Type) {T_inO : inO T} : T <~> O T
    := BuildEquiv T (O T) (O_unit T) _.

  Section Functor.

    (** In this section, we see that [O] is a functor. *)
    
    Definition O_functor {A B : Type} (f : A -> B) : O A -> O B
      := O_rectnd (O_unit B o f).

    (** Functoriality on composition *)
    Definition O_functor_compose {A B C : Type} (f : A -> B) (g : B -> C)
    : (O_functor (g o f)) == (O_functor g) o (O_functor f).
    Proof.
      apply O_rectpaths; intros x; unfold compose.
      refine (O_rectnd_beta (O_unit C o g o f) x @ _).
      transitivity (O_functor g (O_unit B (f x))).
      - symmetry. exact (O_rectnd_beta (O_unit C o g) (f x)).
      - apply ap; symmetry.
        exact (O_rectnd_beta (O_unit B o f) x).
    Defined.

    (** Functoriality on homotopies *)
    Definition O_functor_homotopy {A B : Type} (f g : A -> B) (pi : f == g)
    : O_functor f == O_functor g.
    Proof.
      refine (O_rectpaths _ _ _); intros x.
      refine (O_rectnd_beta (O_unit B o f) x @ _).
      refine (_ @ (O_rectnd_beta (O_unit B o g) x)^).
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
      refine (O_rectpaths _ _ _); intros x.
      apply O_rectnd_beta.
    Qed.

    (** Naturality of [O_unit] *)
    Definition O_unit_natural {A B} (f : A -> B)
    : (O_functor f) o (O_unit A) == (O_unit B) o f
    := (O_rectnd_beta _).

    (** The pointed endofunctor ([O],[O_unit]) is well-pointed *)
    Definition O_functor_wellpointed (A : Type)
    : O_functor (O_unit A) == O_unit (O A).
    Proof.
      refine (O_rectpaths _ _ _); intros x.
      apply O_unit_natural.
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

    (** Postcomposition respects [O_rectnd] *)
    Definition O_rectnd_postcompose {A B C} {B_inO : inO B} {C_inO : inO C}
               (f : A -> B) (g : B -> C)
    : g o O_rectnd f == O_rectnd (g o f).
    Proof.
      refine (O_rectpaths _ _ _); intros x; unfold compose.
      transitivity (g (f x)).
      - apply ap. apply O_rectnd_beta.
      - symmetry. exact (O_rectnd_beta (g o f) x).
    Defined.

  End Functor.

  Section Replete.

    (** An equivalent formulation of repleteness is that a type lies in the subuniverse as soon as its unit map is an equivalence. *)
    Definition inO_isequiv_O_unit {rep : Replete subU} (T:Type)
    : IsEquiv (O_unit T) -> inO T
    := fun _ => inO_equiv_inO (O T) T _ (O_unit T)^-1 _.

    Definition inO_iff_isequiv_O_unit {rep : Replete subU} (T:Type)
    : inO T <-> IsEquiv (O_unit T).
    Proof.
      split.
      - apply isequiv_O_unit_inO.
      - apply inO_isequiv_O_unit.
    Defined.

    Global Instance replete_inO_isequiv_O_unit
           (H : forall T, IsEquiv (O_unit T) -> inO T)
    : Replete subU.
    Proof.
      intros A B A_inO f feq.
      pose (uA := BuildEquiv _ _ (O_unit A) _).
      refine (H B (isequiv_adjointify (O_unit B) _ _ _)); cbn.
      - exact (f o uA^-1 o (O_functor f)^-1).
      - intros x; unfold compose.
        refine ((O_unit_natural f _)^ @ _).
        transitivity (O_functor f ((O_functor f)^-1 x)).
        + apply (ap (O_functor f)).
          apply eisretr.
        + apply eisretr.
      - intros x; unfold compose.
        transitivity (f (uA^-1 (O_unit A (f^-1 x)))).
        + apply ap, ap, (O_unit_natural f^-1 x).
        + transitivity (f (f^-1 x)).
          * apply ap, eissect.
          * apply eisretr.
    Defined.

    (** Thus, [T] is in a replete subuniverse as soon as [O_unit T] admits a retraction. *)
    Definition inO_unit_retract {rep : Replete subU} (T:Type) (mu : O T -> T)
    : Sect (O_unit T) mu -> inO T.
    Proof.
      unfold Sect; intros H.
      apply inO_isequiv_O_unit.
      apply isequiv_adjointify with (g:=mu).
      - refine (O_rectpaths (O_unit T o mu) idmap _).
        intros x; exact (ap (O_unit T) (H x)).
      - exact H.
    Defined.

  End Replete.

  Section OInverts.

    (** The maps that are inverted by the reflector. *)
    Notation O_inverts f := (IsEquiv (O_functor f)).

    Global Instance O_inverts_O_unit (A : Type)
    : O_inverts (O_unit A).
    Proof.
      refine (isequiv_homotopic (O_unit (O A)) _ _).
      intros x; symmetry; apply O_functor_wellpointed.
    Defined.

    (** A map between modal types that is inverted by [O] is already an equivalence. *)
    Definition isequiv_O_inverts {A B} {A_inO : inO A} {B_inO : inO B}
      (f : A -> B) `{O_inverts f}
    : IsEquiv f.
    Proof.
      assert (IsEquiv (O_unit B o f)).
      { refine (isequiv_homotopic (O_functor f o O_unit A) _ _).
        apply O_unit_natural. }
      refine (cancelL_isequiv (O_unit B)).
    Defined.

    Definition equiv_O_inverts {A B} {A_inO : inO A} {B_inO : inO B}
      (f : A -> B) `{O_inverts f}
    : A <~> B
    := BuildEquiv _ _ f (isequiv_O_inverts f).

    Definition O_unit_inv_natural {A B} {A_inO : inO A} {B_inO : inO B}
               (f : A -> B)
    : (O_unit B)^-1 o (O_functor f) == f o (O_unit A)^-1.
    Proof.
      refine (O_rectpaths _ _ _); intros x.
      unfold compose; apply moveR_equiv_V.
      refine (O_unit_natural f x @ _).
      unfold compose; do 2 apply ap.
      symmetry; apply eissect.
    Defined.

    (** Two maps between modal types that become equal after applying [O_functor] are already equal. *)
    Definition O_functor_faithful_inO {A B} {A_inO : inO A} {B_inO : inO B}
      (f g : A -> B) (e : O_functor f == O_functor g)
      : f == g.
    Proof.
      intros x.
      refine (ap f (eissect (O_unit A) x)^ @ _).
      refine (_ @ ap g (eissect (O_unit A) x)).
      transitivity ((O_unit B)^-1 (O_functor f (O_unit A x))).
      + symmetry; apply O_unit_inv_natural.
      + transitivity ((O_unit B)^-1 (O_functor g (O_unit A x))).
        * apply ap, e.
        * apply O_unit_inv_natural.
    Defined.

    (** Any map to a type in the subuniverse that is inverted by [O] must be equivalent to [O_unit].  More precisely, the type of such maps is contractible. *)
    Definition typeof_O_unit (A : Type)
      := { OA : Type & { Ou : A -> OA & ((inO OA) * (O_inverts Ou)) }}.

    Global Instance contr_typeof_O_unit `{Univalence} (A : Type)
    : Contr (typeof_O_unit A).
    Proof.
      exists (O A ; (O_unit A ; (_ , _))).
      intros [OA [Ou [? ?]]].
      pose (f := O_rectnd Ou : O A -> OA).
      pose (g := (O_functor Ou)^-1 o O_unit OA : (OA -> O A)).
      assert (IsEquiv f).
      { refine (isequiv_adjointify f g _ _).
        - apply O_functor_faithful_inO; intros x.
          rewrite O_functor_idmap.
          fold (f o g); rewrite O_functor_compose.
          unfold g.
          simpl rewrite (O_functor_compose (O_unit OA) (O_functor Ou)^-1).
          rewrite O_functor_wellpointed.
          simpl rewrite (O_unit_natural (O_functor Ou)^-1 x).
          refine (O_unit_natural f _ @ _).
          set (y := (O_functor Ou)^-1 x).
          transitivity (O_functor Ou y); try apply eisretr.
          unfold f, O_functor, compose.
          apply O_rectnd_postcompose.
        - refine (O_rectpaths _ _ _); intros x.
          unfold f, compose.
          rewrite O_rectnd_beta. unfold g.
          apply moveR_equiv_V.
          symmetry; apply O_unit_natural.
      }
      refine (path_sigma _ _ _ _ _); cbn.
      - exact (path_universe f).
      - rewrite transport_sigma.
        refine (path_sigma _ _ _ _ _); cbn; try apply path_ishprop.
        apply path_arrow; intros x.
        rewrite transport_arrow_fromconst.
        rewrite transport_path_universe.
        unfold f; apply O_rectnd_beta.
    Qed.

  End OInverts.

  Section Types.
    Context {rep : Replete subU}.

    (** ** The [Unit] type *)
    Global Instance inO_unit : inO Unit.
    Proof.
      apply inO_unit_retract with (mu := fun x => tt).
      exact (@contr Unit _).
    Defined.
    
    (** ** Dependent product and arrows *)
    (** Theorem 7.7.2 *)
    Global Instance inO_forall {fs : Funext} (A:Type) (B:A -> Type) 
    : (forall x, (inO (B x)))
      -> (inO (forall x:A, (B x))).
    Proof.
      intro H.
      pose (ev := fun x => (fun (f:(forall x, (B x))) => f x)).
      pose (zz := fun x:A => O_rectnd (ev x)).
      apply inO_unit_retract with (mu := fun z => fun x => zz x z).
      intro phi.
      unfold zz, ev; clear zz; clear ev.
      apply path_forall; intro x.
      exact (O_rectnd_beta (fun f : forall x0, (B x0) => f x) phi).
    Defined.

    Global Instance inO_arrow {fs : Funext} (A B : Type) {B_inO : inO B}
    : inO (A -> B).
    Proof.
      apply inO_forall.
      intro a. exact _.
    Defined.

    (** ** Product *)
    Global Instance inO_prod (A B : Type) {A_inO : inO A} {B_inO : inO B}
    : inO (A*B).
    Proof.
      apply inO_unit_retract with
        (mu := fun X => (@O_rectnd _ (A * B) A _ fst X , O_rectnd snd X)).
      intros [a b]; apply path_prod; simpl.
      - exact (O_rectnd_beta fst (a,b)). 
      - exact (O_rectnd_beta snd (a,b)).
    Defined.

    (** We show that [OA*OB] has the same universal property as [O(A*B)] *)

    Definition equiv_O_prod_unit_precompose
               {fs : Funext} (A B C : Type) {C_inO : inO C}
    : ((O A) * (O B) -> C) <~> (A * B -> C).
    Proof.
      apply (equiv_compose' (equiv_uncurry A B C)).
      refine (equiv_compose' _ (equiv_inverse (equiv_uncurry (O A) (O B) C))).
      apply (equiv_compose' (equiv_o_O_unit A (B -> C))); simpl.
      apply equiv_postcompose'.
      exact (equiv_o_O_unit B C).
    Defined.

    (** The preceding equivalence turns out to be actually (judgmentally!) precomposition with the following function. *)
    Definition O_prod_unit (A B : Type) : A * B -> O A * O B
      := functor_prod (O_unit A) (O_unit B).

    (** From this, we can define the comparison map for products, and show that precomposing with it is also an equivalence. *)
    Definition O_prod_cmp (A B : Type) : O (A * B) -> O A * O B
      := O_rectnd (O_prod_unit A B).

    Global Instance isequiv_O_prod_cmp (A B : Type)
    : IsEquiv (O_prod_cmp A B).
    Proof.
      refine (isequiv_adjointify _ _ _ _).
      { apply prod_rect; intro a.
        apply O_rectnd; intro b; revert a.
        apply O_rectnd; intro a.
        apply O_unit.
        exact (a, b). }
      { unfold prod_rect, O_prod_cmp, O_prod_unit.
        intros [oa ob].
        revert ob; refine (O_rectpaths _ _ _); intros b.
        revert oa; refine (O_rectpaths _ _ _); intros a.
        cbn. abstract (repeat rewrite O_rectnd_beta; reflexivity). }
      { unfold prod_rect, O_prod_cmp, O_prod_unit.
        refine (O_rectpaths _ _ _); intros [a b]; cbn.
        abstract (repeat (rewrite O_rectnd_beta; cbn); reflexivity). }
    Defined.

    Definition isequiv_O_prod_cmp_precompose
      {fs : Funext} (A B C : Type) {C_inO : inO C}
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
    : (forall (A:Type) (B:A -> Type) {A_inO : inO A} {B_inO : forall a, inO (B a)},
         (inO ({x:A & B x})))
      <->
      (forall (A:Type) (B: (O A) -> Type) {B_inO : forall a, inO (B a)}
              (g : forall (a:A), (B (O_unit A a))),
         {f : forall (z:O A), (B z) & forall a:A, f (O_unit A a) = g a}).
    Proof.
      split.
      - intro H. intros A B ? g.
        pose (Z := sigT B).
        assert (inO Z). apply H; exact _.
        pose (g' := (fun a:A => (O_unit A a ; g a)) : A -> Z).
        pose (f' := O_rectnd g').
        pose (eqf := (O_rectnd_beta g')  : f' o O_unit A == g').
        pose (eqid := O_rectpaths (pr1 o f') idmap
                                  (fun x => ap pr1 (eqf x))).
        exists (fun z => transport B (eqid z) ((f' z).2)); intros a.
        unfold eqid. rewrite O_rectpaths_beta.
        exact (pr2_path (O_rectnd_beta g' a)).
      - intros H A B ? ?.
        pose (h := fun x => @O_rectnd _ ({x:A & B x}) A _ pr1 x).
        pose (p := (fun z => O_rectnd_beta pr1 z)
                   : h o (O_unit _) == pr1).
        pose (g := fun z => (transport B ((p z)^) z.2)).
        simpl in *.
        specialize (H ({x:A & B x}) (B o h) _ g).
        destruct H as [f q].
        apply inO_unit_retract with (mu := fun w => (h w; f w)).
        intros [x1 x2].
        refine (path_sigma B _ _ _ _); simpl.
        * apply p.
        * rewrite (q (x1;x2)).
          unfold g; simpl. exact (transport_pV B _ _).
    Qed.

    (** ** Paths *)

    Global Instance inO_paths (S : Type) {S_inO : inO S} (x y : S)
    : inO (x=y).
    Proof.
      refine (inO_unit_retract _ _ _); intro u.
      - assert (p : (fun _ : O (x=y) => x) == (fun _=> y)). 
        { refine (O_rectpaths _ _ _); unfold compose; simpl.
          intro v; exact v. }
        exact (p u).
      - hnf.
        rewrite O_rectpaths_beta; reflexivity.
    Qed.
    
  End Types.

  Section Monad.

    Definition O_monad_mult A : O (O A) -> O A
      := O_rectnd idmap.

    Definition O_monad_mult_natural {A B} (f : A -> B)
    : O_functor f o O_monad_mult A == O_monad_mult B o O_functor (O_functor f).
    Proof.
      apply O_rectpaths; intros x; unfold compose, O_monad_mult.
      simpl rewrite (O_unit_natural (O_functor f) x).
      rewrite (O_rectnd_beta idmap x).
      rewrite (O_rectnd_beta idmap (O_functor f x)).
      reflexivity.
    Qed.

    Definition O_monad_unitlaw1 A
    : O_monad_mult A o (O_unit (O A)) == idmap.
    Proof.
      apply O_rectpaths; intros x; unfold compose, O_monad_mult.
      exact (O_rectnd_beta idmap (O_unit A x)).
    Defined.

    Definition O_monad_unitlaw2 A
    : O_monad_mult A o (O_functor (O_unit A)) == idmap.
    Proof.
      apply O_rectpaths; intros x; unfold O_monad_mult, O_functor, compose.
      repeat rewrite O_rectnd_beta.
      reflexivity.
    Qed.

    Definition O_monad_mult_assoc A
    : O_monad_mult A o O_monad_mult (O A) == O_monad_mult A o O_functor (O_monad_mult A).
    Proof.
      apply O_rectpaths; intros x; unfold O_monad_mult, O_functor, compose.
      repeat rewrite O_rectnd_beta.
      reflexivity.
    Qed.

  End Monad.

  Section StrongMonad.
    Context {fs : Funext} {rep : Replete subU}.

    Definition O_monad_strength A B : A * O B -> O (A * B)
      := fun aob => O_rectnd (fun b a => O_unit (A*B) (a,b)) (snd aob) (fst aob).

    Definition O_monad_strength_natural A A' B B' (f : A -> A') (g : B -> B')
    : O_functor (functor_prod f g) o O_monad_strength A B ==
      O_monad_strength A' B' o functor_prod f (O_functor g).
    Proof.
      intros [a ob]. revert a. apply ap10.
      revert ob; apply O_rectpaths.
      intros b; simpl.
      apply path_arrow; intros a.
      unfold O_monad_strength, O_functor, compose; simpl.
      repeat rewrite O_rectnd_beta.
      reflexivity.
    Qed.
      
    (** The diagrams for strength, see http://en.wikipedia.org/wiki/Strong_monad *)
    Definition O_monad_strength_unitlaw1 A
    : O_functor (@snd Unit A) o O_monad_strength Unit A == @snd Unit (O A).
    Proof.
      intros [[] oa]; revert oa.
      apply O_rectpaths; intros x; unfold O_monad_strength, O_functor, compose. simpl. 
      repeat rewrite O_rectnd_beta.
      reflexivity.
    Qed.

    Definition O_monad_strength_unitlaw2 A B
    : O_monad_strength A B o functor_prod idmap (O_unit B) == O_unit (A*B).
    Proof.
      intros [a b].
      unfold O_monad_strength, functor_prod, compose. simpl. 
      repeat rewrite O_rectnd_beta.
      reflexivity.
    Qed.

    Definition O_monad_strength_assoc1 A B C
    : O_functor (equiv_prod_assoc A B C)^-1 o O_monad_strength (A*B) C ==
      O_monad_strength A (B*C) o functor_prod idmap (O_monad_strength B C) o (equiv_prod_assoc A B (O C))^-1.
    Proof.
      intros [[a b] oc].
      revert a; apply ap10. revert b; apply ap10.
      revert oc; apply O_rectpaths.
      intros c; simpl.
      apply path_arrow; intros b. apply path_arrow; intros a.
      unfold O_monad_strength, O_functor, functor_prod, compose. simpl. 
      repeat rewrite O_rectnd_beta.
      reflexivity.
    Qed.

    Definition O_monad_strength_assoc2 A B
    : O_monad_mult (A*B) o O_functor (O_monad_strength A B) o O_monad_strength A (O B) ==
      O_monad_strength A B o functor_prod idmap (O_monad_mult B).
    Proof.
      intros [a oob]. revert a; apply ap10.
      revert oob; apply O_rectpaths. apply O_rectpaths.
      intros b; simpl. apply path_arrow; intros a.
      unfold O_monad_strength, O_functor, O_monad_mult, functor_prod, compose. simpl. 
      repeat (rewrite O_rectnd_beta; simpl).
      reflexivity.
    Qed.
      
  End StrongMonad.
      
End Reflective_Subuniverse.
