(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import UnivalenceImpliesFunext.
Require Import HoTT.Tactics.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

Local Arguments compose / .

(** * CoReflective Subuniverses *)

(** ** CoUnit Subuniverses *)

(** A CoUnitSubuniverse is the common underlying structure of a coreflective subuniverse and a comodality.  We make it a separate structure in order to use the same names for its fields and functions in the two cases. *)
Class CoUnitSubuniverse :=
  {
    inO_internal : Type -> Type ;
    O : Type -> Type ;
    O_inO_internal : forall T, inO_internal (O T) ;
    O_counit : forall T, O T -> T ;
    (** In most examples, [Funext] is necessary to prove that the predicate of being in the subuniverse is an hprop.  To avoid needing to assume [Funext] as a global hypothesis when constructing such examples, and since [Funext] is often not needed for any of the rest of the theory, we add it as a hypothesis to this specific field of the record. *)
    hprop_inO_internal : Funext -> forall T, IsHProp (inO_internal T)
  }.

(** For coreflective subuniverses (and hence also comodalities), it will turn out that [inO T] is equivalent to [IsEquiv (O_counit T)].  We could define the former as the latter, and it would simplify some of the general theory.  However, in many examples there is a "more basic" definition of [inO] which is equivalent, but not definitionally identical, to [IsEquiv (O_counit T)].  Thus, including [inO] as data makes more things turn out to be judgmentally what we would expect. *)

(** We made [CoUnitSubuniverse] into a typeclass, rather than just a record, so that when there is an assumed one around it doesn't need to be given explicitly as an argument to everything.  You should *not* ever declare a global [Instance] of [CoUnitSubuniverse].  The things to do with it are:

  1. Assume an arbitrary one for the purposes of general theory, as we will do here.  In this case it is a variable in the context, so typeclass resolution finds it automatically.

  2. Construct a specific one, such as n-types.  You should not define it as a global instance: use [Definition] or [Local Instance].  That way someone else can import your file and still be able to talk about subuniverses other than yours.  (If they do want to use yours, then they can declare it with [Local Existing Instance].)

  3. Apply general theory to a specific example explicitly.  This requires giving the specific example, defined as above, as an explicit argument to the general functions and theorems.

  4. Specify locally that we will be applying the general theory of subuniverses only to a specific example, by declaring that example as a [Local Instance].  (If the subuniverse in question has already been defined somewhere else, you can declare it as an instance locally with [Local Existing Instance].)  This way the instance won't outlast the containing section, module, or file, but inside that section, module, or file, you won't have to give it as an explicit argument.

  The same considerations will apply to [CoReflectiveSubuniverse] and [CoModality].
 *)

Section CoUnit_Subuniverse.

  Context {subU : CoUnitSubuniverse}.

  (** The property of being in the subuniverse.  This is a more usual sort of typeclass, to be inferred automatically in many cases.  Note, however, that you shouldn't write [`{inO A}], since the generalizing binders will then introduce a *new* [CoUnitSubuniverse] hypothesis rather than using the one you intend; write [{A_inO : inO A}] instead.  *)
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

End CoUnit_Subuniverse.

(** ** CoReflective Subuniverses *)

(** A coreflective subuniverse is a [CoUnitSubuniverse], as above, whose counit has a universal property.  Our definition is somewhat different from that in the book, being instead more similar to the definition of a [CoModality]; below we show that it is in fact equivalent. *)
Class CoReflectiveSubuniverse :=
  {
    csubu_usubu : CoUnitSubuniverse ;
    O_corec : forall {P Q : Type} {P_inO : inO P} (f : P -> Q), P -> O Q ;
    O_corec_beta : forall {P Q : Type} {P_inO : inO P} (f : P -> Q) (x : P),
                      O_counit Q (O_corec f x) = f x ;
    O_coindpaths : forall {P Q : Type} {P_inO : inO P}
                         (g h : P -> O Q) 
                         (p : O_counit Q o g == O_counit Q o h),
                    g == h ;
    O_coindpaths_beta : forall {P Q : Type} {P_inO : inO P}
                         (g h : P -> O Q) 
                         (p : O_counit Q o g == O_counit Q o h)
                         (x : P),
                         ap (O_counit Q) (O_coindpaths g h p x) = p x
  }.

Global Existing Instance csubu_usubu.
Coercion csubu_usubu : CoReflectiveSubuniverse >-> CoUnitSubuniverse.


(** ** Replete Subuniverses *)

(** A subuniverse is replete if it is closed under equivalence.  This is also a more usual sort of typeclass.  We are not very interested in non-replete subuniverses; the reason for not including repleteness in the main definition is so that functoriality, below, can not depend on it, so that in turn [Build_Modality_easy] can use functoriality to prove repleteness. *)

Class Replete (subU : CoUnitSubuniverse) :=
  inO_equiv_inO : forall T U (T_inO : @inO subU T) (f : T -> U) (feq : IsEquiv f), @inO subU U.

(** Of course, with univalence this is automatic.  This is the only appearance of univalence in the theory of reflective subuniverses and (non-lex) modalities. *)
Global Instance replete_univalence `{Univalence} (subU : CoUnitSubuniverse)
: Replete subU.
Proof.
  intros T U ? f ?.
  refine (transport (@inO subU) _ _).
  apply path_universe with f; exact _.
Defined.

(** ** Properties of CoReflective Subuniverses *)

(** We now prove a bunch of things about an arbitrary coreflective subuniverse (sometimes replete). *)
Section CoReflective_Subuniverse.
  Context {subU : CoReflectiveSubuniverse}.

  (** Functoriality of [O_rec] homotopies *)
  Definition O_corec_homotopy {P Q} {P_inO : inO P} (f g : P -> Q) 
             (pi : f == g)
  : O_corec f == O_corec g.
  Proof.
    apply O_coindpaths; intro x.
    etransitivity.
    { apply O_corec_beta. }
    { etransitivity.
      { exact (pi _). }
      { symmetry; apply O_corec_beta. } }
  Defined.

  (** If [T] is in the subuniverse, then [O_counit T] is an equivalence. *)
  Global Instance isequiv_O_counit_inO (T : Type) {T_inO : inO T} : IsEquiv (O_counit T).
  Proof.
    pose (g := O_corec idmap).
    refine (isequiv_adjointify (O_counit T) g _ _).
    - intros x.
      apply O_corec_beta.
    - refine (O_coindpaths (g o (O_counit T)) idmap _).
      intros x; unfold compose.
      exact (O_corec_beta _ _).
  Defined.

  Definition equiv_O_counit (T : Type) {T_inO : inO T} : O T <~> T
    := BuildEquiv (O T) T (O_counit T) _.

  Section Functor.

    (** In this section, we see that [O] is a functor. *)
    
    Definition O_functor {A B : Type} (f : A -> B) : O A -> O B
      := O_corec (f o O_counit A).

    (** Functoriality on composition *)
    Definition O_functor_compose {A B C : Type} (f : A -> B) (g : B -> C)
    : (O_functor (g o f)) == (O_functor g) o (O_functor f).
    Proof.
      apply O_coindpaths; intros x; unfold compose.
      refine (O_corec_beta (g o f o O_counit A) x @ _).
      transitivity (g (O_counit B (O_functor f x))).
      - unfold compose. apply ap; symmetry.
        exact (O_corec_beta (f o O_counit A) x).
      - symmetry. exact (O_corec_beta (g o O_counit B) (O_functor f x)).
    Defined.

    (** Functoriality on homotopies *)
    Definition O_functor_homotopy {A B : Type} (f g : A -> B) (pi : f == g)
    : O_functor f == O_functor g.
    Proof.
      refine (O_coindpaths _ _ _); intros x.
      refine (O_corec_beta (f o O_counit A) x @ _).
      refine (_ @ (O_corec_beta (g o O_counit A) x)^).
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
      refine (O_coindpaths _ _ _); intros x.
      apply O_corec_beta.
    Qed.

    (** Naturality of [O_counit] *)
    Definition O_counit_natural {A B} (f : A -> B)
    : (O_counit B) o (O_functor f) == f o (O_counit A)
    := (O_corec_beta _).

    (** The pointed endofunctor ([O],[O_counit]) is well-pointed *)
    Definition O_functor_wellpointed (A : Type)
    : O_functor (O_counit A) == O_counit (O A).
    Proof.
      refine (O_coindpaths _ _ _); intros x.
      apply O_counit_natural.
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
    Definition O_corec_precompose {A B C} {A_inO : inO A} {B_inO : inO B}
               (f : A -> B) (g : B -> C)
    : O_corec g o f == O_corec (g o f).
    Proof.
      refine (O_coindpaths _ _ _); intros x; unfold compose.
      transitivity (g (f x)).
      - exact (O_corec_beta g (f x)).
      - symmetry. apply (O_corec_beta (g o f) x).
    Defined.

  End Functor.

  Section Replete.

    (** An equivalent formulation of repleteness is that a type lies in the subuniverse as soon as its counit map is an equivalence. *)
    Definition inO_isequiv_O_counit {rep : Replete subU} (T:Type)
    : IsEquiv (O_counit T) -> inO T
    := fun _ => inO_equiv_inO (O T) T _ (O_counit T) _.

    Definition inO_iff_isequiv_O_counit {rep : Replete subU} (T:Type)
    : inO T <-> IsEquiv (O_counit T).
    Proof.
      split.
      - apply isequiv_O_counit_inO.
      - apply inO_isequiv_O_counit.
    Defined.

    Global Instance replete_inO_isequiv_O_counit
           (H : forall T, IsEquiv (O_counit T) -> inO T)
    : Replete subU.
    Proof.
      intros A B A_inO f feq.
      pose (uA := BuildEquiv _ _ (O_counit A) _).
      refine (H B (isequiv_adjointify (O_counit B) _ _ _)); cbn.
      - exact ((O_functor f) o uA^-1 o f^-1).
      - intros x; unfold compose.
        refine ((O_counit_natural f _) @ _).
        transitivity (f (f^-1 x)).
        + apply (ap f).
          apply eisretr.
        + apply eisretr.
      - intros x; unfold compose.
        transitivity (O_functor f (uA^-1 (O_counit A ((O_functor f)^-1 x)))).
        + apply ap, ap. symmetry. apply (O_counit_natural f^-1 x).
        + transitivity ((O_functor f) ((O_functor f)^-1 x)).
          * apply ap, eissect.
          * apply eisretr.
    Defined.

    (** Thus, [T] is in a replete subuniverse as soon as [O_counit T] admits a retraction. *)
    Definition inO_counit_section {rep : Replete subU} (T:Type) (mu : T -> O T)
    : Sect mu (O_counit T) -> inO T.
    Proof.
      unfold Sect; intros H.
      apply inO_isequiv_O_counit.
      apply isequiv_adjointify with (g:=mu).
      - exact H.
      - refine (O_coindpaths (mu o O_counit T) idmap _).
        intros x. apply H.
    Defined.

  End Replete.

(*
  Section OInverts.

    (** The maps that are inverted by the reflector. *)
    Notation O_inverts f := (IsEquiv (O_functor f)).

    Global Instance O_inverts_O_counit (A : Type)
    : O_inverts (O_counit A).
    Proof.
      refine (isequiv_homotopic (O_counit (O A)) _ _).
      intros x; symmetry; apply O_functor_wellpointed.
    Defined.

    (** A map between modal types that is inverted by [O] is already an equivalence. *)
    Definition isequiv_O_inverts {A B} {A_inO : inO A} {B_inO : inO B}
      (f : A -> B) `{O_inverts f}
    : IsEquiv f.
    Proof.
      assert (IsEquiv (f o O_counit A)).
      { refine (isequiv_homotopic (f o O_counit A) _ _).
        apply O_counit_natural. }
      refine (cancelL_isequiv (O_counit B)).
    Defined.

    Definition equiv_O_inverts {A B} {A_inO : inO A} {B_inO : inO B}
      (f : A -> B) `{O_inverts f}
    : A <~> B
    := BuildEquiv _ _ f (isequiv_O_inverts f).

    Definition O_unit_inv_natural {A B} {A_inO : inO A} {B_inO : inO B}
               (f : A -> B)
    : (O_unit B)^-1 o (O_functor f) == f o (O_unit A)^-1.
    Proof.
      refine (O_indpaths _ _ _); intros x.
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
      pose (f := O_rec Ou : O A -> OA).
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
          apply O_rec_postcompose.
        - refine (O_indpaths _ _ _); intros x.
          unfold f, compose.
          rewrite O_rec_beta. unfold g.
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
        unfold f; apply O_rec_beta.
    Qed.

  End OInverts.
*)

(*
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
      pose (zz := fun x:A => O_rec (ev x)).
      apply inO_unit_retract with (mu := fun z => fun x => zz x z).
      intro phi.
      unfold zz, ev; clear zz; clear ev.
      apply path_forall; intro x.
      exact (O_rec_beta (fun f : forall x0, (B x0) => f x) phi).
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
        (mu := fun X => (@O_rec _ (A * B) A _ fst X , O_rec snd X)).
      intros [a b]; apply path_prod; simpl.
      - exact (O_rec_beta fst (a,b)). 
      - exact (O_rec_beta snd (a,b)).
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
      := O_rec (O_prod_unit A B).

    Global Instance isequiv_O_prod_cmp (A B : Type)
    : IsEquiv (O_prod_cmp A B).
    Proof.
      refine (isequiv_adjointify _ _ _ _).
      { apply prod_rec; intro a.
        apply O_rec; intro b; revert a.
        apply O_rec; intro a.
        apply O_unit.
        exact (a, b). }
      { unfold prod_rec, O_prod_cmp, O_prod_unit.
        intros [oa ob].
        revert ob; refine (O_indpaths _ _ _); intros b.
        revert oa; refine (O_indpaths _ _ _); intros a.
        cbn. abstract (repeat rewrite O_rec_beta; reflexivity). }
      { unfold prod_rec, O_prod_cmp, O_prod_unit.
        refine (O_indpaths _ _ _); intros [a b]; cbn.
        abstract (repeat (rewrite O_rec_beta; cbn); reflexivity). }
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
        pose (f' := O_rec g').
        pose (eqf := (O_rec_beta g')  : f' o O_unit A == g').
        pose (eqid := O_indpaths (pr1 o f') idmap
                                  (fun x => ap pr1 (eqf x))).
        exists (fun z => transport B (eqid z) ((f' z).2)); intros a.
        unfold eqid. rewrite O_indpaths_beta.
        exact (pr2_path (O_rec_beta g' a)).
      - intros H A B ? ?.
        pose (h := fun x => @O_rec _ ({x:A & B x}) A _ pr1 x).
        pose (p := (fun z => O_rec_beta pr1 z)
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
        { refine (O_indpaths _ _ _); unfold compose; simpl.
          intro v; exact v. }
        exact (p u).
      - hnf.
        rewrite O_indpaths_beta; reflexivity.
    Qed.
    
  End Types.
*)

  Section CoMonad.

    Definition O_comonad_comult A : O A -> O (O A)
      := O_corec idmap.

    Definition O_comonad_comult_natural {A B} (f : A -> B)
    : (O_functor (O_functor f)) o O_comonad_comult A == O_comonad_comult B o O_functor f.
    Proof.
      apply O_coindpaths; intros x; unfold compose, O_comonad_comult.
      simpl rewrite (O_counit_natural (O_functor f) (O_corec idmap x)).
      rewrite (O_corec_beta idmap (O_functor f x)).
      rewrite (O_corec_beta idmap x).
      reflexivity.
    Qed.

    Definition O_comonad_unitlaw1 A
    : O_counit (O A) o O_comonad_comult A == idmap.
    Proof.
      apply O_coindpaths; intros x; unfold compose, O_comonad_comult.
      apply ap. exact (O_corec_beta idmap x).
    Defined.

    Definition O_comonad_unitlaw2 A
    : (O_functor (O_counit A)) o (O_comonad_comult A) == idmap.
    Proof.
      apply O_coindpaths; intros x; 
        unfold O_comonad_comult, O_functor, compose.
      repeat rewrite O_corec_beta.
      reflexivity.
    Qed.

    Definition O_monad_mult_assoc A
    : O_comonad_comult (O A) o O_comonad_comult A
      ==
      (O_functor (O_comonad_comult A)) o (O_comonad_comult A).
    Proof.
      apply O_coindpaths; intros x; 
        unfold O_comonad_comult, O_functor, compose.
      repeat rewrite O_corec_beta.
      reflexivity.
    Qed.

  End CoMonad.

(*
  Section StrongMonad.
    Context {fs : Funext} {rep : Replete subU}.

    Definition O_monad_strength A B : A * O B -> O (A * B)
      := fun aob => O_rec (fun b a => O_unit (A*B) (a,b)) (snd aob) (fst aob).

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
    : O_monad_strength A B o functor_prod idmap (O_unit B) == O_unit (A*B).
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
*)
      
End CoReflective_Subuniverse.
