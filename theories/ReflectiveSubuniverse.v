(* -*- mode: coq; mode: visual-line -*- *)

Require Import Overture PathGroupoids HProp Equivalences EquivalenceVarieties
        UnivalenceImpliesFunext Functorish.
Require Import types.Empty types.Unit types.Arrow types.Sigma types.Paths
        types.Forall types.Prod types.Universe ObjectClassifier.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** * Reflective Subuniverses *)

Section Unit_Subuniverse.

  (** A UnitSubuniverse is the common underlying structure of a reflective subuniverse and a modality.  It consists of: *)
  Class UnitSubuniverse :=
    {
      (** an endomorphism [O] of [Type], and *)
      O : Type -> Type ;
      (** maps [T -> O T] for all [T]. *)
      O_unit : forall T, T -> O T
    }.

  (** We made [UnitSubuniverse] into a typeclass, rather than just a record, so that when there is an assumed one around it doesn't need to be given explicitly as an argument to everything.  You should *not* ever declare a global [Instance] of [UnitSubuniverse].  The things to do with it are:

  1. Assume an arbitrary one for the purposes of general theory, as we will do here.  In this case it is a variable in the context, so typeclass resolution finds it automatically.

  2. Construct a specific one, such as n-types.  You should not define it as a global instance: use [Definition] or [Local Instance].  That way someone else can import your file and still be able to talk about subuniverses other than yours.  (If they do want to use yours, then they can declare it with [Local Existing Instance].)

  3. Apply general theory to a specific example explicitly.  This requires giving the specific example, defined as above, as an explicit argument to the general functions and theorems.

  4. Specify locally that we will be applying the general theory of subuniverses only to a specific example, by declaring that example as a [Local Instance].  (If the subuniverse in question has already been defined somewhere else, you can declare it as an instance locally with [Local Existing Instance].)  This way the instance won't outlast the containing section, module, or file, but inside that section, module, or file, you won't have to give it as an explicit argument.

  The same considerations will apply to [ReflectiveSubuniverse] and [Modality].
  *)

  Context {subU : UnitSubuniverse}.

  (** The property of being in the subuniverse.  This is a more usual sort of typeclass, to be inferred automatically in many cases.  Note, however, that you shouldn't write [`{inO A}], since the generalizing binders will then introduce a *new* [UnitSubuniverse] hypothesis rather than using the one you intend; write [{A_inO : inO A}] instead.  *)
  Class inO (T : Type) :=
    isequiv_inO : IsEquiv (O_unit T).

  Typeclasses Transparent inO.
  Global Existing Instance isequiv_inO.

  Definition equiv_O_unit (T : Type) {T_inO : inO T} : T <~> O T
    := BuildEquiv T (O T) (O_unit T) T_inO.

  Global Instance hprop_inO `{Funext} (T : Type) : IsHProp (inO T) := _.

  (** Being in the universe transports along equivalences, by univalence *)
  Definition inO_equiv_inO `{Univalence} (T : Type) {U : Type} {T_inO : inO T} (f : T <~> U)
    : inO U
    := transport inO (path_universe f) _.
    
  (** The type of types in the subuniverse *)
  Definition TypeO : Type
    := {T : Type & inO T}.

  Coercion TypeO_pr1 (T : TypeO) := @pr1 Type inO T.

  (** The second component of [TypeO] is unique *)
  Definition path_TypeO `{Funext}
    : forall (T T' : TypeO), T.1 = T'.1 -> T = T'.
  Proof.
    intros [T h] [T' h'] X.
    apply (path_sigma _ _ _ X). cbn.
    apply allpath_hprop.
  Defined.

End Unit_Subuniverse.


Section Reflective_Subuniverse.
  Context {ua : Univalence}.

  (** A reflective subuniverse is a subuniverse with unit, as above,
     for which the unit has a universal property. *)
  Class ReflectiveSubuniverse :=
    {
      (** The underlying [UnitSubuniverse] *)
      rsubu_usubu : UnitSubuniverse ;
      (** [O T] is in the subuniverse for all [T] *)
      O_inO : forall T, inO (O T) ;
      (** an equivalence [((O P)->Q) <~> (P -> Q)] *)
      isequiv_o_O_unit : forall (P Q : Type) (Q_inO : inO Q), 
                  IsEquiv (fun f : O P -> Q => f o O_unit P)
    }.

  Global Existing Instance rsubu_usubu.
  Coercion rsubu_usubu : ReflectiveSubuniverse >-> UnitSubuniverse.
  Global Existing Instance O_inO.
  Global Existing Instance isequiv_o_O_unit.

  Context {subU : ReflectiveSubuniverse}.

  Section ORec.

    Context (P Q : Type) {Q_inO : inO Q}.

    (** The equivalence arising from [isequiv_o_O_unit] *)
    Definition equiv_O_rectnd : (O P -> Q) <~> (P -> Q)
      := BuildEquiv _ _ (fun f => f o (O_unit P)) _.
    
    (** Some shortcuts to manipulate the above equivalence.  Here is a "recursor" for [O]. *)
    Definition O_rectnd : (P -> Q) -> (O P) -> Q
      := equiv_O_rectnd^-1.

    Context (f : P -> Q).

    (** Here is its "computation rule". *)
    Definition O_rectnd_retr : O_rectnd f o O_unit _ = f
      := eisretr equiv_O_rectnd f.

    (** Versions of [O_rectnd_retr] with [compose] unfolded and that are further pre- or post-composed with another function.  This enables [rewrite] to recognize them. *)
    Definition O_rectnd_retr' : (fun x => O_rectnd f (O_unit _ x)) = f
      := O_rectnd_retr.
    Definition O_rectnd_retr'_pre (A : Type) (g : A -> P)
      : (fun x => O_rectnd f (O_unit _ (g x))) = f o g
      := ap (fun k => k o g) O_rectnd_retr.
    Definition O_rectnd_retr'_post (B : Type) (h : Q -> B)
      : (fun x => h (O_rectnd f (O_unit _ x))) = h o f
      := ap (fun k => h o k) O_rectnd_retr.
    Definition O_rectnd_retr'_prepost (A B : Type) (g : A -> P) (h : Q -> B)
      : (fun x => h (O_rectnd f (O_unit _ (g x)))) = h o f o g
      := ap (fun k => h o k o g) O_rectnd_retr.

    (** And here is the "uniqueness rule" for the "recursor" *)
    Definition O_rectnd_sect (f : O P -> Q) : O_rectnd (f o O_unit _) = f
      := eissect equiv_O_rectnd f.

  End ORec.

  (** Here is a tactic that tries all the forms of [O_rectnd_retr]. *)
  Ltac rewrite_O_rectnd_retr :=
    repeat first
      [ unfold compose; rewrite O_rectnd_retr'
        | unfold compose; rewrite O_rectnd_retr'_post
        | unfold compose; rewrite O_rectnd_retr'_pre
        | unfold compose; rewrite O_rectnd_retr'_prepost
      ].

  Section Basic_facts.
    
    (** [T] is in the subuniverse as soon as [O_unit T] admits a retraction. *)
    Definition inO_unit_retract (T:Type) (mu : O T -> T)
    : Sect (O_unit T) mu -> inO T.
    Proof.
      unfold Sect; intros H. apply isequiv_adjointify with (g:=mu).
      - apply ap10.
        apply ((ap (equiv_O_rectnd T (O T)))^-1).
        apply path_arrow; intros x; unfold compose; simpl.
        exact (ap (O_unit T) (H x)).
      - exact H.
    Defined.

    (** Injectivity of composing with the unit. *)
    
    Definition path_arrow_modal {A B : Type} {BinO : inO B} (f g : O A -> B)
      : ((f o O_unit A = g o O_unit A) -> (f = g))
      := @equiv_inj _ _ (equiv_O_rectnd A B) _ _ _.
    
    Definition ap10_path_arrow_modal {A B : Type} {BinO : inO B} (f g : O A -> B)
               (pi : f o O_unit A = g o O_unit A)
    : forall a, ap10 (path_arrow_modal _ _ pi) (O_unit _ a) = ap10 pi a.
    Proof.
      intros a.
      refine ((ap10_ap_precompose (O_unit _) (path_arrow_modal f g pi) a) ^ @ _).
      apply (ap (fun h => ap10 h a)).
      unfold path_arrow_modal, equiv_inj.
      apply eisretr.
    Qed.

  End Basic_facts.

  Section Functor.

    (** In this section, we see that [O] is a functor. *)
    
    Definition O_functor {A B : Type} (f : A -> B) : O A -> O B.
    Proof.
      apply O_rectnd.
      - exact _.
      - intro x; exact (O_unit B (f x)).
    Defined.

    (* What is this for? *)
    (* Definition O_functor_modal_square (A : Type) (B : SubuniverseType subU) (f : A -> B)
    : ((equiv_O_unit _ B) ^-1)  o  (O_functor A B f)  o  (subU.(O_unit) A)
      =  f.
    Proof.
      apply path_arrow; intro x; unfold compose, O_functor; simpl.
      pose ((ap10 ((O_rectnd_retr A (subU.(O) B)) ((O_unit subU B) o f)) x)^).
      exact (transport (fun U => O_rectnd B B (fun x : B => x) U = f x)
                       ((ap10 ((O_rectnd_retr A (subU.(O) B)) ((O_unit subU B) o f)) x)^)
                       (ap10 (O_rectnd_retr B B idmap) (f x))).
    Defined.
     *)

    (** Functoriality on composition *)
    Definition O_functor_compose {A B C : Type} (f : A -> B) (g : B -> C)
    : (O_functor (g o f)) = (O_functor g) o (O_functor f).
    Proof.
      apply path_arrow_modal; unfold O_functor.
      rewrite_O_rectnd_retr.
      reflexivity.
    Qed.

    (** Hence functoriality on commutative squares *)
    Definition O_functor_square {A B C X : Type} (pi1 : X -> A) (pi2 : X -> B)
               (f : A -> C) (g : B -> C) (comm : (f o pi1) = (g o pi2))
    : ( (O_functor f) o (O_functor pi1) )
      = ( (O_functor g) o (O_functor pi2) ).
    Proof.
      transitivity (O_functor (f o pi1)).
      - symmetry; apply O_functor_compose.
      - transitivity (O_functor (g o pi2)).
        * apply ap; exact comm.
        * apply O_functor_compose.
    Defined.

    (** Functoriality on identities *)
    Definition O_functor_idmap (A : Type)
    : @O_functor A A idmap = idmap.
    Proof.
      apply path_arrow_modal; unfold O_functor.
      rewrite_O_rectnd_retr.
      reflexivity.
    Qed.

    (** Which implies preservation of equivalences *)
    Global Instance O_functorish : Functorish O
      := Build_Functorish O _ _.
    Proof.
      exact @O_functor.
      exact O_functor_idmap.
    Defined.

    Global Instance isequiv_O_functor `{Univalence}
      {A B} (f : A -> B) `{IsEquiv _ _ f}
    : IsEquiv (O_functor f)
    := isequiv_fmap O f.

    Definition equiv_O_functor `{Univalence} {A B} (f : A <~> B)
    : O A <~> O B
    := BuildEquiv _ _ (O_functor f) _.

    (** Naturality of [O_unit] *)
    Definition O_unit_natural {A B} (f : A -> B)
    : (O_functor f) o (O_unit A) = (O_unit B) o f
    := (O_rectnd_retr _ _ _).

    (** The pointed endofunctor ([O],[O_unit]) is well-pointed *)
    Definition O_functor_wellpointed (A : Type)
    : O_functor (O_unit A) o O_unit A = O_unit (O A) o O_unit A
    := O_unit_natural (O_unit A).

  End Functor.

  Section OInverts.

    (** The maps that are inverted by the reflector. *)
    Notation O_inverts f := (IsEquiv (O_functor f)).

    Global Instance O_inverts_O_unit (A : Type)
    : O_inverts (O_unit A).
    Proof.
      refine (isequiv_homotopic (O_unit (O A)) _ _).
      apply ap10, path_arrow_modal.
      symmetry; apply O_unit_natural.
    Defined.

    (** A map between modal types that is inverted by [O] is already an equivalence. *)
    Definition isequiv_O_inverts {A B} {A_inO : inO A} {B_inO : inO B}
      (f : A -> B) `{O_inverts f}
    : IsEquiv f.
    Proof.
      assert (IsEquiv (O_unit B o f)).
      { refine (isequiv_homotopic (O_functor f o O_unit A) _ _).
        apply ap10, O_unit_natural. }
      refine (cancelL_isequiv (O_unit B)).
    Defined.

    Definition equiv_O_inverts {A B} {A_inO : inO A} {B_inO : inO B}
      (f : A -> B) `{O_inverts f}
    : A <~> B
    := BuildEquiv _ _ f (isequiv_O_inverts f).

    (** Two maps between modal types that become equal after applying [O_functor] are already equal. *)
    Definition O_functor_faithful_inO `{Funext} {A B} {A_inO : inO A} {B_inO : inO B}
      (f g : A -> B) (e : O_functor f = O_functor g)
      : f = g.
    Proof.
      refine (@equiv_inj _ _ (equiv_postcompose (O_unit B)) _ _ _ _); cbn.
      transitivity (O_functor f o O_unit A); try (symmetry; apply O_unit_natural).
      transitivity (O_functor g o O_unit A); try (apply O_unit_natural).
      exact (ap (fun h => h o O_unit A) e).
    Defined.

    (** Any map to a type in the subuniverse that is inverted by [O] must be equivalent to [O_unit].  More precisely, the type of such maps is contractible. *)
    Definition typeof_O_unit (A : Type)
      := { OA : Type & { Ou : A -> OA & ((inO OA) * (O_inverts Ou)) }}.

    Global Instance contr_typeof_O_unit `{Univalence} (A : Type)
    : Contr (typeof_O_unit A).
    Proof.
      exists (O A ; (O_unit A ; (_ , _))).
      intros [OA [Ou [? ?]]].
      pose (f := O_rectnd A OA Ou : O A -> OA).
      pose (g := (O_functor Ou)^-1 o O_unit OA : (OA -> O A)).
      assert (IsEquiv f).
      { refine (isequiv_adjointify f g _ _); apply ap10.
        - apply O_functor_faithful_inO.
          rewrite O_functor_idmap.
          fold (f o g); rewrite O_functor_compose.
          refine (path_arrow_modal (O_functor f o O_functor g) idmap _).
          unfold g; rewrite O_functor_compose.
          (* Here we need to "rewrite modulo associativity" again... *)
          match goal with |- (?a o (?b o ?c) o ?d = ?e) => change (a o b o (c o d) = e) end.
          rewrite O_functor_wellpointed.
          match goal with |- (?a o ?b o (?c o ?d) = ?e) => change ((a o (b o c)) o d = e) end.
          apply (ap (fun h => h o O_unit OA)).
          rewrite O_unit_natural.
          match goal with |- (?a o (?b o ?c) = ?d) => change ((a o b) o c = d) end.
          rewrite O_unit_natural.
          refine (moveR_equiv_M (f := equiv_precompose (O_functor Ou)^-1)
                                (O_unit OA o f) idmap _); cbn.
          apply path_arrow_modal.
          transitivity (O_unit OA o Ou); try (symmetry; apply O_unit_natural).
          apply (ap (fun h => O_unit OA o h)).
          unfold f. rewrite_O_rectnd_retr; reflexivity.
        - refine (path_arrow_modal (g o f) idmap _).
          unfold f; rewrite_O_rectnd_retr. unfold g.
          refine (moveR_equiv_M
                    (f := equiv_postcompose (O_functor Ou)^-1)
                    (O_unit OA o Ou) (O_unit A) _); cbn.
          symmetry; apply O_unit_natural.
      }
      refine (path_sigma _ _ _ _ _); cbn.
      - exact (path_universe f).
      - rewrite transport_sigma.
        refine (path_sigma _ _ _ _ _); cbn; try apply allpath_hprop.
        apply path_arrow; intros x.
        rewrite transport_arrow_fromconst.
        rewrite transport_path_universe.
        unfold f.
        revert x; apply ap10; rewrite_O_rectnd_retr; reflexivity.
    Qed.

  End OInverts.

  Section Types.

    Context `{fs : Funext}.

    (** ** The [Unit] type *)
    Global Instance inO_unit : inO Unit.
    Proof.
      apply inO_unit_retract with (mu := fun x => tt).
      exact (@contr Unit _).
    Defined.
    
    (** ** Dependent product and arrows *)
    (** Theorem 7.7.2 *)
    Global Instance inO_forall (A:Type) (B:A -> Type) 
    : (forall x, (inO (B x)))
      -> (inO (forall x:A, (B x))).
    Proof.
      intro H.
      pose (ev := fun x => (fun (f:(forall x, (B x))) => f x)).
      pose (zz := fun x:A => O_rectnd _ (B x) (ev x)).
      apply inO_unit_retract with (mu := fun z => fun x => zz x z).
      intro phi.
      unfold zz, ev; clear zz; clear ev.
      apply path_forall; intro x.
      pose (foo := O_rectnd_retr _ (B x) (fun f : forall x0, (B x0) => f x)).
      exact (ap10 foo phi).
    Qed.

    Global Instance inO_arrow (A B : Type) {B_inO : inO B} : inO (A -> B).
    Proof.
      apply inO_forall.
      intro a. exact _.
    Qed.

    (** ** Product *)
    Global Instance inO_prod (A B : Type) {A_inO : inO A} {B_inO : inO B}
    : inO (A*B).
    Proof.
      apply inO_unit_retract with
        (mu := fun X => (O_rectnd (A * B) A fst X , O_rectnd (A * B) B snd X)).
      intros [a b]; apply path_prod; simpl.
      - exact (ap10 (O_rectnd_retr (A * B) A fst) (a,b)). 
      - exact (ap10 (O_rectnd_retr (A * B) B snd) (a,b)). 
    Qed.

    (** We show that [OA*OB] has the same universal property as [O(A*B)] *)

    Definition equiv_O_prod_unit_precompose (A B C : Type) {C_inO : inO C}
    : ((O A) * (O B) -> C) <~> (A * B -> C).
    Proof.
      apply (equiv_compose' (equiv_uncurry A B C)).
      refine (equiv_compose' _ (equiv_inverse (equiv_uncurry (O A) (O B) C))).
      apply (equiv_compose' (equiv_O_rectnd A (B -> C))); simpl.
      apply equiv_postcompose'.
      exact (equiv_O_rectnd B C).
    Defined.

    (** The preceding equivalence turns out to be actually (judgmentally!) precomposition with the following function. *)
    Definition O_prod_unit (A B : Type) : A * B -> O A * O B
      := fun ab => (O_unit A (fst ab) , O_unit B (snd ab)).

    (** From this, we can define the comparison map for products, and show that precomposing with it is also an equivalence. *)
    Definition O_prod_cmp (A B : Type) : O (A * B) -> O A * O B
      := O_rectnd (A * B) (O A * O B) (O_prod_unit A B).

    Definition isequiv_O_prod_cmp_precompose
      (A B C : Type) {C_inO : inO C}
    : IsEquiv (fun h : O A * O B -> C => h o O_prod_cmp A B).
    Proof.
      unfold O_prod_cmp.
      refine (isequiv_homotopic
                ((O_rectnd (A*B) C) o
                 (equiv_O_prod_unit_precompose A B C)) _ _).
      intros h.
      apply path_arrow_modal.
      rewrite_O_rectnd_retr.
      reflexivity.
    Qed.

    (** Thus, by the Yoneda lemma, the functor [O] preserves products. *)
    Global Instance isequiv_O_prod_cmp (A B : Type)
    : IsEquiv (O_prod_cmp A B).
    Proof.
      apply isequiv_isequiv_precompose;
      apply isequiv_O_prod_cmp_precompose;
      exact _.
    Defined.

    Definition equiv_O_prod_cmp (A B : Type)
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
        pose (f' := O_rectnd _ _ g').
        pose (eqf := (O_rectnd_retr _ _ g')  : f' o O_unit A = g').
        pose (eqid := path_arrow_modal (pr1 o f') idmap
                                       (ap (fun k => pr1 o k) eqf)).
        exists (fun z => transport B (ap10 eqid z) ((f' z).2)); intros a.
        unfold eqid. rewrite ap10_path_arrow_modal.
        refine (_ @ pr2_path (ap10 (O_rectnd_retr A Z g') a)).
        apply (ap (fun p => transport B p _)).
        exact (ap10_ap_postcompose pr1 eqf a).
      - intros H A B ? ?.
        pose (h := fun x => O_rectnd ({x:A & B x}) A pr1 x).
        pose (p := (fun z => ap10 (O_rectnd_retr ({x : A & B x}) A pr1) z)
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
      - assert (p : (fun _ : O (x=y) => x) = (fun _=> y)). 
        { apply ((ap (equiv_O_rectnd (x=y) S))^-1).
          apply path_arrow; intro v. exact v. }
        exact (ap10 p u).
      - hnf.
        rewrite <- ap10_ap_precompose.
        rewrite eisretr. 
        rewrite ap10_path_arrow; reflexivity.
    Qed.
    
  End Types.
End Reflective_Subuniverse.
