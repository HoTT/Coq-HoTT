(* -*- mode: coq; mode: visual-line -*- *)

(** * Accessible subuniverses and modalities *)

Require Import HoTT.Basics HoTT.Types.
Require Import Extensions NullHomotopy.
Require Import ReflectiveSubuniverse Modality.

Local Open Scope nat_scope.
Local Open Scope path_scope.


(** ** Accessible reflective subuniverses *)

(** An accessible reflective subuniverse is one that is the localization at a small family of maps.  Accessibility is necessary for some constructions, and in practice it's a reasonable hypothesis that includes most examples (though a few examples, such as double negation, may only be accessible if we assume propositional resizing).

We now give the basic definitions related to accessibility, using [ooExtendableAlong] as our notion of equivalence as we did with reflective subuniverses.  The actual construction of a reflective subuniverse by localization will be in [Localization]. *)

Record LocalGenerators@{a} :=
  { lgen_indices : Type@{a} ;
    lgen_domain : lgen_indices -> Type@{a} ;
    lgen_codomain : lgen_indices -> Type@{a} ;
    lgenerator : forall i, lgen_domain i -> lgen_codomain i
  }.

Coercion lgenerator : LocalGenerators >-> Funclass.

(** We put this definition in a module so that no one outside of this file will use it accidentally.  It will be redefined in [Localization] to refer to the localization reflective subuniverse, which is judgmentally the same but will also pick up typeclass inference for [In]. *)
Module Import IsLocal_Internal.
  Definition IsLocal f X :=
    (forall (i : lgen_indices f), ooExtendableAlong (f i) (fun _ => X)).
End IsLocal_Internal.

Class IsAccRSU@{a i} (O : Subuniverse@{i}) :=
{
  acc_lgen : LocalGenerators@{a} ;
  inO_iff_islocal : forall (X : Type@{i}),
      (** We call [iff] explicitly to control the number of universe parameters. *)
      iff@{i i i} (In O X) (IsLocal acc_lgen X) ;
}.

Arguments acc_lgen O {_}.
Arguments inO_iff_islocal O {_} X.

  Global Instance O_inverts_generators {O : ReflectiveSubuniverse} `{IsAccRSU O}
             (i : lgen_indices (acc_lgen O))
  : O_inverts O (acc_lgen O i).
  Proof.
    pose (ext_dom := fst (inO_iff_islocal O (O (lgen_domain (acc_lgen O) i))) _).
    pose (ext_cod := fst (inO_iff_islocal O (O (lgen_codomain (acc_lgen O) i))) _).
    simple refine (isequiv_adjointify _ _ _ _).
    - apply O_rec.
      exact ((fst (ext_dom i 1%nat) (to O _)).1).
    - apply O_indpaths; intros x; simpl.
      rewrite O_rec_beta.
      refine ((fst (snd (ext_cod i 2)
                        (fun x => O_functor O (acc_lgen O i)
                                            ((fst (ext_dom i 1%nat) (to O _)).1 x))
                        _) _).1 x); intros a.
      rewrite ((fst (ext_dom i 1%nat) (to O _)).2 a).
      apply to_O_natural.
    - apply O_indpaths; intros x; simpl.
      rewrite (to_O_natural O (acc_lgen O i) x).
      rewrite O_rec_beta.
      apply ((fst (ext_dom i 1%nat) (to O _)).2 x).
  Qed.

(** The construction of the localization reflective subuniverse for any family of maps will be in [Localization]. *)


(** ** Accessible modalities *)

(** A modality is accessible just when its underlying reflective subuniverse is accessible.  However, for modalities we have a simpler characterization in terms of families of generating connected objects rather than families of generating inverted maps.  We call an object [S]-null if it is local with respect to the maps [S i -> Unit]. *)

Record NullGenerators :=
  { ngen_indices : Type@{a} ;
    ngen_type : ngen_indices -> Type@{a}
  }.

Coercion ngen_type : NullGenerators >-> Funclass.

Definition null_to_local_generators : NullGenerators@{a1} -> LocalGenerators@{a2}
  := fun S => Build_LocalGenerators (ngen_indices S) (ngen_type S) (fun _ => Unit) (fun _ _ => tt).

(** As with [IsLocal], the real version of this notation will be defined in [Nullification]. *)
Module Import IsNull_Internal.
  Definition IsNull (S : NullGenerators@{a}) (X : Type@{i})
    := IsLocal@{i i a} (null_to_local_generators@{a a} S) X.
End IsNull_Internal.

(** A central fact: if a type [X] is null for all the fibers of a map [f], then it is [f]-local.  (NB: the converse is *not* generally true.)  TODO: Should this go in [Extensions]? *)
Definition extendable_isnull_fibers (n : nat)
           {A B} (f : A -> B) (C : B -> Type)
: (forall b, ooExtendableAlong (@const (hfiber f b) Unit tt)
                               (fun _ => C b))
  -> ExtendableAlong n f C.
Proof.
  revert C.
  simple_induction n n IHn; intros C null; [exact tt | split].
  - intros g.
    exists (fun b => (fst (null b 1%nat) (fun x => x.2 # g x.1)).1 tt).
    intros a.
    rewrite (path_unit tt (const tt a)).
    exact ((fst (null (f a) 1%nat) _).2 (a ; 1)).
  - intros h k.
    apply IHn; intros b.
    apply ooextendable_homotopy, null.
Defined.

Definition ooextendable_isnull_fibers {A B} (f : A -> B) (C : B -> Type)
: (forall b, ooExtendableAlong (@const (hfiber f b) Unit tt)
                               (fun _ => C b))
  -> ooExtendableAlong f C
:= fun null n => extendable_isnull_fibers n f C null.

(** We define a modality to be accessible if it consists of the null types for some family of generators as above. *)

Class IsAccModality@{a i} (O : Subuniverse@{i}) :=
{
  acc_ngen : NullGenerators@{a} ;
  inO_iff_isnull : forall (X : Type@{i}),
      iff@{i i i} (In O X) (IsNull acc_ngen X) ;
}.

Arguments acc_ngen O {_}.
Arguments inO_iff_isnull O {_} X.

Section AccessibleModalities.
  Context (O : Modality) {acco : IsAccModality O}.

  (** Unsurprisingly, the generators are connected. *)
  Global Instance isconnected_acc_ngen i : IsConnected O (acc_ngen O i).
  Proof.
    apply isconnected_from_elim_to_O.
    pose (H := fst (fst (inO_iff_isnull O (O (acc_ngen O i))) _ i 1%nat)
                   (to O ((acc_ngen O) i))).
    exists (H.1 tt).
    exact (fun x => (H.2 x)^).
  Defined.

  (** If all the generators are inhabited, some things become a bit simpler. *)
  Section InhabitedGenerators.

    Context (inhab : forall i, acc_ngen O i).

    (** For testing modal-ness of types, it suffices for all maps out of a generator to be constant.  Probably one could do without [Funext].  *)
    Definition inO_const_fromgen `{Funext} A
               (c : forall i (f : acc_ngen O i -> A), NullHomotopy f)
    : In O A.
    Proof.
      apply (snd (inO_iff_isnull O A)); intros i.
      apply ((equiv_ooextendable_isequiv _ _)^-1%equiv).
      snrapply isequiv_adjointify.
      - intros f []; exact (c i f).1.
      - intros f; apply path_arrow; intros x.
        simpl; unfold composeD.
        symmetry; exact ((c i f).2 x).
      - intros g; apply path_arrow; intros [].
        pose ((c i (g oD (null_to_local_generators (acc_ngen O)) i)).2).
        simpl in p; unfold composeD in p.
        symmetry; apply p, inhab.
    Defined.

    (** In particular, all hprops are modal. *)
    Definition inO_hprop_inhab_gen `{Funext} (A : Type) `{IsHProp A}
    : In O A.
    Proof.
      apply inO_const_fromgen; intros i f.
      exists (f (inhab i)).
      intros; apply path_ishprop.
    Defined.

  End InhabitedGenerators.

End AccessibleModalities.

(** We will now show that a modality is accessible in this sense if and only if its underlying reflective subuniverse is accessible in the sense previously defined.  We (almost?) never need to actually use this, though; in practice accessible modalities usually seem to be given to us with the appropriate sort of generators. *)

(** One direction of this implication is trivial. *)
Global Instance acc_rsu_modality (O : Modality) `{IsAccModality O}
  : IsAccRSU O
  := Build_IsAccRSU O (null_to_local_generators (acc_ngen O)) (fun X => inO_iff_isnull O X).

(** For the less trivial converse, the idea is as follows.  By [ooextendable_isnull_fibers], we can detect locality with respect to a map by nullity with respect to its fibers.  Therefore, our first thought might be to just consider all the fibers of all the maps that we are localizing at.  However, this doesn't quite work because [ooextendable_isnull_fibers] is not an if-and-only-if, so not every modal type would necessarily be null for that type family.

     We do know, however, that if [f] is an [O]-connected map, then any [O]-modal type is null for its fibers (since they are [O]-connected types).  There is no *a priori* why all the maps we localize at should end up being connected for the modality; they will always be inverted, but not every inverted map is connected (unless the modality is lex).  But if [f : A -> B] is [O]-inverted, then the [O]-connected map [to O A] is (up to equivalence) the composite of [f] with the [O]-connected map [to O B].  Thus, if [X] is null for the fibers of [to O A] and [to O B], it will be [f]-local and hence [O]-modal, while all [O]-modal types will be null for these fibers since they are connected. *)

(** We don't make this an [Instance] since it is rarely used, and would cause loops when combined with the previous one. *)
Definition acc_modality_rsu (O : Modality) `{IsAccRSU O}
  : IsAccModality O.
Proof.
  unshelve econstructor.
  { refine (Build_NullGenerators
              (  { i : lgen_indices@{a} (acc_lgen O)
                   & O (lgen_domain@{a} (acc_lgen O) i) }
               + { i : lgen_indices@{a} (acc_lgen O)
                   & O (lgen_codomain@{a} (acc_lgen O) i) })
              _).
    intros [ [i x] | [i x] ]; exact (hfiber (to O _) x). }
  { assert (cm := @conn_map_to_O O).
    split.
    - intros X_inO [ [i x] | [i x] ];
        exact (ooextendable_const_isconnected_inO O _ _).
    - intros Xnull.
      apply (snd (inO_iff_islocal O X)); intros i.
      refine (cancelL_ooextendable (fun _ => X) (acc_lgen O i)
                                   (to O (lgen_codomain (acc_lgen O) i)) _ _).
      + apply ooextendable_isnull_fibers; intros x.
        exact (Xnull (inr (i;x))).
      + refine (ooextendable_homotopic _
                                       (O_functor O (acc_lgen O i)
                                                  o to O (lgen_domain (acc_lgen O) i)) _ _).
        1:apply to_O_natural.
        apply ooextendable_compose.
        * apply ooextendable_equiv, O_inverts_generators.
        * apply ooextendable_isnull_fibers; intros x.
          exact (Xnull (inl (i;x))). }
Defined.

(** The construction of the nullification modality for any family of types will be in [Nullification]. *)
