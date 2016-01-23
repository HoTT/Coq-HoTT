(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import EquivalenceVarieties Fibrations Extensions Pullback NullHomotopy.
Require Import Modality Accessible.
Require Import HoTT.Tactics.

Local Open Scope path_scope.


(** * Lex modalities *)

(** ** Basic theory *)

(** A lex modality is one that preserves finite limits, or equivalently pullbacks.  It turns out that a more basic and useful way to say this is that all path-spaces of connected types are connected.  Note how different this is from the behavior of, say, truncation modalities!

  This is a "large" definition, and we don't know of any small one that's equivalent to it (see <http://mathoverflow.net/questions/185980/a-small-definition-of-sub-%E2%88%9E-1-topoi>.  However, so far we never need to apply it "at multiple universes at once".  Thus, rather than making it a module type, we can make it a typeclass and rely on ordinary universe polymorphism. *)

Module Lex_Modalities_Theory (Os : Modalities).

  Module Export Os_Theory := Modalities_Theory Os.

  Class Lex (O : Modality@{u a})
    := isconnected_paths : forall (A : Type@{i}) (x y : A),
                             IsConnected@{u a i} O A ->
                             IsConnected@{u a i} O (x = y).

  Global Existing Instance isconnected_paths.

  (** The following numbered lemmas are all actually equivalent characterizations of lex-ness. *)

  (** 1. Every map between connected types is a connected map. *)
  Global Instance conn_map_lex {O : Modality} `{Lex O}
         {A : Type@{i}} {B : Type@{j}} {f : A -> B}
         `{IsConnected O A} `{IsConnected O B}
  : IsConnMap O f.
  Proof.
    intros b; refine (isconnected_sigma O).
  Defined.

  (** 2. Connected maps are left- as well as right-cancellable. *)
  Definition cancelL_conn_map (O : Modality) `{Lex O}
             {A B C : Type} (f : A -> B) (g : B -> C)
  : IsConnMap O g -> IsConnMap O (g o f) -> IsConnMap O f.
  Proof.
    intros ? ? b.
    refine (isconnected_equiv O _ (hfiber_hfiber_compose_map f g b) _).
  Defined.

  (** 3. Every map inverted by [O] is [O]-connected. *)
  Definition isconnected_O_inverts (O : Modality) `{Lex O}
             {A B : Type} (f : A -> B) `{O_inverts O f}
  : IsConnMap O f.
  Proof.
    refine (cancelL_conn_map O f (to O B) _ _).
    refine (conn_map_homotopic O _ _ (to_O_natural O f) _).
    (** Typeclass magic! *)
  Defined.

  (** 4. Connected types are closed under pullbacks.  (Closure under fibers is [conn_map_lex] above. *)
  Global Instance isconnected_pullback (O : Modality) `{Lex O}
         {A B C : Type} {f : A -> C} {g : B -> C}
         `{IsConnected O A} `{IsConnected O B} `{IsConnected O C}
  : IsConnected O (Pullback f g).
  Proof.
    apply isconnected_sigma; [ exact _ | intros a ].
    refine (isconnected_equiv O (hfiber g (f a))
                              (equiv_functor_sigma' (equiv_idmap _)
                              (fun b => equiv_path_inverse _ _))
                              _).
  Defined.

  (** 5. The reflector preserves pullbacks.  This justifies the terminology "lex". *)
  Definition O_functor_pullback (O : Modality) `{Lex O}
             {A B C} (f : B -> A) (g : C -> A)
  : IsPullback (O_functor_square O _ _ _ _ (pullback_commsq f g)).
  Proof.
    refine (isequiv_O_inverts O _).
    refine (O_inverts_conn_map O _).
    refine (cancelR_conn_map O (to O (Pullback f g)) _).
    refine (conn_map_homotopic O
             (functor_pullback f g (O_functor O f) (O_functor O g)
                               (to O A) (to O B) (to O C)
                               (to_O_natural O f) (to_O_natural O g))
             _ _ _).
    (** This *seems* like it ought to be the easier goal, but it turns out to involve lots of naturality wrangling.  If we ever want to make real use of this theorem, we might want to separate out this goal into an opaque lemma so we could make the main theorem transparent. *)
    - intros [b [c e]];
        unfold functor_pullback, functor_sigma, pullback_corec;
        simpl.
      refine (path_sigma' _ (to_O_natural O pullback_pr1 (b;(c;e)))^ _).
      rewrite transport_sigma'; simpl.
      refine (path_sigma' _ (to_O_natural O pullback_pr2 (b;(c;e)))^ _).
      rewrite transport_paths_Fl.
      rewrite transport_paths_Fr.
      Open Scope long_path_scope.
      unfold O_functor_square.
      rewrite ap_V, inv_V, O_functor_homotopy_beta, !concat_p_pp.
      unfold pullback_commsq; simpl.
      rewrite to_O_natural_compose, !concat_pp_p.
      do 3 apply whiskerL.
      rewrite ap_V, <- inv_pp.
      rewrite <- (inv_V (O_functor_compose _ _ _ _)), <- inv_pp.
      apply inverse2, to_O_natural_compose.
      Close Scope long_path_scope.
    (** By contrast, this goal, which seems to contain all the mathematical content, is solved fairly easily by [hfiber_functor_pullback] and typeclass magic invoking [isconnected_pullback]. *)
    - intros [ob [oc oe]].
      refine (isconnected_equiv O _
                (hfiber_functor_pullback _ _ _ _ _ _ _ _ _ _)^-1 _).
  Qed.

  (** 6. The reflector preserves fibers.  This is a slightly simpler version of the previous. *)
  Global Instance isequiv_O_functor_hfiber (O : Modality) `{Lex O}
             {A B} (f : A -> B) (b : B)
  : IsEquiv (O_functor_hfiber O f b).
  Proof.
    refine (isequiv_O_inverts O _).
    apply O_inverts_conn_map.
    refine (cancelR_conn_map O (to O _) _).
    unfold O_functor_hfiber.
    refine (conn_map_homotopic O
             (@functor_hfiber _ _ _ _ f (O_functor O f)
                               (to O A) (to O B)
                               (fun x => (to_O_natural O f x)^) b)
             _ _ _).
    - intros [a p].
      rewrite O_rec_beta.
      unfold functor_hfiber, functor_sigma. apply ap.
      apply whiskerR, inv_V.
    - intros [oa p].
      refine (isconnected_equiv O _
               (hfiber_functor_hfiber _ _ _ _)^-1 _).
  Defined.

  Definition equiv_O_functor_hfiber (O : Modality) `{Lex O}
             {A B} (f : A -> B) (b : B)
  : O (hfiber f b) <~> hfiber (O_functor O f) (to O B b)
    := BuildEquiv _ _ (O_functor_hfiber O f b) _.

  (** 7. Lex modalities preserve path-spaces. *)
  Definition O_path_cmp (O : Modality) {A} (x y : A)
  : O (x = y) -> (to O A x = to O A y)
    := O_rec (ap (to O A)).

  Global Instance isequiv_O_path_cmp {O : Modality} `{Lex O} {A} (x y : A)
  : IsEquiv (O_path_cmp O x y).
  Proof.
    refine (isequiv_conn_ino_map O _).
    refine (cancelR_conn_map O (to O (x = y)) _).
    refine (conn_map_homotopic O (ap (to O A)) _ _ _).
    - intros ?; symmetry; by apply O_rec_beta.
    - intros p.
      refine (isconnected_equiv O _ (hfiber_ap p)^-1 _).
  Defined.

  (** We will not prove that any of these lemmas are equivalent characterizations of lex-ness, because they are all fairly obvious and we don't yet know of any use for them; [isconnected_paths] is usually strictly easier to prove than they are. *)

  (** Another useful lemma, which is probably not equivalent to lex-ness: any commutative square with connected maps in one direction and modal ones in the other must necessarily be a pullback. *)
  Definition ispullback_connmap_mapino_commsq (O : Modality) `{Lex O} {A B C D}
             {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
             `{IsConnMap O _ _ f} `{IsConnMap O _ _ g}
             `{MapIn O _ _ h} `{MapIn O _ _ k}
             (p : k o f == g o h)
  : IsPullback p.
  Proof.
    refine (isequiv_conn_ino_map O (pullback_corec p)).
    - refine (cancelL_conn_map O (pullback_corec p) (k^* g) _ _).
    - refine (cancelL_mapinO O _ (equiv_pullback_symm k g) _ _).
      refine (cancelL_mapinO O _ (g^* k) _ _).
  Defined.

  (** Lex modalities preserve [n]-types for all [n].  This is definitely not equivalent to lex-ness, since it is true for the truncation modalities that are not lex.  But it is also not true of all modalities; e.g. the shape modality in a cohesive topos can take 0-types to [oo]-types. *)
  Global Instance istrunc_O_lex `{Funext} {O : Modality} `{Lex O}
         {n} {A} `{IsTrunc n A}
  : IsTrunc n (O A).
  Proof.
    generalize dependent A; simple_induction n n IHn; intros A ?.
    - exact _.               (** Already proven for all modalities. *)
    - refine (O_ind (fun x => forall y, IsTrunc n (x = y)) _); intros x.
      refine (O_ind (fun y => IsTrunc n (to O A x = y)) _); intros y.
      refine (trunc_equiv _ (O_path_cmp O x y)).
  Defined.

End Lex_Modalities_Theory.

(** ** Lex reflective subuniverses *)

(** A reflective subuniverse that preserves fibers is in fact a modality (and hence lex). *)
Module Type Preserves_Fibers (Os : ReflectiveSubuniverses).

  Export Os.
  Module Export Os_Theory := ReflectiveSubuniverses_Theory Os.

  Parameter isequiv_O_functor_hfiber :
     forall (O : ReflectiveSubuniverse) {A B} (f : A -> B) (b : B),
       IsEquiv (O_functor_hfiber O f b).

End Preserves_Fibers.

Module Lex_Reflective_Subuniverses
       (Os : ReflectiveSubuniverses) (Opf : Preserves_Fibers Os)
  <: SigmaClosed Os.

  Import Opf.

  Definition inO_sigma@{u a i j k} (O : ReflectiveSubuniverse@{u a})
             (A:Type@{i}) (B:A -> Type@{j})
             (A_inO : In@{u a i} O A)
             (B_inO : forall a, In@{u a j} O (B a))
  : In@{u a k} O {x:A & B x}.
  Proof.
    pose (g := O_rec@{u a k i k k i} pr1 : O {x : A & B x} -> A).
    transparent assert (p : (forall x, g (to O _ x) = x.1)).
    { intros x; subst g; apply O_rec_beta. }
    apply inO_isequiv_to_O@{u a k k}.
    apply isequiv_fcontr; intros x.
    refine (contr_equiv' _ (hfiber_hfiber_compose_map@{k k i k k k k k k} _ g x)).
    apply fcontr_isequiv.
    unfold hfiber_compose_map.
    transparent assert (h : (Equiv@{k k} (hfiber@{k i} (@pr1 A B) (g x))
                                         (hfiber@{k i} g (g x)))).
    { refine (_ oE equiv_to_O@{u a k k} O _).
      - refine (_ oE BuildEquiv _ _
                  (O_functor_hfiber@{u a k i k k i k k (* <- this k is irrelevant *) k k k k k k}
                                   O (@pr1 A B) (g x)) _).
        unfold hfiber.
        refine (equiv_functor_sigma' 1 _). intros y; cbn.
        refine (_ oE (equiv_moveR_equiv_V _ _)).
        apply equiv_concat_l.
        apply moveL_equiv_V.
        unfold g, O_functor.
        revert y; apply O_indpaths@{u a k i i k k}; intros [a q]; cbn.
        refine (_ @ (O_rec_beta _ _)^).
        apply ap, O_rec_beta.
      - refine (inO_equiv_inO@{u (*dwim1*) a (*dwim2*) j (*dwim3*) k (* <- dwim4 *) k} _
                 (hfiber_fibration@{i j k k} (g x) B)). }
    refine (isequiv_homotopic (h oE equiv_hfiber_homotopic _ _ p (g x)) _).
    intros [[a b] q]; cbn. clear h.
    unfold O_functor_hfiber.
    rewrite O_rec_beta.
    unfold functor_sigma; cbn.
    refine (path_sigma' _ 1 _).
    rewrite O_indpaths_beta; cbn.
    unfold moveL_equiv_V, moveR_equiv_V.
    Open Scope long_path_scope.
    rewrite !ap_pp, !concat_p_pp, !ap_V.
    unfold to_O_natural.
    rewrite concat_pV_p.
    subst p.
    rewrite concat_pp_V.
    rewrite concat_pp_p; apply moveR_Vp.
    rewrite <- !(ap_compose (to O A) (to O A)^-1).
    rapply @concat_A1p.
    Close Scope long_path_scope.
  Qed.

End Lex_Reflective_Subuniverses.

(** ** Accessible lex modalities *)

(** We now restrict to lex modalities that are also accessible. *)
Module Accessible_Lex_Modalities_Theory
       (Os : Modalities)
       (Acc : Accessible_Modalities Os).

  Module Export Acc_Theory := Accessible_Modalities_Theory Os Acc.
  Module Export Lex_Theory := Lex_Modalities_Theory Os.

  (** Unfortunately, another subtlety of modules bites us here.  It appears that each application of a parametrized module to arguments creates a *new* module, and Coq has no algorithm (not even syntactic identity) for considering two such modules "the same".  In particular, the applications [Module Os_Theory := Modalities_Theory Os] that occur in both [Accessible_Modalities_Theory Os Acc] and [Lex_Modalities_Theory Os] create two *different* modules, which appear here as [Acc_Theory.Os_Theory] and [Lex_Theory.Os_Theory].  Thus, for instance, we have two different definitions [Acc_Theory.Os_Theory.O_ind] and [Lex_Theory.Os_Theory.O_ind], etc.

  Fortunately, since these duplicate pairs of definitions each have the same body *and are (usually) transparent*, Coq is willing to consider them identical.  Thus, this doesn't cause a great deal of trouble.  However, there are certain contexts in which this doesn't apply.  For instance, if any definition in [Modalities_Theory] is opaque, then Coq will be unable to notice that its duplicate copies in [Acc_Theory.Os_Theory] and [Lex_Theory.Os_Theory] were identical, potentially causing problems.  But since we generally only make definitions opaque if we aren't going to depend on their actual value anywhere else, this is unlikely to be much of an issue.

  A more serious issue is that there are some declarations that function up to a syntactic equality that is stricter than judgmental conversion.  For instance, [Inductive] and [Record] definitions, like modules, always create a new object not convertible to any previously existing one.  There are no [Inductive] or [Record] definitions in [Modalities_Theory], but there are [Class] declarations, and these function similarly.  In particular, typeclass search is unable to use [Instance]s defined in [Acc_Theory] to instantiate typeclasses from [Modalities_Theory] (such as [IsConnected]) needed by functions in [Lex_Theory], and vice versa.

  Fortunately, all the typeclasses defined in [Modalities_Theory] are *singleton* or *definitional* classes (defined with `:= unique_field` rather than `{ field1 ; field2 ; ... }`), which means that they do not actually introduce a new record wrapper.  Thus, the [Instance]s from [Acc_Theory] can in fact be typechecked to *belong* to the typeclasses needed by [Lex_Theory], and hence can be supplied explicitly.

  We can also do this once and for all by defining [Instance]s translating automatically between the two typeclasses, although unfortunately we probably can't declare such instances in both directions at once for fear of infinite loops.  Fortunately, there is not a lot in [Acc_Theory], so this direction seems likely to be the most useful. *)

  Global Instance isconnected_acc_to_lex {O : Modality} {A : Type}
         {H : Acc_Theory.Os_Theory.IsConnected O A}
            : Lex_Theory.Os_Theory.IsConnected O A
         := H.

  (** Probably the most important thing about an accessible lex modality is that the universe of modal types is again modal.  Here by "the universe" we mean a universe large enough to contain the generating family; this is why we need accessibility. *)
  Global Instance inO_typeO `{Univalence} (O : Modality) `{Lex O}
  : In O (Type_ O).
  Proof.
    apply (snd (inO_iff_isnull O _)); intros i n; simpl in *.
    destruct n; [ exact tt | split ].
    - intros P.
      (** Here is the core of the proof: we must show that any family of modal types indexed by a (generating) connected type is equivalent to a constant family.  We take the constant family to be constant at the reflection of the sum of our given family [P]. *)
      simple refine (fun u => (O (sigT P) ; _) ; _); cbn beta.
      1:exact _.
      intros x; symmetry; apply path_TypeO; simpl.
      refine (path_universe (fun p => to O _ (x ; p))).
      revert x; apply isequiv_from_functor_sigma.
      refine (@isequiv_compose _ _
                (pullback_corec ((fun w:sigT P => 1)
                                 : const tt o to O (sigT P) == const tt o pr1))
                _ _ (fun w => (w.2.1 ; w.1)) _).
      (** And here is the core of why it works: the useful lemma above about detecting pullback squares. *)
      + refine (ispullback_connmap_mapino_commsq O
                 ((fun w:sigT P => 1)
                  : const tt o to O (sigT P) == const tt o pr1)).
        (** All the necessary hypotheses are found by typeclass magic! *)
      + refine (@isequiv_compose _ _
                  (equiv_compose
                    (equiv_prod_symm (O (sigT P)) (acc_gen O i))
                    (equiv_pullback_unit_prod (O (sigT P)) (acc_gen O i)))
                  _ _ (equiv_sigma_prod0 _ _)^-1 _).
    - intros A B.
      (** The case [n>0] is actually quite easy, using univalence and the fact that modal types are closed under [Equiv]. *)
      refine (extendable_postcompose' n _ _ _
                (fun b => (equiv_path_TypeO O (A b) (B b))
                            oE (equiv_path_universe (A b) (B b)))
                _).
      refine (extendable_conn_map_inO O n (@const (acc_gen O i) Unit tt)
                                      (fun b => A b <~> B b)).
      (** Typeclass magic! *)
  Defined.

  (** [inO_typeO] is also an equivalent characterization of lex-ness for a modality.  We will prove this, because it is less obvious, and also more useful. *)
  Definition lex_inO_typeO (O : Modality) `{In O (Type_ O)}
  : Lex O.
  Proof.
    intros A x y ?.
    apply isconnected_from_elim_to_O.
    (** The idea is that if [A] is connected and [Type_ O] is modal, then [fun y => O (x = y) : A -> Type_ O] is constant.  Thus, [to O (x=x) 1] can be transported around to make it contractible everywhere. *)
    pose (e := isconnected_elim O (Type_ O)
                 (fun y' => (O (x = y') ; O_inO _))).
    exists (transport idmap (e.2 x @ (e.2 y)^)..1 (to O (x=x) 1)).
    intros [].
    exact ((transport2 idmap (ap (ap pr1) (concat_pV (e.2 x))) _)^).
  Defined.

End Accessible_Lex_Modalities_Theory.
